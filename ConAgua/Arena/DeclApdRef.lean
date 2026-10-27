import ConAgua.Arena.DeclApdSpec
import ConAgua.Arena.IndPosSpec.MatesW
import ConAgua.Arena.IndStubs
import ConAgua.Arena.SimLib
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# `all_level_params_defined` refines `allLevelParamsDefined` (lane `decls3`)

The shape of `IndSumSpec/McGoStep.lean`'s `mentions_const_go` refinement (`mcGoOK`), with three
differences:

* the memo's values are the words `0`/`1` (`apdVR`, `MemoRV`), so the answers stay `0`/`1`;
* the walk's fuel is a word `f` that the twin shares (`f.toNat`, one unit per level);
* the leaves read levels: `sort` runs `lv_apd` (`apdW_ok`) against `readLevel`; `const` runs
  `alpd_ls` over the `ls_node` slice against `readLevels`. Parameters are compared as handle
  words in L and as names in the twin: `NmsR` with `nameN` (injective under `NStoreWF`).

Twin-side facts L does not check (`ApdEnv`): the store's name store is well formed, the
`sort`/`const` nodes' levels read back (`StoreDen`'s fields), and the parameters' names read back.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The memo relation and frames -/

/-- A stored value word is exactly the answer's `0`/`1`. -/
def apdVR (_ : Mem) (w : Word) (v : Bool) : Prop := w = if v then 1 else 0

/-- The memo relation of the walk (keys `(node, 0)`, as `bvarBC`'s). -/
abbrev apdMR (m : Mem) (mp : Std.HashMap EIdx Bool) : Prop := MemoRV apdSch bmKey apdVR m mp

theorem apdSch_wf : apdSch.WF := ⟨by decide, by decide⟩

theorem apdVR_stable : VStable apdSch apdVR := fun _ _ _ _ _ h => h

/-- The walk writes the memo array `APDM` (151) and `CTL[152..153]` only; both are apart from the
arena (arrays below 64 and `CTL` words below 64) and from `CheckR`'s upper tiers (arrays from 137,
`CTL` words from 130), and array 151 is in the reserved walk-local range 144‥191. -/
abbrev ApdFr (m m' : Mem) : Prop := MemFrame [APDM] [152, 153] m m'

theorem apdFrame_arena {m m' : Mem} {a : AState} (hf : ApdFr m m') (hR : ArenaR m a) : ArenaR m' a :=
  ArenaR.frame (fun b hb => by simp at hb; subst hb; simp [arenaArrs, storeArrs, memoArrs, APDM, WSM, BMEMO, LMEMO, IMEMO, FRMEMO])
    (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> exact not_mem_arenaCtl _ (by decide))
    hf hR

theorem apdFrame_iw {m m' : Mem} (hf : ApdFr m m') : m'.arr64 IW = m.arr64 IW :=
  hf.1 IW (by decide) (by decide)

/-- What the twin side must provide beyond the stage relation. -/
structure ApdEnv (a : AState) : Prop where
  nwf : NStoreWF a.store.lss.ls.ns
  sort : ∀ (h : EIdx) (u : LIdx), a.store.view h = some (.sort u) →
    ∃ l, denoteL a.store.ls u = some l
  constLs : ∀ (h : EIdx) (c : NIdx) (us : LsIdx), a.store.view h = some (.const c us) →
    ∃ ls, denoteLs a.store.lss us = some ls

/-- `StoreDen`'s two level fields, with the name store's well-formedness. -/
theorem ApdEnv.of_den {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {fe : IFEnv}
    (hd : StoreDen dn m a fe)
    (hw : NStoreWF a.store.lss.ls.ns) : ApdEnv a := ⟨hw, hd.sort, hd.constLs⟩

/-! ## The parameter slice -/

theorem nmsR_congr {N : Word → ConLeche.Name → Prop} {m m' : Mem} {A : ArrId}
    (h : m'.arr64 A = m.arr64 A) {o k : Word} {ps : List ConLeche.Name} (hp : NmsR N m A o k ps) :
    NmsR N m' A o k ps := by
  induction hp with
  | nil => exact .nil
  | cons hk hn _ ih => exact .cons hk (by rw [rdW, h]; exact hn) ih

theorem hd_word {a : Array Word} {i : Nat} {x : NIdx} (h : hd? a i = some x) :
    ∃ w, a[i]? = some w ∧ w.toNat < 2 ^ 32 ∧ decI w = x := by
  unfold hd? at h
  cases e : a[i]? with
  | none => simp [e] at h
  | some w =>
    by_cases hw : w.toNat < 2 ^ 32
    · simp [e, hw] at h
      exact ⟨w, rfl, hw, h⟩
    · simp [e, hw] at h

/-- A decoded slice of `IW` handles with names is an `NmsR`. -/
theorem nmsR_of_slice {m : Mem} {ns : NStore} (hsz : (m.arr64 IW).size < 2 ^ 64) :
    ∀ (c : Nat) (o l : Word) (lps : List NIdx) (ks : List ConLeche.Name), l.toNat = c →
      hslice? (iwA m) o.toNat c = some lps → lps.mapM (denoteN ns) = some ks →
      NmsR (nameN ns) m IW o l ks := by
  intro c
  induction c with
  | zero =>
    intro o l lps ks hl hs hm
    have : l = 0 := UInt64.toNat_inj.mp (by simpa using hl)
    subst this
    have h0 : hslice? (iwA m) o.toNat 0 = some ([] : List NIdx) := rfl
    rw [h0] at hs
    cases hs
    simp at hm
    subst hm
    exact .nil
  | succ c ih =>
    intro o l lps ks hl hs hm
    rw [hslice?_succ] at hs
    cases hx : (hd? (iwA m) o.toNat : Option NIdx) with
    | none => rw [hx] at hs; simp at hs
    | some x =>
      rw [hx] at hs
      cases hy : (hslice? (iwA m) (o.toNat + 1) c : Option (List NIdx)) with
      | none => rw [hy] at hs; simp at hs
      | some xs =>
        rw [hy] at hs
        simp at hs
        subst hs
        simp only [List.mapM_cons, Option.bind_eq_bind] at hm
        cases hn : denoteN ns x with
        | none => rw [hn] at hm; simp at hm
        | some nx =>
          rw [hn] at hm
          cases hr : xs.mapM (denoteN ns) with
          | none => rw [hr] at hm; simp at hm
          | some ks' =>
            rw [hr] at hm
            simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at hm
            subst hm
            have hl0 : l ≠ 0 := fun e => by subst e; simp at hl
            obtain ⟨w, hwa, hwlt, hdw⟩ := hd_word hx
            have hsz' : o.toNat < (m.arr64 IW).size := by
              have := (Array.getElem?_eq_some_iff.mp hwa).1
              exact this
            have hlt' : o.toNat + 1 < 2 ^ 64 := by omega
            have ho : (o + 1).toNat = o.toNat + 1 := by
              rw [UInt64.toNat_add]; simp; omega
            have hl1 : (l - 1).toNat = c := by
              rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
              simp; omega
            refine .cons hl0 ?_ (ih (o + 1) (l - 1) xs ks' hl1 (by rw [ho]; exact hy) hr)
            have hrd : rdW (m.arr64 IW) o = w := by
              simp only [rdW]; exact (by rw [show (m.arr64 IW)[o.toNat]? = some w from hwa]; rfl)
            rw [hrd]
            exact ⟨hwlt, by rw [hdw]; exact hn⟩

/-! ## Levels -/

section levels
variable {N : Word → ConLeche.Name → Prop}

theorem alpdLsW_ok (hN : NameRel N) (n : Nat) :
    ∀ (m : Mem) (o l lo ll x : Word) (Ls : List ConLeche.Level) (ks : List ConLeche.Name),
      LvsR N m lo ll Ls → NmsR N m IW o l ks → alpdLsW n m o l lo ll = some x →
      x = if Ls.all (ConLeche.Level.allParamsDefined ks) then 1 else 0 := by
  induction n with
  | zero => intro m o l lo ll x Ls ks _ _ h; simp [alpdLsW] at h
  | succ n ih =>
    intro m o l lo ll x Ls ks hLs hks h
    cases hLs with
    | nil => rw [alpdLsW_nil n m o l lo 0 rfl] at h; simp at h; simp [← h]
    | @cons _ _ L Ls' hne hL hrest =>
      rw [alpdLsW_cons n m o l lo _ hne] at h
      cases e : apdW IW n m (prd m lo) o l with
      | none => rw [e] at h; simp [alpdLsK] at h
      | some y =>
        rw [e] at h
        have hy := apdW_ok hN n m _ o l y L ks hL hks e
        by_cases hy0 : y = 0
        · subst hy0; rw [alpdLsK_zero] at h; simp at h
          have : ConLeche.Level.allParamsDefined ks L = false := by
            revert hy; cases ConLeche.Level.allParamsDefined ks L <;> simp
          simp [this, ← h]
        · rw [alpdLsK_ne n m o l lo _ y hy0] at h
          have : ConLeche.Level.allParamsDefined ks L = true := by
            revert hy; cases ConLeche.Level.allParamsDefined ks L <;> simp_all
          rw [ih _ _ _ _ _ _ _ _ hrest hks h]; simp [this]

end levels

theorem apd_sort_ok {m : Mem} {a : AState} (hA : ArenaR m a) (env : ApdEnv a) (n : Nat)
    (o l x r : Word) (ks : List ConLeche.Name)
    (hps : NmsR (nameN a.store.lss.ls.ns) m IW o l ks) (hx : H x) (L : ConLeche.Level)
    (hL : denoteL a.store.ls (decI x) = some L) (hr : apdW IW n m x o l = some r) :
    r = if L.allParamsDefined ks then 1 else 0 := by
  have hlv : LvR (nameN a.store.lss.ls.ns) m x L := by
    have := denoteL_lvR hA (decI x) L hL
    rwa [decI_word_self x hx] at this
  exact apdW_ok (nameN_rel _ env.nwf) n m x o l r L ks hlv hps hr

theorem apd_const_ok {m : Mem} {a : AState} (hA : ArenaR m a) (env : ApdEnv a) (n : Nat)
    (o l y r : Word) (ks : List ConLeche.Name) (m1 : Mem)
    (hps : NmsR (nameN a.store.lss.ls.ns) m IW o l ks) (hy : H y) (Ls : List ConLeche.Level)
    (hL : denoteLs a.store.lss (decI y) = some Ls)
    (hn : apdC1 n m o l (lsNodeW m y) = some (r, m1)) :
    m1 = m ∧ r = if Ls.all (ConLeche.Level.allParamsDefined ks) then 1 else 0 := by
  unfold denoteLs at hL
  cases hv : a.store.lss.view (decI y) with
  | none => rw [hv] at hL; simp at hL
  | some ids =>
    rw [hv] at hL
    simp only at hL
    obtain ⟨hnode, hbd, hsl⟩ := lsNodeW_store hA hy hv
    rw [hnode, apdC1_go n m o l _ (by simp)] at hn
    simp only [List.headD_cons, List.tail_cons] at hn
    have hlv := lvsR_of_slice hA ids Ls _ _ hsl (by have := hA.lit.1.top41; omega) hL
    cases e : alpdLsW n m o l (tfld m LVLS (tierW y) (idxW y) 0) (tfld m LVLS (tierW y) (idxW y) 1) with
    | none => rw [e] at hn; simp [apdR1] at hn
    | some z =>
      rw [e, apdR1_some] at hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      exact ⟨rfl, alpdLsW_ok (nameN_rel _ env.nwf) n m o l _ _ z Ls ks hlv hps e⟩

/-! ## The twin's readbacks -/

theorem readLevel_run (a : AState) (h : LIdx) (L : ConLeche.Level) (hd : denoteL a.store.ls h = some L) :
    (readLevel h).run a = .ok (L, a) := by
  simp [readLevel, hd, StateT.run_bind, StateT.run_get]; rfl

theorem readLevels_run (a : AState) (h : LsIdx) (Ls : List ConLeche.Level)
    (hd : denoteLs a.store.lss h = some Ls) : (readLevels h).run a = .ok (Ls, a) := by
  simp [readLevels, hd, StateT.run_bind, StateT.run_get]; rfl

theorem readNames_run (a : AState) : ∀ (lps : List NIdx) (ks : List ConLeche.Name),
    lps.mapM (denoteN a.store.lss.ls.ns) = some ks → (readNames lps).run a = .ok (ks, a) := by
  intro lps
  induction lps with
  | nil => intro ks h; simp at h; subst h; rfl
  | cons x xs ih =>
    intro ks h
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases hx : denoteN a.store.lss.ls.ns x with
    | none => rw [hx] at h; simp at h
    | some nx =>
      rw [hx] at h
      cases hr : xs.mapM (denoteN a.store.lss.ls.ns) with
      | none => rw [hr] at h; simp at h
      | some ks' =>
        rw [hr] at h
        simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        have h1 : (readName x).run a = .ok (nx, a) := by
          have : denoteN a.store.ns x = some nx := hx
          simp [readName, StateT.run_bind, StateT.run_get, this]; rfl
        simp only [readNames, StateT.run_bind, h1, except_ok_bind, ih ks' hr]
        rfl

/-! ## The twin's arms -/

/-- The twin's arms of a node view (its inner `match`), named. -/
def apdArm (ks : List ConLeche.Name) (memo : Std.HashMap EIdx Bool) (fuel : Nat) :
    ENodeView → AM (Bool × Std.HashMap EIdx Bool)
  | .bvar _ | .lit _ => pure (true, memo)
  | .sort u => do
    let l ← readLevel u
    pure (l.allParamsDefined ks, memo)
  | .const _ us => do
    let ls ← readLevels us
    pure (ls.all (ConLeche.Level.allParamsDefined ks), memo)
  | .fvar _ t => ConRon.Arena.allLevelParamsDefinedGo ks memo fuel t
  | .app f a => do
    let (b₁, memo) ← ConRon.Arena.allLevelParamsDefinedGo ks memo fuel f
    if b₁ then ConRon.Arena.allLevelParamsDefinedGo ks memo fuel a
    else pure (false, memo)
  | .lam t b => do
    let (b₁, memo) ← ConRon.Arena.allLevelParamsDefinedGo ks memo fuel t
    if !b₁ then pure (false, memo) else ConRon.Arena.allLevelParamsDefinedGo ks memo fuel b
  | .forallE t b => do
    let (b₁, memo) ← ConRon.Arena.allLevelParamsDefinedGo ks memo fuel t
    if !b₁ then pure (false, memo) else ConRon.Arena.allLevelParamsDefinedGo ks memo fuel b
  | .letE t v b => do
    let (b₁, memo) ← ConRon.Arena.allLevelParamsDefinedGo ks memo fuel t
    if !b₁ then pure (false, memo) else do
      let (b₂, memo) ← ConRon.Arena.allLevelParamsDefinedGo ks memo fuel v
      if !b₂ then pure (false, memo)
      else ConRon.Arena.allLevelParamsDefinedGo ks memo fuel b
  | .proj _ _ e => ConRon.Arena.allLevelParamsDefinedGo ks memo fuel e

theorem allLevelParamsDefinedGo_succ' (ks : List ConLeche.Name) (memo : Std.HashMap EIdx Bool)
    (fuel : Nat) (h : EIdx) :
    ConRon.Arena.allLevelParamsDefinedGo ks memo (fuel + 1) h = (
      match memo[h]? with
      | some r => pure (r, memo)
      | none => do
        let v ← view h
        let p ← apdArm ks memo fuel v
        pure (p.1, p.2.insert h p.1) : AM (Bool × Std.HashMap EIdx Bool)) := by
  rw [ConRon.Arena.allLevelParamsDefinedGo.eq_2]
  cases memo[h]? with
  | some r => rfl
  | none =>
    simp only
    congr 1; funext v
    cases v with
    | letE t v' b' =>
      simp only [apdArm, bind_assoc, pure_bind]
      congr 1; funext x
      split
      · simp_all
      · simp only [bind_assoc]
        congr 1; funext y; split <;> simp_all
    | _ => first | rfl | (simp only [apdArm, bind_assoc, pure_bind]; try (congr 1; funext x; split <;> simp_all))

theorem apdTwin_node (ks : List ConLeche.Name) (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx)
    (a : AState) (v : ENodeView) (hv : a.store.view h = some v) (hmiss : memo[h]? = none) :
    (ConRon.Arena.allLevelParamsDefinedGo ks memo (fuel + 1) h).run a =
      ((do let p ← apdArm ks memo fuel v; pure (p.1, p.2.insert h p.1) :
        AM (Bool × Std.HashMap EIdx Bool)).run a) := by
  rw [allLevelParamsDefinedGo_succ']
  simp only [hmiss, StateT.run_bind, view_run h a v hv, except_ok_bind]

/-! ## The refinement, by induction on the exec fuel -/

/-- A nonzero fuel word is the successor of its decrement. -/
theorem apd_fuel_pred (f : Word) (hf : f ≠ 0) : ∃ F, f.toNat = F + 1 ∧ (f - 1).toNat = F := by
  have : f.toNat ≠ 0 := fun h => hf (UInt64.toNat_inj.mp (by simpa using h))
  refine ⟨(f - 1).toNat, ?_, rfl⟩
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
  simp; omega

/-- What the walk's word model says about the twin. -/
def ApdGoOK (a : AState) (n : Nat) : Prop :=
  ∀ (m m' : Mem) (o l f h r : Word) (mp : Std.HashMap EIdx Bool) (ks : List ConLeche.Name),
    ArenaR m a → NmsR (nameN a.store.lss.ls.ns) m IW o l ks → H h → apdMR m mp →
    apdGoW n m o l f h = some (r, m') →
    ∃ b mp', (ConRon.Arena.allLevelParamsDefinedGo ks mp f.toNat (decE h)).run a =
        .ok ((b, mp'), a) ∧ r = (if b then 1 else 0) ∧ apdMR m' mp' ∧ ApdFr m m'

section step
variable {a : AState} (env : ApdEnv a)

/-- The two-child shape (`app`, `lam`, `forallE`): the first child, then the second unless the
first answered `false`. -/
theorem apdBin_ok (n : Nat) (ih : ApdGoOK a n) (m m1 : Mem) (o l f : Word) (F : Nat) (x y r : Word)
    (mp : Std.HashMap EIdx Bool) (ks : List ConLeche.Name) (hF1 : (f - 1).toNat = F) (hx : H x)
    (hy : H y) (hA : ArenaR m a) (hps : NmsR (nameN a.store.lss.ls.ns) m IW o l ks)
    (hM : apdMR m mp) (hn : apdB1 n o l f y (apdGoW n m o l (f - 1) x) = some (r, m1)) :
    ∃ b₁ mp₁ m₀, (ConRon.Arena.allLevelParamsDefinedGo ks mp F (decE x)).run a =
        .ok ((b₁, mp₁), a) ∧ apdMR m₀ mp₁ ∧ ApdFr m m₀ ∧
      ((b₁ = false ∧ r = 0 ∧ m1 = m₀) ∨
        (b₁ = true ∧ ∃ b₂ mp₂, (ConRon.Arena.allLevelParamsDefinedGo ks mp₁ F (decE y)).run a =
          .ok ((b₂, mp₂), a) ∧ r = (if b₂ then 1 else 0) ∧ apdMR m1 mp₂ ∧ ApdFr m₀ m1)) := by
  rcases h1 : apdGoW n m o l (f - 1) x with _ | ⟨r1, m₀⟩ <;> simp only [h1, apdB1, apdB1_some, reduceCtorEq] at hn
  obtain ⟨b₁, mp₁, hr1, hb1, hM1, hf1⟩ := ih m m₀ o l (f - 1) x r1 mp ks hA hps hx hM h1
  rw [hF1] at hr1
  refine ⟨b₁, mp₁, m₀, hr1, hM1, hf1, ?_⟩
  by_cases hz : r1 ≠ 0
  · rw [ite_eq_left hz] at hn
    have hb : b₁ = true := by revert hb1 hz; cases b₁ <;> simp
    subst hb
    obtain ⟨b₂, mp₂, hr2, hb2, hM2, hf2⟩ := ih m₀ m1 o l (f - 1) y r mp₁ ks (apdFrame_arena hf1 hA)
      (nmsR_congr (apdFrame_iw hf1) hps) hy hM1 hn
    rw [hF1] at hr2
    exact Or.inr ⟨rfl, b₂, mp₂, hr2, hb2, hM2, hf2⟩
  · rw [ite_eq_right hz] at hn
    simp only [ne_eq, Decidable.not_not] at hz
    subst hz
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
    have hb : b₁ = false := by revert hb1; cases b₁ <;> simp
    exact Or.inl ⟨hb, rfl, rfl⟩

/-- The three-child shape (`letE`). -/
theorem apdLet_ok (n : Nat) (ih : ApdGoOK a n) (m m1 : Mem) (o l f : Word) (F : Nat)
    (x y w r : Word) (mp : Std.HashMap EIdx Bool) (ks : List ConLeche.Name)
    (hF1 : (f - 1).toNat = F) (hx : H x) (hy : H y) (hw : H w) (hA : ArenaR m a)
    (hps : NmsR (nameN a.store.lss.ls.ns) m IW o l ks) (hM : apdMR m mp)
    (hn : apdL1 n o l f y w (apdGoW n m o l (f - 1) x) = some (r, m1)) :
    ∃ b₁ mp₁ m₀, (ConRon.Arena.allLevelParamsDefinedGo ks mp F (decE x)).run a =
        .ok ((b₁, mp₁), a) ∧ apdMR m₀ mp₁ ∧ ApdFr m m₀ ∧
      ((b₁ = false ∧ r = 0 ∧ m1 = m₀) ∨
        (b₁ = true ∧ ∃ b₂ mp₂ m₂, (ConRon.Arena.allLevelParamsDefinedGo ks mp₁ F (decE y)).run a =
          .ok ((b₂, mp₂), a) ∧ apdMR m₂ mp₂ ∧ ApdFr m₀ m₂ ∧
          ((b₂ = false ∧ r = 0 ∧ m1 = m₂) ∨
            (b₂ = true ∧ ∃ b₃ mp₃, (ConRon.Arena.allLevelParamsDefinedGo ks mp₂ F (decE w)).run a =
              .ok ((b₃, mp₃), a) ∧ r = (if b₃ then 1 else 0) ∧ apdMR m1 mp₃ ∧ ApdFr m₂ m1)))) := by
  rcases h1 : apdGoW n m o l (f - 1) x with _ | ⟨r1, m₀⟩ <;> simp only [h1, apdL1, apdL1_some, reduceCtorEq] at hn
  obtain ⟨b₁, mp₁, hr1, hb1, hM1, hf1⟩ := ih m m₀ o l (f - 1) x r1 mp ks hA hps hx hM h1
  rw [hF1] at hr1
  refine ⟨b₁, mp₁, m₀, hr1, hM1, hf1, ?_⟩
  by_cases hz : r1 ≠ 0
  · rw [ite_eq_left hz] at hn
    have hb : b₁ = true := by revert hb1 hz; cases b₁ <;> simp
    subst hb
    rcases h2 : apdGoW n m₀ o l (f - 1) y with _ | ⟨r2, m₂⟩ <;> simp only [h2, apdL2, apdL2_some, reduceCtorEq] at hn
    obtain ⟨b₂, mp₂, hr2, hb2, hM2, hf2⟩ := ih m₀ m₂ o l (f - 1) y r2 mp₁ ks
      (apdFrame_arena hf1 hA) (nmsR_congr (apdFrame_iw hf1) hps) hy hM1 h2
    rw [hF1] at hr2
    refine Or.inr ⟨rfl, b₂, mp₂, m₂, hr2, hM2, hf2, ?_⟩
    by_cases hz2 : r2 ≠ 0
    · rw [ite_eq_left hz2] at hn
      have hb : b₂ = true := by revert hb2 hz2; cases b₂ <;> simp
      subst hb
      have hf12 := hf1.trans hf2
      obtain ⟨b₃, mp₃, hr3, hb3, hM3, hf3⟩ := ih m₂ m1 o l (f - 1) w r mp₂ ks
        (apdFrame_arena hf12 hA) (nmsR_congr (apdFrame_iw hf12) hps) hw hM2 hn
      rw [hF1] at hr3
      exact Or.inr ⟨rfl, b₃, mp₃, hr3, hb3, hM3, hf3⟩
    · rw [ite_eq_right hz2] at hn
      simp only [ne_eq, Decidable.not_not] at hz2
      subst hz2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      have hb : b₂ = false := by revert hb2; cases b₂ <;> simp
      exact Or.inl ⟨hb, rfl, rfl⟩
  · rw [ite_eq_right hz] at hn
    simp only [ne_eq, Decidable.not_not] at hz
    subst hz
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
    have hb : b₁ = false := by revert hb1; cases b₁ <;> simp
    exact Or.inl ⟨hb, rfl, rfl⟩

/-- The tail of every node: the final `put` records the answer. -/
theorem apdFinish {m1 m2 : Mem} (h : Word) (hh : H h) (ks : List ConLeche.Name)
    (mp mp1 : Std.HashMap EIdx Bool) (F : Nat) (v : ENodeView) (b : Bool) (r : Word)
    (hv : a.store.view (decE h) = some v) (hmiss : mp[decE h]? = none)
    (harm : (apdArm ks mp F v).run a = .ok ((b, mp1), a)) (hr : r = if b then 1 else 0)
    (hM1 : apdMR m1 mp1) (hset : msetG apdSch m1 h 0 r = some m2) :
    (ConRon.Arena.allLevelParamsDefinedGo ks mp (F + 1) (decE h)).run a =
        .ok ((b, mp1.insert (decE h) b), a) ∧ apdMR m2 (mp1.insert (decE h) b) ∧ ApdFr m1 m2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [apdTwin_node ks mp F (decE h) a v hv hmiss]
    simp only [StateT.run_bind, harm, except_ok_bind]
    rfl
  · exact memoRV_set apdSch apdSch_wf bmKey apdVR apdVR_stable m1 mp1 hM1 h 0 r ⟨hh, rfl⟩ b hr m2 hset
  · exact (msetG_frame apdSch apdSch_wf m1 m2 h 0 r hset).mono (by simp) (by simp)

include env in
/-- **The node arms**: the model's arms against the twin's. -/
theorem apdNode_ok (n : Nat) (ih : ApdGoOK a n) (m m1 : Mem) (o l f : Word) (F : Nat) (h : Word)
    (vl : List Word) (v : ENodeView) (r : Word) (mp : Std.HashMap EIdx Bool)
    (ks : List ConLeche.Name) (hF1 : (f - 1).toNat = F) (hvr : ViewR vl v)
    (hv : a.store.view (decE h) = some v) (hA : ArenaR m a)
    (hps : NmsR (nameN a.store.lss.ls.ns) m IW o l ks) (hM : apdMR m mp)
    (hn : apdNodeW n m o l f (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0) = some (r, m1)) :
    ∃ b mp1, (apdArm ks mp F v).run a = .ok ((b, mp1), a) ∧ r = (if b then 1 else 0) ∧
      apdMR m1 mp1 ∧ ApdFr m m1 := by
  cases v with
  | bvar i =>
    simp only [ViewR] at hvr
    obtain ⟨hg, -⟩ := hvr
    rw [apdNodeW_leaf n m o l f _ _ _ _ (by rw [hg]; decide) (by rw [hg]; decide)
      (by rw [hg]; decide) (by rw [hg]; decide) (by rw [hg]; decide) (by rw [hg]; decide)] at hn
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
    exact ⟨true, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
  | lit i =>
    simp only [ViewR] at hvr
    rw [apdNodeW_leaf n m o l f _ _ _ _ (by rw [hvr]; decide) (by rw [hvr]; decide)
      (by rw [hvr]; decide) (by rw [hvr]; decide) (by rw [hvr]; decide) (by rw [hvr]; decide)] at hn
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
    exact ⟨true, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
  | sort u =>
    simp only [ViewR, getD1_eq'] at hvr
    obtain ⟨hg, hx, hdx⟩ := hvr
    rw [apdNodeW_sort n m o l f _ _ _ _ hg] at hn
    cases e : apdW IW n m (vl.tail.headD 0) o l with
    | none => rw [e] at hn; simp [apdR1] at hn
    | some y =>
      rw [e, apdR1_some] at hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      obtain ⟨L, hL⟩ := env.sort (decE h) u hv
      have hy := apd_sort_ok hA env n o l _ y ks hps hx L (by rw [hdx]; exact hL) e
      refine ⟨L.allParamsDefined ks, mp, ?_, hy, hM, MemFrame.refl _ _ _⟩
      simp only [apdArm, StateT.run_bind, readLevel_run a u L hL, except_ok_bind]
      rfl
  | const nn us =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, -, -, hy, hdy⟩ := hvr
    rw [apdNodeW_const n m o l f _ _ _ _ hg] at hn
    obtain ⟨Ls, hL⟩ := env.constLs (decE h) nn us hv
    have hL' : denoteLs a.store.lss (decI (vl.tail.tail.headD 0)) = some Ls := by rw [hdy]; exact hL
    obtain ⟨rfl, hz⟩ := apd_const_ok hA env n o l _ r ks m1 hps hy Ls hL' hn
    refine ⟨Ls.all (ConLeche.Level.allParamsDefined ks), mp, ?_, hz, hM, MemFrame.refl _ _ _⟩
    simp only [apdArm, StateT.run_bind, readLevels_run a us Ls hL, except_ok_bind]
    rfl
  | fvar i ty =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, -, hy, hdy⟩ := hvr
    subst hdy
    rw [apdNodeW_fvar n m o l f _ _ _ _ hg] at hn
    obtain ⟨b, mp', hr, hb, hM', hf⟩ := ih m m1 o l (f - 1) _ r mp ks hA hps hy hM hn
    rw [hF1] at hr
    exact ⟨b, mp', hr, hb, hM', hf⟩
  | proj s i e =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, -, -, -, hw, hdw⟩ := hvr
    subst hdw
    rw [apdNodeW_proj n m o l f _ _ _ _ hg] at hn
    obtain ⟨b, mp', hr, hb, hM', hf⟩ := ih m m1 o l (f - 1) _ r mp ks hA hps hw hM hn
    rw [hF1] at hr
    exact ⟨b, mp', hr, hb, hM', hf⟩
  | app f' x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    subst hdx hdy
    rw [apdNodeW_bin n m o l f _ _ _ _ (Or.inl hg)] at hn
    obtain ⟨b₁, mp₁, m₀, h1, hM₀, hf₀, hc⟩ := apdBin_ok n ih m m1 o l f F _ _ r mp ks hF1 hx hy hA hps hM hn
    rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, b₂, mp₂, h2, hr, hM2, hf2⟩
    · refine ⟨false, mp₁, ?_, rfl, hM₀, hf₀⟩
      simp only [apdArm, StateT.run_bind, h1, except_ok_bind, Bool.false_eq_true, ↓reduceIte]; rfl
    · refine ⟨b₂, mp₂, ?_, hr, hM2, hf₀.trans hf2⟩
      simp only [apdArm, StateT.run_bind, h1, h2, except_ok_bind, ↓reduceIte]
  | lam t b' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    subst hdx hdy
    rw [apdNodeW_bin n m o l f _ _ _ _ (Or.inr (Or.inl hg))] at hn
    obtain ⟨b₁, mp₁, m₀, h1, hM₀, hf₀, hc⟩ := apdBin_ok n ih m m1 o l f F _ _ r mp ks hF1 hx hy hA hps hM hn
    rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, b₂, mp₂, h2, hr, hM2, hf2⟩
    · refine ⟨false, mp₁, ?_, rfl, hM₀, hf₀⟩
      simp only [apdArm, StateT.run_bind, h1, except_ok_bind, Bool.not_false, ↓reduceIte]; rfl
    · refine ⟨b₂, mp₂, ?_, hr, hM2, hf₀.trans hf2⟩
      simp only [apdArm, StateT.run_bind, h1, h2, except_ok_bind, Bool.false_eq_true, Bool.not_true, ↓reduceIte]
  | forallE t b' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    subst hdx hdy
    rw [apdNodeW_bin n m o l f _ _ _ _ (Or.inr (Or.inr hg))] at hn
    obtain ⟨b₁, mp₁, m₀, h1, hM₀, hf₀, hc⟩ := apdBin_ok n ih m m1 o l f F _ _ r mp ks hF1 hx hy hA hps hM hn
    rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, b₂, mp₂, h2, hr, hM2, hf2⟩
    · refine ⟨false, mp₁, ?_, rfl, hM₀, hf₀⟩
      simp only [apdArm, StateT.run_bind, h1, except_ok_bind, Bool.not_false, ↓reduceIte]; rfl
    · refine ⟨b₂, mp₂, ?_, hr, hM2, hf₀.trans hf2⟩
      simp only [apdArm, StateT.run_bind, h1, h2, except_ok_bind, Bool.false_eq_true, Bool.not_true, ↓reduceIte]
  | letE t v' b' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy, hw, hdw⟩ := hvr
    subst hdx hdy hdw
    rw [apdNodeW_let n m o l f _ _ _ _ hg] at hn
    obtain ⟨b₁, mp₁, m₀, h1, hM₀, hf₀, hc⟩ :=
      apdLet_ok n ih m m1 o l f F _ _ _ r mp ks hF1 hx hy hw hA hps hM hn
    rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, b₂, mp₂, m₂, h2, hM2, hf2, hc2⟩
    · refine ⟨false, mp₁, ?_, rfl, hM₀, hf₀⟩
      simp only [apdArm, StateT.run_bind, h1, except_ok_bind, Bool.not_false, ↓reduceIte]; rfl
    · rcases hc2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, b₃, mp₃, h3, hr, hM3, hf3⟩
      · refine ⟨false, mp₂, ?_, rfl, hM2, hf₀.trans hf2⟩
        simp only [apdArm, StateT.run_bind, h1, h2, except_ok_bind, Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓reduceIte]; rfl
      · refine ⟨b₃, mp₃, ?_, hr, hM3, (hf₀.trans hf2).trans hf3⟩
        simp only [apdArm, StateT.run_bind, h1, h2, h3, except_ok_bind, Bool.false_eq_true, Bool.not_true, ↓reduceIte]

end step

section step2
variable {a : AState} (env : ApdEnv a)

include env in
theorem apdGo_step_ok (n : Nat) (ih : ApdGoOK a n) : ApdGoOK a (n + 1) := by
  intro m m' o l f h r mp ks hA hps hh hM hb
  rw [apdGoW_succ] at hb
  have hf : ¬ f = 0 := fun hf => by rw [apdG1_abort n m o l f h hf] at hb; simp at hb
  rw [apdG1_go n m o l f h hf] at hb
  obtain ⟨F, hF, hF1⟩ := apd_fuel_pred f hf
  rw [hF]
  have hfr : ¬ mfindG apdSch m h 0 = [] := fun hfr => by rw [apdG2_abort n m o l f h _ hfr] at hb; simp at hb
  by_cases hhit : (mfindG apdSch m h 0).headD 0 ≠ 0
  · rw [apdG2_hit n m o l f h _ hfr hhit] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    obtain ⟨b, hb1, hb2⟩ := memoRV_hit apdSch bmKey apdVR m mp hM h 0 hfr hhit ⟨hh, rfl⟩
    have hk : bmKey.dk h 0 = decE h := rfl
    rw [hk] at hb1
    refine ⟨b, mp, ?_, hb2, hM, MemFrame.refl _ _ _⟩
    rw [allLevelParamsDefinedGo_succ', hb1]
    rfl
  · have hhit0 : (mfindG apdSch m h 0).headD 0 = 0 := by simpa using hhit
    rw [apdG2_miss n m o l f h _ hfr hhit] at hb
    have hmiss := memoRV_miss apdSch bmKey apdVR m mp hM h 0 ⟨hh, rfl⟩ hfr hhit0
    have hk : bmKey.dk h 0 = decE h := rfl
    rw [hk] at hmiss
    have hne : eViewW m h ≠ [] := fun e => by rw [apdG3_abort n m o l f h _ e] at hb; simp at hb
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hA h hne
    generalize eViewW m h = vl at hb hvr hne
    rw [apdG3_go n m o l f h vl hne] at hb
    cases hnode : apdNodeW n m o l f (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
        (vl.tail.tail.tail.headD 0) with
    | none => rw [hnode] at hb; simp [apdG4] at hb
    | some pn =>
      obtain ⟨rn, m1⟩ := pn
      rw [hnode, apdG4_some] at hb
      cases hset : msetG apdSch m1 h 0 rn with
      | none => rw [hset] at hb; simp [apdG5] at hb
      | some m2 =>
        rw [hset, apdG5_some] at hb
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
        obtain ⟨b, mp1, harm, hr, hM1, hfr1⟩ :=
          apdNode_ok env n ih m m1 o l f F h vl v rn mp ks hF1 hvr hv hA hps hM hnode
        obtain ⟨hrun, hM2, hfs⟩ := apdFinish (a := a) h hh ks mp mp1 F v b rn hv hmiss harm hr hM1 hset
        exact ⟨b, mp1.insert (decE h) b, hrun, hr, hM2, hfr1.trans hfs⟩

include env in
theorem apdGoOK (n : Nat) : ApdGoOK a n := by
  induction n with
  | zero => intro m m' o l f h r mp ks _ _ _ _ hb; simp [apdGoW] at hb
  | succ n ih => exact apdGo_step_ok env n ih

end step2

/-! ## The entry -/

theorem apdEntry_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} (n : Nat) (hS : StageR dn vis fe m a) (env : ApdEnv a) (o l e r : Word)
    (lps : List NIdx) (ks : List ConLeche.Name) (hks : lps.mapM (denoteN a.store.lss.ls.ns) = some ks)
    (hdec : decHL m o.toNat l.toNat = some lps) (he : H e)
    (hM : rdW (m.arr64 CTL) apdSch.cs + 2 ≠ 0 → apdMR (mclearG apdSch m) ∅)
    (hb : apdEntryW n m o l e = some (r, m')) :
    ∃ b, (ConRon.Arena.allLevelParamsDefined lps (decE e)).run a = .ok (b, a) ∧
      r = (if b then 1 else 0) ∧ StageR dn vis fe m' a ∧ IWGrow m m' ∧ ∃ mp, apdMR m' mp := by
  unfold apdEntryW at hb
  obtain ⟨h0, hb⟩ := of_ite_none hb
  have hf0 : MemFrame [] [apdSch.cs, apdSch.cs + 1] m (mclearG apdSch m) := mclearG_frame apdSch m
  have hM0 := hM h0
  have hA0 : ArenaR (mclearG apdSch m) a :=
    ArenaR.frame (A := []) (C := [apdSch.cs, apdSch.cs + 1]) (fun b hb => by simp at hb)
      (fun x hx => by
        simp at hx; rcases hx with rfl | rfl <;> exact not_mem_arenaCtl _ (by decide)) hf0
      hS.1.arena.1
  have hsz := hS.2.2.2.1
  have hps0 : NmsR (nameN a.store.lss.ls.ns) m IW o l ks :=
    nmsR_of_slice hsz _ o l lps ks rfl hdec hks
  have hps : NmsR (nameN a.store.lss.ls.ns) (mclearG apdSch m) IW o l ks :=
    nmsR_congr (hf0.1 IW (by simp) (by decide)) hps0
  obtain ⟨b, mp1, hrun, hr, hM1, hfr1⟩ := apdGoOK env n _ _ o l _ e r _ ks hA0 hps he hM0 hb
  have hfall : MemFrame [APDM] [apdSch.cs, apdSch.cs + 1] m m' :=
    (hf0.mono (by simp) (by simp)).trans (hfr1.mono (by simp) (by simp))
  obtain ⟨hS', hg⟩ := StageR.frame_hi hS hfall (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide) (by decide)
    (by simp)
  refine ⟨b, ?_, hr, hS', hg, _, hM1⟩
  have hrn := readNames_run a lps ks hks
  simp only [ConRon.Arena.allLevelParamsDefined]
  have hcw : (UInt64.toNat 4000000000) = coreWalkFuel := CWF_eq
  rw [hcw] at hrun
  generalize coreWalkFuel = F at hrun ⊢
  rw [StateT.run_bind, hrn, except_ok_bind, StateT.run_bind, hrun, except_ok_bind]
  rfl

/-- What the refinement needs of a program: the walk's functions and its callees. -/
structure ApdProg (p : Prog) : Prop where
  eview : p.lookup "e_view" = some eView
  lsnode : p.lookup "ls_node" = some lsNode
  find : p.lookup "apd_find" = some (memoFindG apdSch)
  put : p.lookup "apd_put" = some (memoPutG apdSch)
  clear : p.lookup "apd_clear" = some (memoClearG apdSch)
  lmem : p.lookup "lv_mem" = some (lvMemG IW)
  lnode : p.lookup "lv_node" = some lvNode
  lapd : p.lookup "lv_apd" = some lvApd
  ls : p.lookup "alpd_ls" = some alpdLs
  go : p.lookup "alpd_go" = some alpdGo
  entry : p.lookup "all_level_params_defined" = some allLevelParamsDefinedL

/-- **`alpd_go` refines `allLevelParamsDefinedGo`**, from a related memo and the parameter slice,
at the twin fuel `f.toNat` exactly (the L walk's fuel word is the twin's; the exec fuel only
bounds the depth). -/
@[refines ConRon.Arena.allLevelParamsDefinedGo]
theorem alpdGo_refines (p : Prog) (hp : ApdProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (o l f h : Word)
    (mp : Std.HashMap EIdx Bool) (ks : List ConLeche.Name) (hh : H h)
    (hS : StageR dn vis fe s₀.mem a₀) (env : ApdEnv a₀)
    (hps : NmsR (nameN a₀.store.lss.ls.ns) s₀.mem IW o l ks) (hM : apdMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "alpd_go" [o, l, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.allLevelParamsDefinedGo ks mp f.toNat (decE h)) a₀ ∧
      AM.st (ConRon.Arena.allLevelParamsDefinedGo ks mp f.toNat (decE h)) a₀ = a₀ ∧
      r.headD 0 = (if (AM.res (ConRon.Arena.allLevelParamsDefinedGo ks mp f.toNat (decE h)) a₀).1
        then 1 else 0) ∧
      apdMR s'.mem (AM.res (ConRon.Arena.allLevelParamsDefinedGo ks mp f.toNat (decE h)) a₀).2 ∧
      StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (apdGo_spec p hp.eview hp.lsnode hp.find hp.put hp.lmem hp.lnode hp.lapd hp.ls
    hp.go n s₀ o l f h) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, mp', hrun, hb, hM', hfr⟩ := apdGoOK env n _ _ o l f h _ mp ks hS.1.arena.1 hps hh hM hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  obtain ⟨hS', hg⟩ := StageR.frame_hi hS hfr (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide) (by decide) (by decide)
  refine ⟨hl, hok, hst, by rw [hres]; exact hb, by rw [hres]; exact hM', hS', hg⟩

/-! ## The census theorem -/

theorem apd_decW0B {m : Mem} {r : List Word} {b : Bool} (h : r.headD 0 = if b then 1 else 0) :
    decW0B m r b := by
  cases b <;> (simp only [decW0B]; rw [h]; simp)

/-- **`all_level_params_defined(o, l, e)` refines `allLevelParamsDefined lps e`** under the stage
relation: `(o, l)` an `IW` slice decoding to the handles `lps`, whose names read back, `e` a handle;
the twin side must provide `ApdEnv` (the name store well formed, the `sort`/`const` levels of
`StoreDen` read back) and the walk's memo well formed on entry (it is cleared first, so any
`MemoRV` memo will do). The result is `0`/`1`; the stage relation and the pool's growth are kept. -/
@[refines ConRon.Arena.allLevelParamsDefined]
theorem allLevelParamsDefined_refines (p : Prog) (hp : ApdProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (o l e : Word) (he : H e) (lps : List NIdx) :
    RefAM p "all_level_params_defined" [o, l, e]
      (fun m a => StageR dn vis fe m a ∧ decHL m o.toNat l.toNat = some lps ∧ ApdEnv a ∧
        (∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks) ∧ ∃ mp0, apdMR m mp0)
      (ConRon.Arena.allLevelParamsDefined lps (decI e)) (KeepPost dn vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, hdec, env, ⟨ks, hks⟩, mp0, hM⟩
  cases n with
  | zero =>
    rw [invoke_eq _ hp.entry]; simp only [callFn, allLevelParamsDefinedL]; vcgen [exec] <;> grind
  | succ n =>
    refine triple_post (allLevelParamsDefined_spec_raw p hp.eview hp.lsnode hp.find hp.put hp.clear
      hp.lmem hp.lnode hp.lapd hp.ls hp.go hp.entry n s₀ o l e) ?_
    rintro r s' ⟨hloc, hm⟩
    obtain ⟨b, hrun, hr, hS', hg, -⟩ := apdEntry_ok n hS env o l e _ lps ks hks hdec he
      (memoRV_clear apdSch apdSch_wf bmKey apdVR _ mp0 hM) hm
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
    refine ⟨hloc, hok, ?_⟩
    change KeepPost dn vis fe decW0B _ _ (AM.st (ConRon.Arena.allLevelParamsDefined lps (decE e)) a₀) r
      (AM.res (ConRon.Arena.allLevelParamsDefined lps (decE e)) a₀)
    rw [hst, hres]
    exact ⟨hS', hg, apd_decW0B hr⟩

end L.Ind
