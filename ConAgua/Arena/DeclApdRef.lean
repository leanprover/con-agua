import ConAgua.Arena.DeclApdSpec

/-!
# `all_level_params_defined` refines `allLevelParamsDefined` (lane `decls3`)

The shape of `IndSumSpec5.lean`'s `mentions_const_go` refinement (`mcGoOK`), with three
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
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

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
  ArenaR.frame (fun b hb => by simp at hb; subst hb; simp [arenaArrs, storeArrs, memoArrs, APDM])
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
theorem ApdEnv.of_den {m : Mem} {a : AState} {fe : IFEnv} (hd : StoreDen m a fe)
    (hw : NStoreWF a.store.lss.ls.ns) : ApdEnv a := ⟨hw, hd.sort, hd.constLs⟩

/-! ## The parameter slice -/

theorem NmsR.congr {N : Word → ConLeche.Name → Prop} {m m' : Mem} {A : ArrId}
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
      cases e : apdW IW n m (rdW (m.arr64 POOL) lo) o l with
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
    have hlv := lvsR_of_slice hA ids Ls _ _ hsl (by have := m.top.toNat_lt; omega) hL
    cases e : alpdLsW n m o l (lsO m (tierW y) (idxW y)) (lsL m (tierW y) (idxW y)) with
    | none => rw [e] at hn; simp [apdR1] at hn
    | some z =>
      rw [e, apdR1_some] at hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
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
  | .bvar _ => pure (true, memo)
  | .lit _ => pure (true, memo)
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
    simp only [bind_assoc]
    congr 1; funext v
    cases v with
    | letE t v' b' =>
      simp only [apdArm, bind_assoc, pure_bind]
      congr 1; funext x
      split
      · simp_all
      · simp only [bind_assoc, pure_bind]
        congr 1; funext y; split <;> simp_all
    | _ => first | rfl | (simp only [apdArm, bind_assoc, pure_bind]; try (congr 1; funext x; split <;> simp_all))

theorem apdTwin_node (ks : List ConLeche.Name) (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx)
    (a : AState) (v : ENodeView) (hv : a.store.view h = some v) (hmiss : memo[h]? = none) :
    (ConRon.Arena.allLevelParamsDefinedGo ks memo (fuel + 1) h).run a =
      ((do let p ← apdArm ks memo fuel v; pure (p.1, p.2.insert h p.1) :
        AM (Bool × Std.HashMap EIdx Bool)).run a) := by
  rw [allLevelParamsDefinedGo_succ']
  simp only [hmiss, StateT.run_bind, view_run h a v hv, except_ok_bind]
