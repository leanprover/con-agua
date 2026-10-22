import ConAgua.Arena.WhnfIotaRec
import ConAgua.Arena.WhnfIotaRefine5
import ConAgua.Arena.WhnfIotaRefine6

/-!
# `iota_rec_at`'s pieces: the twin split the same way, and the inner pieces' proofs

The twin's `iotaRecAt` is named in blocks (`iotaRecCT` … `iotaRecCmpT`, one per L piece of
`WhnfIotaRec.lean`); `iotaRecAt_eq` puts them back together. Each L piece has a word-level model
through `callW` (`…W`), an L spec (`vcgen` + `finish` against `callW_spec`), and a refinement in
`CoreSpec` shape with the callees' specs as hypotheses.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## The twin, in blocks -/

section twin
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)

/-- The parameter comparison. -/
def iotaRecCmpT (rl : IRecRule) (lps : List NIdx) (us : LsIdx) (args : List EIdx) (rP : Nat)
    (margs : List EIdx) : AM Bool := do
  let cmpA ← recFireArgs rl lps us args rP
  defEqList r fe depth (margs.take rl.ctorParams) cmpA

/-- The checks past `iotaCase3` (the twin's text). -/
def iotaRecVckT (mI rP : Nat) (lps : List NIdx) (us : LsIdx) (args : List EIdx) (usj : LsIdx)
    (cvj : IConstantVal) (rl : IRecRule) (margs : List EIdx) (cmpL : LsIdx) : AM Bool := do
  if ← liftFueled "level comparison" (← lvlsEq? usj cmpL) then do
    let cmpA ← recFireArgs rl lps us args rP
    if ← defEqList r fe depth (margs.take rl.ctorParams) cmpA then do
      let tyC ← constTyAt cvj usj
      if ← iotaCertsFull r fe depth tyC margs then
        iotaIndexOk r fe depth mI rP rl.ctorParams tyC margs ((args.take mI).drop rP)
      else pure false
    else pure false
  else pure false

/-- The checks past `iotaCase3`, the parameter comparison named. -/
theorem iotaRecVckT_eq (mI rP : Nat) (lps : List NIdx) (us : LsIdx) (args : List EIdx)
    (usj : LsIdx) (cvj : IConstantVal) (rl : IRecRule) (margs : List EIdx) (cmpL : LsIdx) :
    iotaRecVckT r fe depth mI rP lps us args usj cvj rl margs cmpL = (do
      if ← liftFueled "level comparison" (← lvlsEq? usj cmpL) then do
        if ← iotaRecCmpT r fe depth rl lps us args rP margs then do
          let tyC ← constTyAt cvj usj
          if ← iotaCertsFull r fe depth tyC margs then
            iotaIndexOk r fe depth mI rP rl.ctorParams tyC margs ((args.take mI).drop rP)
          else pure false
        else pure false
      else pure false) := by
  simp only [iotaRecVckT, iotaRecCmpT, bind_assoc]

/-- The certificate family. -/
def iotaRecFamT (mI rP : Nat) (lps : List NIdx) (us : LsIdx) (args : List EIdx) (usj : LsIdx)
    (cvj : IConstantVal) (rl : IRecRule) (margs : List EIdx) : AM Bool :=
  if mode.verifiedChecks then do
    let cmpL ← recFireLevels rl lps us cvj.levelParams
    if ← iotaCase3 fe rl cvj cmpL then iotaRecVckT r fe depth mI rP lps us args usj cvj rl margs cmpL
    else pure true
  else pure true

/-- The fire past the major's arguments. -/
def iotaRecFire2T (c : NIdx) (mI rP : Nat) (lps : List NIdx) (us : LsIdx) (args : List EIdx)
    (usj : LsIdx) (cvj : IConstantVal) (rl : IRecRule) (margs : List EIdx) : AM (Option EIdx) :=
  if margs.length = rl.ctorParams + rl.nfields then do
    let fam ← iotaRecFamT mode r fe depth mI rP lps us args usj cvj rl margs
    if fam then do
      let rhs ← ruleRhsAt c rl.ctor lps rl.rhs us
      let x ← mkAppN rhs (args.take rP ++ margs.drop rl.ctorParams)
      pure (some x)
    else pure none
  else pure none

/-- The major's arguments, then the fire. -/
def iotaRecFireT (c : NIdx) (mI rP : Nat) (lps : List NIdx) (us : LsIdx) (args : List EIdx)
    (major : EIdx) (usj : LsIdx) (cvj : IConstantVal) (rl : IRecRule) : AM (Option EIdx) := do
  let margs ← getAppArgs coreWalkFuel major
  iotaRecFire2T mode r fe depth c mI rP lps us args usj cvj rl margs

/-- The major's preparation, its head's constructor, the rule. -/
def iotaRecMajorT (c : NIdx) (us : LsIdx) (cv : IConstantVal) (mI rP : Nat)
    (rules : List IRecRule) (args : List EIdx) : AM (Option EIdx) := do
  let b0 ← internE (.bvar 0)
  let major ← prepareMajor mode r fe depth c rules (args.getD mI b0)
  let hh ← getAppFn coreWalkFuel major
  if hh.tag == ETag.const then
    match ← view hh with
    | .const cj usj =>
      match fe.find? cj with
      | some (.ctorInfo cvj _ _) =>
        match findRule rules cj with
        | some rl => iotaRecFireT mode r fe depth c mI rP cv.levelParams us args major usj cvj rl
        | none => pure none
      | _ => pure none
    | _ => pure none
  else pure none

/-- The recursor's record, the arity, the levels' length, the telescope. -/
def iotaRecCT (c : NIdx) (us : LsIdx) (sargs : Array EIdx) (n : Nat) : AM (Option EIdx) :=
  match fe.find? c with
  | some (.recInfo cv mI rP rules) => do
    if n ≠ mI + 1 then pure none
    else do
    let args := (takeEidx sargs n).toList
    match ← viewLsLen us with
    | none => failDanglingLs
    | some usl =>
    let peeled ← peelPis (mI + 1) cv.type
    if args.length = mI + 1 ∧ usl = cv.levelParams.length ∧ peeled.isSome then
      iotaRecMajorT mode r fe depth c us cv mI rP rules args
    else pure none
  | _ => pure none

theorem ite_bind' {m : Type → Type} [Monad m] {α β : Type} (c : Prop) [Decidable c] (x y : m α)
    (f : α → m β) : (ite c x y >>= f) = ite c (x >>= f) (y >>= f) := by
  split <;> rfl

/-- **The twin, put back together.** -/
theorem iotaRecAt_eq (hd : EIdx) (sargs : Array EIdx) (n : Nat) :
    iotaRecAt mode r fe depth hd sargs n =
      if hd.tag == ETag.const then do
        match ← viewConst hd with
        | none => failDanglingE
        | some (c, us) => iotaRecCT mode r fe depth c us sargs n
      else pure none := by
  unfold iotaRecAt
  split
  · congr 1; funext x
    rcases x with _ | ⟨c, us⟩
    · rfl
    · unfold iotaRecCT
      cases h : fe.find? c with
      | none => simp only [h]
      | some ci =>
        cases ci <;> simp only [h]
        rename_i cv mI rP rules
        by_cases hn : n ≠ mI + 1
        · rw [if_pos hn, if_pos hn]
        · rw [if_neg hn, if_neg hn]
          congr 1; funext x
          rcases x with _ | usl
          · rfl
          · show (peelPis (mI + 1) cv.type >>= _) = (peelPis (mI + 1) cv.type >>= _)
            congr 1; funext peeled
            by_cases hc : (takeEidx sargs n).toList.length = mI + 1 ∧ usl = cv.levelParams.length ∧
                peeled.isSome = true
            · rw [if_pos hc, if_pos hc]
              unfold iotaRecMajorT
              congr 1; funext b0; congr 1; funext major; congr 1; funext hh
              by_cases ht : (Idx.tag hh == ETag.const) = true
              · rw [if_pos ht, if_pos ht]
                congr 1; funext v
                rcases v with _ | _ | _ | ⟨cj, usj⟩ <;> try rfl
                show (match fe.find? cj with | _ => _) = _
                cases h2 : fe.find? cj with
                | none => simp only [h2]
                | some ci =>
                  cases ci <;> simp only [h2]
                  cases findRule _ cj with
                  | none => simp only
                  | some rl =>
                    simp only [iotaRecFireT, iotaRecFire2T, iotaRecFamT, iotaRecVckT,
                      bind_assoc, ite_bind', pure_bind]
              · rw [if_neg ht, if_neg ht]
            · rw [if_neg hc, if_neg hc]
  · rfl

end twin

/-! ## What the proofs assume -/

/-- **Program hypotheses**: part 4's (`IotaProg4`), the pieces, and the `bvar` interning. -/
structure IotaRecProg' (p : Prog) : Prop extends IotaProg4 p, IotaRecProg p where
  bvf : p.lookup "bvar_find" = some bvarFind
  bvp : p.lookup "bvar_push" = some bvarPush
  bvi : p.lookup "intern_bvar" = some internBVar

/-- **The callees `iota_rec_at`'s pieces read the record pool after leave it alone** (new stub
assumption, as `ErecKeptKnot`/`ErecKeptInst`: the record pool grows only when a declaration is
installed, never during a term check). -/
def ErecKeptRec (p : Prog) : Prop :=
  ∀ (n : Nat) (f : FnName) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem),
    f ∈ ["rec_fire_levels", "iota_case3", "lvls_eq_c", "rec_fire_args", "const_ty_at",
      "iota_certs_full"] →
    callW p n f vs m = some (r, m') → m'.arr64 EREC = m.arr64 EREC

/-- **A level-list comparison that runs compares lists that read back** (new stub assumption):
`lvls_eq_c`'s refinement (`lvlsEqC_refines`) asks that both handles denote, which `CoreS` does
not carry (as `CoreS.lvl_den` for single levels); the twin's store is well formed, and a cached
verdict was stored by a comparison whose readbacks succeeded. -/
def LvlsEqDen (p : Prog) : Prop :=
  ∀ (n : Nat) (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb u v : Word) (r : List Word) (m' : Mem), CoreS dn m a vis fe M eb →
    callW p n "lvls_eq_c" [u, v] m = some (r, m') →
    (∃ lu, denoteLs a.store.lss (decI u) = some lu) ∧ (∃ lv, denoteLs a.store.lss (decI v) = some lv)

/-- **A stored recursor's shape** (new stub assumption, an invariant of every installed
environment that `EnvR` does not carry): the rule prefix is at most the major's index plus one,
and a plain rule's constructor parameters lie within it. The L code reads the leading `rP`
arguments as a stack slice of the spine, and a plain rule's comparands as a prefix of it. -/
def RecShape : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (vis : Word) (fe : IFEnv) (c : NIdx)
    (cv : IConstantVal) (mI rP : Nat) (rules : List IRecRule), EnvR dn m vis fe →
    fe.find? c = some (.recInfo cv mI rP rules) →
    rP ≤ mI + 1 ∧ ∀ rl ∈ rules, rl.fire = .plain → rl.ctorParams ≤ rP

theorem instSpinePins_take (lps : List NIdx) (us : LsIdx) (args : List EIdx) (rP : Nat) :
    ∀ pins : List EIdx, instSpinePins lps us (args.take rP) rP pins = instSpinePins lps us args rP pins
  | [] => rfl
  | x :: xs => by
    simp only [instSpinePins, List.take_take, Nat.min_self, instSpinePins_take lps us args rP xs]

theorem recFireArgs_take (rl : IRecRule) (lps : List NIdx) (us : LsIdx) (args : List EIdx) (rP : Nat)
    (h : rl.fire = .plain → rl.ctorParams ≤ rP) :
    recFireArgs rl lps us (args.take rP) rP = recFireArgs rl lps us args rP := by
  cases hf : rl.fire with
  | nested lv pins =>
    rw [recFireArgs_nested_eq _ _ _ _ _ _ _ hf, recFireArgs_nested_eq _ _ _ _ _ _ _ hf,
      instSpinePins_take]
  | plain =>
    simp only [recFireArgs, hf, List.take_take, Nat.min_eq_left (h hf)]

/-! ## `erec_push(o, c)` -/

/-- Model of the `erec_push` loop at L fuel `k`. -/
def epW (o c so : Word) : Nat → Mem → Word → Option Mem
  | 0, _, _ => none
  | k + 1, m, j =>
    if j < c then
      if h : (o + j).toNat < (m.arr64 EREC).size then
        if (so + j).toNat < (m.arr64 SPN).size ∧ (136 : Word).toNat < (m.arr64 CTL).size then
          epW o c so k ((m.set64 SPN (so + j) (m.arr64 EREC)[(o + j).toNat]).set64 CTL 136 (so + j + 1))
            (j + 1)
        else none
      else none
    else some m

theorem epW_end (o c so : Word) (k : Nat) (m : Mem) (j : Word) (h : ¬ j < c) :
    epW o c so (k + 1) m j = some m := by
  simp only [epW, h, ↓reduceIte]

theorem epW_cont (o c so : Word) (k : Nat) (m : Mem) (j : Word) (h : j < c)
    (h1 : (o + j).toNat < (m.arr64 EREC).size)
    (h2 : (so + j).toNat < (m.arr64 SPN).size ∧ (136 : Word).toNat < (m.arr64 CTL).size) :
    epW o c so (k + 1) m j =
      epW o c so k ((m.set64 SPN (so + j) (m.arr64 EREC)[(o + j).toNat]).set64 CTL 136 (so + j + 1))
        (j + 1) := by
  simp only [epW, h, ↓reduceIte, h1, ↓reduceDIte, h2, and_self]

theorem epW_bad1 (o c so : Word) (k : Nat) (m : Mem) (j : Word) (h : j < c)
    (h1 : ¬ (o + j).toNat < (m.arr64 EREC).size) : epW o c so (k + 1) m j = none := by
  simp only [epW, h, ↓reduceIte, h1, ↓reduceDIte]

theorem epW_bad2 (o c so : Word) (k : Nat) (m : Mem) (j : Word) (h : j < c)
    (h1 : (o + j).toNat < (m.arr64 EREC).size)
    (h2 : ¬ ((so + j).toNat < (m.arr64 SPN).size ∧ (136 : Word).toNat < (m.arr64 CTL).size)) :
    epW o c so (k + 1) m j = none := by
  simp only [epW, h, ↓reduceIte, h1, ↓reduceDIte, h2]

theorem erecPushLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k erecPushLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 3 = s₀.loc 3 ∧
      epW (s₀.loc 0) (s₀.loc 1) (s₀.loc 3) k s₀.mem (s₀.loc 4) = some s'.mem; ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := erecPushLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish [epW_end, epW_cont, epW_bad1, epW_bad2]

theorem erecPushLoop_step_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p k) erecPushLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 3 = s₀.loc 3 ∧
      epW (s₀.loc 0) (s₀.loc 1) (s₀.loc 3) (k + 1) s₀.mem (s₀.loc 4) = some s'.mem; ⊤⦄ :=
  Triple.step_exec (erecPushLoop_spec p (k + 1) s₀)

/-- Model of `erec_push`. -/
def epTop (k : Nat) (m : Mem) (o c kd : Word) : Option (List Word × Mem) :=
  if kd ≠ 1 then some ([0], m) else
  if (136 : Word).toNat < (m.arr64 CTL).size then
    if UInt64.ofNat (m.arr64 SPN).size < rdW (m.arr64 CTL) 136 then none
    else if UInt64.ofNat (m.arr64 SPN).size - rdW (m.arr64 CTL) 136 < c then none
    else match epW o c (rdW (m.arr64 CTL) 136) (k + 1) m 0 with
      | none => none
      | some m' => some ([rdW (m.arr64 CTL) 136], m')
  else none

theorem erecPush_spec (p : Prog) (hp : p.lookup "erec_push" = some erecPushL) (k : Nat) (s₀ : St)
    (o c kd : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "erec_push" [o, c, kd]
    ⦃fun r s' => LocEq s' s₀ ∧ epTop k s₀.mem o c kd = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, erecPushL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, erecPushLoop_step_spec p k] <;>
  simp_all [epTop, Cmp.eval, BinOp.eval, Mem.len64, LocEq, St.setLocs_cons, St.setLoc_loc,
    St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal,
    Sig.retOr, rdW, CTL] <;>
  (have h136 : 136 < (s₀.mem.arr64 1).size := by assumption
   refine ⟨h136, ?_⟩
   simp_all [getD_136 _ h136, SPN])

/-- Element `j` of a decoded handle slice. -/
theorem hslice?_at {k : IdxKind} {a : Array Word} {o c : Nat} {l : List (Idx k)}
    (h : hslice? a o c = some l) (j : Nat) (hj : j < c) :
    ∃ w, a[o + j]? = some w ∧ w.toNat < 2 ^ 32 ∧ l[j]? = some (decI w) := by
  obtain ⟨hl, hg⟩ := mapM_option_get _ _ _ h
  have := hg j (by simpa using hj)
  simp only [List.getElem_range] at this
  obtain ⟨w, hw, hw32, hx⟩ := hd?_some (k := k) (x := l[j]'(by simp at hl; omega)) (by
    rw [this]; exact List.getElem?_eq_getElem _)
  exact ⟨w, hw, hw32, by rw [← hx]; exact List.getElem?_eq_getElem _⟩

/-- **The `erec_push` loop** pushes the rest of the slice. -/
theorem epW_ok (E : Array Word) (hE : E.size < 2 ^ 63) (o c so : Word) (pins : List EIdx)
    (hpins : hslice? E o.toNat c.toNat = some pins) :
    ∀ (K k : Nat) (m : Mem) (j : Word) (m' : Mem), c.toNat - j.toNat = K → j.toNat ≤ c.toNat →
      m.arr64 EREC = E → spTop m = so + j → so.toNat + c.toNat ≤ (m.arr64 SPN).size →
      (m.arr64 SPN).size < 2 ^ 63 → epW o c so k m j = some m' →
      MemFrame [SPN] [136] m m' ∧ StackGrew m m' ∧ spTop m' = so + c ∧
        SpineR m' (so + j) (c - j) (pins.drop j.toNat).toArray := by
  intro K
  induction K with
  | zero =>
    intro k m j m' hK hj hEm htop hso hspn hL
    have hn : ¬ j < c := fun h => by
      have : j.toNat < c.toNat := h
      omega
    have hjc : j = c := UInt64.toNat_inj.mp (by omega)
    cases k with
    | zero => simp [epW] at hL
    | succ k =>
    rw [epW_end o c so k m j hn] at hL
    cases hL
    subst hjc
    have hdrop : pins.drop j.toNat = [] := by
      apply List.drop_eq_nil_of_le; rw [hslice?_length hpins]; omega
    rw [hdrop, UInt64.sub_self]
    refine ⟨MemFrame.refl _ _ _, (StackKept.refl _).toGrew, htop, SpineR.nil_at m _ ?_⟩
    rw [UInt64.toNat_add]; simp; omega
  | succ K ih =>
    intro k m j m' hK hj hEm htop hso hspn hL
    have hlt : j < c := by
      have : j.toNat < c.toNat := by omega
      exact this
    have hlt' : j.toNat < c.toNat := hlt
    cases k with
    | zero => simp [epW] at hL
    | succ k =>
    obtain ⟨w, hw, hw32, hpw⟩ := hslice?_at hpins j.toNat hlt'
    have hoj : (o + j).toNat = o.toNat + j.toNat := by
      have := (Array.getElem?_eq_some_iff.mp hw).1
      rw [UInt64.toNat_add]; simp; omega
    have h1 : (o + j).toNat < (m.arr64 EREC).size := by
      rw [hoj, hEm]; exact (Array.getElem?_eq_some_iff.mp hw).1
    have hval : (m.arr64 EREC)[(o + j).toNat] = w := by
      have := (Array.getElem?_eq_some_iff.mp hw).2
      simp only [hEm, hoj]; exact this
    have hsoj : (so + j).toNat = so.toNat + j.toNat := by
      rw [UInt64.toNat_add]; simp; omega
    by_cases hgn : ¬ ((so + j).toNat < (m.arr64 SPN).size ∧ (136 : Word).toNat < (m.arr64 CTL).size)
    · rw [epW_bad2 o c so k m j hlt h1 hgn] at hL; cases hL
    have hg := Classical.not_not.mp hgn
    rw [epW_cont o c so k m j hlt h1 hg, hval] at hL
    obtain ⟨hfr, hsp3, hgrew, hslot, hsz3⟩ := push_step m (so + j) w hg.1 hg.2 htop (by omega)
    have hj1 : (j + 1).toNat = j.toNat + 1 := uint64_succ_toNat c j hlt
    have hEm3 : ((m.set64 SPN (so + j) w).set64 CTL 136 (so + j + 1)).arr64 EREC = E := by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide), hEm]
    obtain ⟨hfr4, hgr4, htop4, hys⟩ := ih k _ (j + 1) m' (by omega) (by omega) hEm3
      (by rw [hsp3, UInt64.add_assoc]) (by rw [hsz3]; exact hso) (by rw [hsz3]; exact hspn) hL
    refine ⟨hfr.trans hfr4, hgrew.trans hgr4, htop4, ?_⟩
    have hdrop : pins.drop j.toNat = decE w :: pins.drop (j.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [hslice?_length hpins]; exact hlt')]
      congr 1
      have := hpw
      rw [List.getElem?_eq_getElem (by rw [hslice?_length hpins]; exact hlt')] at this
      exact Option.some.inj this
    have e1 : c - j = (c - (j + 1)) + 1 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega),
        UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega), hj1]
      simp; omega
    have e2 : so + (j + 1) = so + j + 1 := by rw [UInt64.add_assoc]
    have hsjp1 : (so + j + 1).toNat = (so + j).toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    rw [e1, hdrop]
    rw [e2, hj1] at hys
    have hsize' : (m'.arr64 SPN).size = (m.arr64 SPN).size := by
      rw [hgr4.2.1, hsz3]
    refine SpineR.cons_slot m' (so + j) (c - (j + 1)) w _ hw32 ?_ hys ?_ (by rw [hsize']; exact hspn)
    · have := hgr4.2.2 (so + j) (by rw [hsp3, UInt64.lt_iff_toNat_lt, hsjp1]; omega)
      rw [this, hslot]
    · rw [hsize', UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega), hsoj]
      omega

/-- **`erec_push` as a run**: the slice is on the stack at the old top, the top raised past it,
only the stack and its top written. -/
theorem callW_erecPush (p : Prog) (hp : p.lookup "erec_push" = some erecPushL) (n : Nat) (m : Mem)
    (o c : Word) (pins : List EIdx) (hE : (m.arr64 EREC).size < 2 ^ 63)
    (hspn : (m.arr64 SPN).size < 2 ^ 63)
    (hpins : hslice? (m.arr64 EREC) o.toNat c.toNat = some pins) (r : List Word) (m' : Mem)
    (h : callW p n "erec_push" [o, c, 1] m = some (r, m')) :
    MemFrame [SPN] [136] m m' ∧ StackGrew m m' ∧ r.headD 0 = spTop m ∧ spTop m' = spTop m + c ∧
      SpineR m' (spTop m) c pins.toArray := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (erecPush_spec p hp n ⟨m, Locals.init []⟩ o c 1) h
  rw [ht] at hW
  simp only [epTop, ne_eq, not_true_eq_false, ↓reduceIte] at hW
  by_cases h136n : ¬ (136 : Word).toNat < (m.arr64 CTL).size
  · rw [if_neg h136n] at hW; cases hW
  have h136 : (136 : Word).toNat < (m.arr64 CTL).size := Classical.not_not.mp h136n
  rw [if_pos h136] at hW
  by_cases hg1 : UInt64.ofNat (m.arr64 SPN).size < rdW (m.arr64 CTL) 136
  · rw [if_pos hg1] at hW; cases hW
  rw [if_neg hg1] at hW
  by_cases hg2 : UInt64.ofNat (m.arr64 SPN).size - rdW (m.arr64 CTL) 136 < c
  · rw [if_pos hg2] at hW; cases hW
  rw [if_neg hg2] at hW
  cases hm : epW o c (rdW (m.arr64 CTL) 136) (n + 1) m 0 with
  | none => rw [hm] at hW; cases hW
  | some m₁ =>
  rw [hm] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hmm⟩ := hW
  subst hmm
  have h64 : (m.arr64 SPN).size < 2 ^ 64 := by omega
  have hsolt : (rdW (m.arr64 CTL) 136).toNat ≤ (m.arr64 SPN).size := by
    have : ¬ (m.arr64 SPN).size < (rdW (m.arr64 CTL) 136).toNat := by
      intro h
      apply hg1
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' h64]; exact h
    omega
  have hso : (rdW (m.arr64 CTL) 136).toNat + c.toNat ≤ (m.arr64 SPN).size := by
    have h2 : ¬ UInt64.ofNat (m.arr64 SPN).size - rdW (m.arr64 CTL) 136 < c := hg2
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' h64]; exact hsolt),
      UInt64.toNat_ofNat_of_lt' h64] at h2
    omega
  have hspt : spTop m = rdW (m.arr64 CTL) 136 + 0 := by rw [UInt64.add_zero]; rfl
  obtain ⟨hfr, hgr, htop, hys⟩ := epW_ok (m.arr64 EREC) hE o c (rdW (m.arr64 CTL) 136) pins hpins
    (c.toNat - (0 : Word).toNat) (n + 1) m 0 m₁ rfl (by simp) rfl hspt hso hspn hm
  refine ⟨hfr, hgr, by rw [← hr]; rfl, htop, ?_⟩
  simp only [UInt64.add_zero, UInt64.sub_zero, UInt64.toNat_zero, List.drop_zero] at hys
  exact hys

/-! ## Reading decoded records by word -/

theorem irRdW {b : Array Word} {q : Word} {w : Word} (hsz : b.size < 2 ^ 63) (c : Word) {k : Nat}
    (hc : c.toNat = k) (hb : b[q.toNat + k]? = some w) : rdW b (q + c) = w := by
  have hlt := (Array.getElem?_eq_some_iff.mp hb).1
  have : (q + c).toNat = q.toNat + k := by
    rw [UInt64.toNat_add, hc, Nat.mod_eq_of_lt (by omega)]
  simp only [rdW, this, hb]; rfl

theorem irRdW0 {b : Array Word} {q : Word} {w : Word} (hb : b[q.toNat]? = some w) : rdW b q = w := by
  simp only [rdW, hb]; rfl

/-- The words of a `ConstantVal` decoded at `q + 1`. -/
theorem decCV_rd1 {b : Array Word} {q : Word} {cv : IConstantVal} (hsz : b.size < 2 ^ 63)
    (h : decCV b (q.toNat + 1) = some cv) :
    HW (rdW b (q + 1)) ∧ cv.name = decI (rdW b (q + 1)) ∧
      hslice? b (rdW b (q + 2)).toNat (rdW b (q + 3)).toNat = some cv.levelParams ∧
      cv.levelParams.length = (rdW b (q + 3)).toNat ∧
      HW (rdW b (q + 4)) ∧ cv.type = decI (rdW b (q + 4)) := by
  simp only [decCV, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨nm, hn, ls, hl, ty, ht, rfl⟩ := h
  obtain ⟨w1, hw1, hl1, rfl⟩ := hd?_some hn
  obtain ⟨w4, hw4, hl4, rfl⟩ := hd?_some ht
  simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hl
  obtain ⟨o, ⟨w2, hw2, rfl⟩, c, ⟨w3, hw3, rfl⟩, hs⟩ := hl
  have e1 : rdW b (q + 1) = w1 := irRdW hsz 1 rfl hw1
  have e2 : rdW b (q + 2) = w2 := irRdW hsz 2 rfl (by rw [← hw2]; congr 1)
  have e3 : rdW b (q + 3) = w3 := irRdW hsz 3 rfl (by rw [← hw3]; congr 1)
  have e4 : rdW b (q + 4) = w4 := irRdW hsz 4 rfl (by rw [← hw4]; congr 1)
  rw [e1, e2, e3, e4]
  exact ⟨hl1, rfl, hs, hslice?_length hs, hl4, rfl⟩

/-- A recursor record by its kind word `5`. -/
theorem decCI_rec_rd {b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {ci : IConstantInfo} (hsz : b.size < 2 ^ 63) (h : decCI b dn q.toNat = some ci) :
    (rdW b q = 5 → ∃ cv rules, ci = .recInfo cv (rdW b (q + 5)).toNat (rdW b (q + 6)).toNat rules ∧
      decCV b (q.toNat + 1) = some cv ∧
      decRules b (rdW b (q + 7)).toNat (rdW b (q + 8)).toNat = some rules) ∧
    (rdW b q ≠ 5 → ∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) := by
  cases hq : b[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  rw [irRdW0 hq]
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  constructor
  · intro hw; subst hw
    simp only [show UInt64.toNat 5 = 5 from rfl, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cv, hcv, mI, hmI, rP, hrP, o, ho, c, hc, rules, hr, rfl⟩ := h
    simp only [Option.map_eq_some_iff] at hmI hrP ho hc
    obtain ⟨w5, hw5, rfl⟩ := hmI
    obtain ⟨w6, hw6, rfl⟩ := hrP
    obtain ⟨w7, hw7, rfl⟩ := ho
    obtain ⟨w8, hw8, rfl⟩ := hc
    rw [irRdW hsz 5 rfl hw5, irRdW hsz 6 rfl hw6, irRdW hsz 7 rfl hw7, irRdW hsz 8 rfl hw8]
    exact ⟨cv, rules, rfl, hcv, hr⟩
  · intro hw cv mI rP rules hc
    subst hc
    have hne : w.toNat ≠ 5 := fun e => hw (UInt64.toNat_inj.mp (by rw [e]; rfl))
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h hne; simp [Option.bind_eq_some_iff] at h hne)

/-- A constructor record by its kind word `4`. -/
theorem decCI_ctor_rd {b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {ci : IConstantInfo} (h : decCI b dn q.toNat = some ci) (h4 : rdW b q = 4) :
    ∃ cv np nf, ci = .ctorInfo cv np nf ∧ decCV b (q.toNat + 1) = some cv := by
  cases hq : b[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  rw [irRdW0 hq] at h4
  subst h4
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some,
    show UInt64.toNat 4 = 4 from rfl, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨cv, hcv, np, -, nf, -, rfl⟩ := h
  exact ⟨cv, np, nf, rfl, hcv⟩

/-- The common fields of a decoded rule record. -/
theorem decRule_tail {b : Array Word} {q : Nat} {fire : IRecRuleFire} {rl : IRecRule}
    (h : ((hd? b q).bind fun c => (nat? b (q + 1)).bind fun nf => (nat? b (q + 2)).bind fun cp =>
      (hd? b (q + 8)).bind fun rhs => (bool? b (q + 9)).bind fun k => (bool? b (q + 10)).bind
        fun eta => pure (IRecRule.mk c nf cp fire rhs k eta)) = some rl) :
    rl.fire = fire ∧ hd? b q = some rl.ctor ∧ nat? b (q + 1) = some rl.nfields ∧
      nat? b (q + 2) = some rl.ctorParams ∧ hd? b (q + 8) = some rl.rhs ∧
      bool? b (q + 9) = some rl.k := by
  simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨c, hc, nf, hnf, cp, hcp, rhs, hrhs, k, hk, eta, -, rfl⟩ := h
  exact ⟨rfl, hc, hnf, hcp, hrhs, hk⟩

/-- The words of a rule record. -/
theorem decRule_rd {b : Array Word} {q : Word} {rl : IRecRule} (hsz : b.size < 2 ^ 63)
    (h : decRule b q.toNat = some rl) :
    HW (rdW b q) ∧ rl.ctor = decI (rdW b q) ∧ rl.nfields = (rdW b (q + 1)).toNat ∧
      rl.ctorParams = (rdW b (q + 2)).toNat ∧
      (rdW b (q + 3) ≠ 1 → rl.fire = .plain) ∧
      (rdW b (q + 3) = 1 → ∃ lv pins, rl.fire = .nested lv pins ∧
        hslice? b (rdW b (q + 6)).toNat (rdW b (q + 7)).toNat = some pins) ∧
      HW (rdW b (q + 8)) ∧ rl.rhs = decI (rdW b (q + 8)) ∧ rl.k = (rdW b (q + 9) != 0) := by
  simp only [decRule, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨kd, hkd, h⟩ := h
  simp only [nat?, Option.map_eq_some_iff] at hkd
  obtain ⟨w3, hw3, rfl⟩ := hkd
  have e3 : rdW b (q + 3) = w3 := irRdW hsz 3 rfl hw3
  have common : ∀ fire, ((hd? b q.toNat).bind fun c => (nat? b (q.toNat + 1)).bind fun nf =>
      (nat? b (q.toNat + 2)).bind fun cp => (hd? b (q.toNat + 8)).bind fun rhs =>
      (bool? b (q.toNat + 9)).bind fun k => (bool? b (q.toNat + 10)).bind fun eta =>
      pure (IRecRule.mk c nf cp fire rhs k eta)) = some rl →
      HW (rdW b q) ∧ rl.ctor = decI (rdW b q) ∧ rl.nfields = (rdW b (q + 1)).toNat ∧
      rl.ctorParams = (rdW b (q + 2)).toNat ∧ HW (rdW b (q + 8)) ∧
      rl.rhs = decI (rdW b (q + 8)) ∧ rl.k = (rdW b (q + 9) != 0) := by
    intro fire hf
    obtain ⟨-, hc, hnf, hcp, hrhs, hk⟩ := decRule_tail hf
    obtain ⟨w0, hw0, hl0, e0⟩ := hd?_some hc
    obtain ⟨w8, hw8, hl8, e8⟩ := hd?_some hrhs
    simp only [nat?, bool?, Option.map_eq_some_iff] at hnf hcp hk
    obtain ⟨w1, hw1, e1⟩ := hnf
    obtain ⟨w2, hw2, e2⟩ := hcp
    obtain ⟨w9, hw9, e9⟩ := hk
    rw [irRdW0 hw0, irRdW hsz 1 rfl hw1, irRdW hsz 2 rfl hw2, irRdW hsz 8 rfl hw8,
      irRdW hsz 9 rfl hw9]
    exact ⟨hl0, e0, e1.symm, e2.symm, hl8, e8, e9.symm⟩
  rcases hk : w3.toNat with _ | _ | k
  · rw [hk] at h
    simp only [Option.bind_some] at h
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := common _ h
    have hf := (decRule_tail h).1
    refine ⟨c1, c2, c3, c4, fun _ => hf, fun h3 => ?_, c5, c6, c7⟩
    rw [e3] at h3; subst h3; simp at hk
  · rw [hk] at h
    cases hlv : hlist? (k := .level) b (q.toNat + 4) with
    | none => rw [hlv] at h; simp at h
    | some lv =>
    cases hp : hlist? (k := .expr) b (q.toNat + 6) with
    | none => rw [hlv, hp] at h; simp at h
    | some pins =>
    rw [hlv, hp] at h
    simp only [Option.bind_some] at h
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := common _ h
    have hf := (decRule_tail h).1
    have h31 : rdW b (q + 3) = 1 := by rw [e3]; exact UInt64.toNat_inj.mp (by rw [hk]; rfl)
    refine ⟨c1, c2, c3, c4, fun h3 => absurd h31 h3, fun _ => ⟨lv, pins, hf, ?_⟩, c5, c6, c7⟩
    simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hp
    obtain ⟨o, ⟨w6, hw6, rfl⟩, c, ⟨w7, hw7, rfl⟩, hs⟩ := hp
    rw [irRdW hsz 6 rfl hw6, irRdW hsz 7 rfl (by rw [← hw7]; congr 1)]
    exact hs
  · rw [hk] at h
    simp at h


theorem callW_erecPush_no (p : Prog) (hp : p.lookup "erec_push" = some erecPushL) (n : Nat) (m : Mem)
    (o c kd : Word) (hk : kd ≠ 1) (r : List Word) (m' : Mem)
    (h : callW p n "erec_push" [o, c, kd] m = some (r, m')) : r.headD 0 = 0 ∧ m' = m := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (erecPush_spec p hp n ⟨m, Locals.init []⟩ o c kd) h
  rw [ht] at hW
  simp only [epTop, hk, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq,
    Prod.mk.injEq] at hW
  exact ⟨by rw [← hW.1]; rfl, hW.2.symm⟩

/-! ## `stack_cover(x)` -/

/-- Model of `stack_cover`. -/
def scovW (m : Mem) (x : Word) : Option Mem :=
  if rdW (m.arr64 CTL) 136 < x then
    if (136 : Word).toNat < (m.arr64 CTL).size then some (m.set64 CTL 136 x) else none
  else some m

theorem stackCover_spec (p : Prog) (hp : p.lookup "stack_cover" = some stackCoverL) (n : Nat)
    (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "stack_cover" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ scovW s₀.mem x = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, stackCoverL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
    finish [scovW]

/-- **`stack_cover` as a run**: only the top written, the stack kept below the old top, the new
top at least `x`. -/
theorem callW_stackCover (p : Prog) (hp : p.lookup "stack_cover" = some stackCoverL) (n : Nat)
    (m : Mem) (x : Word) (r : List Word) (m' : Mem)
    (h : callW p n "stack_cover" [x] m = some (r, m')) :
    MemFrame [] [136] m m' ∧ StackGrew m m' ∧ x ≤ spTop m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (stackCover_spec p hp n ⟨m, Locals.init []⟩ x) h
  rw [ht] at hW
  simp only [scovW] at hW
  by_cases hlt : rdW (m.arr64 CTL) 136 < x
  · rw [if_pos hlt] at hW
    by_cases h136 : (136 : Word).toNat < (m.arr64 CTL).size
    · rw [if_pos h136] at hW
      cases hW
      have hspn : (m.set64 CTL 136 x).arr64 SPN = m.arr64 SPN :=
        Mem.arr64_set64_ne _ _ _ _ _ (by decide)
      have htop : spTop (m.set64 CTL 136 x) = x := by
        unfold spTop; rw [rdW_set64, if_pos ⟨rfl, rfl, h136⟩]
      refine ⟨MemFrame.setCtl m 136 x, ⟨?_, by rw [hspn], fun i _ => by simp only [spW, hspn]⟩,
        by rw [htop]; exact UInt64.le_refl _⟩
      rw [htop]; exact UInt64.le_of_lt hlt
    · rw [if_neg h136] at hW; cases hW
  · rw [if_neg hlt] at hW
    cases hW
    exact ⟨MemFrame.refl _ _ _, (StackKept.refl _).toGrew, UInt64.not_lt.mp hlt⟩

/-! ## `iota_rec_cmp(mode, vis, d, us, recP, so, rl, mo)` -/

/-- Model of `iota_rec_cmp`. -/
def irCmpW (p : Prog) (n : Nat) (m : Mem) (mode vis d us recP so rl mo : Word) :
    Option (Word × Mem) :=
  match callW p n "erec_push" [rdW (m.arr64 EREC) (rl + 6), rdW (m.arr64 EREC) (rl + 7),
      rdW (m.arr64 EREC) (rl + 3)] m with
  | none => none
  | some (rp, m1) =>
  match callW p n "rec_fire_args" [rdW (m1.arr64 EREC) (rl + 3), rp.headD 0,
      rdW (m1.arr64 EREC) (rl + 7), rdW (m1.arr64 EREC) (recP + 2), rdW (m1.arr64 EREC) (recP + 3),
      us, so, rdW (m1.arr64 EREC) (recP + 6), rdW (m1.arr64 EREC) (rl + 2)] m1 with
  | none => none
  | some (ra, m2) =>
  match callW p n "stack_cover" [ra.headD 0 + ra.tail.headD 0] m2 with
  | none => none
  | some (rx, m3) =>
  match callW p n "defeq_list" [mode, vis, d, mo, rdW (m3.arr64 EREC) (rl + 2), ra.headD 0,
      ra.tail.headD 0] m3 with
  | none => none
  | some (rd, m4) =>
    if (136 : Word).toNat < (m4.arr64 CTL).size then
      some (rd.headD 0, m4.set64 CTL 136 (rdW (m.arr64 CTL) 136))
    else none

theorem iotaRecCmp_spec (p : Prog) (hp : p.lookup "iota_rec_cmp" = some iotaRecCmpL) (n : Nat)
    (s₀ : St) (mode vis d us recP so rl mo : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_rec_cmp" [mode, vis, d, us, recP, so, rl, mo]
    ⦃fun r s' => LocEq s' s₀ ∧ irCmpW p n s₀.mem mode vis d us recP so rl mo = some (r.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaRecCmpL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "erec_push", callW_spec p n "rec_fire_args", callW_spec p n "stack_cover",
    callW_spec p n "defeq_list"] <;>
  simp_all [-UInt64.toNat_add, irCmpW, EREC, CTL, BinOp.eval, getElem_rdW', Cmp.eval, LocEq,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr] <;>
  (congr 1; apply rdW_eq; simp_all)

/-- **`iota_rec_cmp` refines the parameter comparison.** -/
theorem iotaRecCmp_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d us recP so rl mo mn sn : Word) (lps : List NIdx) (rule : IRecRule)
    (args margs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW us →
    hslice? (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps →
    decRule (s₀.mem.arr64 EREC) rl.toNat = some rule →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat ≤ sn.toNat →
    (rule.fire = .plain → rule.ctorParams ≤ (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat) →
    SpineR s₀.mem mo mn margs → mo.toNat + mn.toNat ≤ (spTop s₀.mem).toNat →
    rule.ctorParams ≤ mn.toNat →
    CoreSpec p (n + 1) "iota_rec_cmp" [mode, vis, d, us, recP, so, rl, mo]
      (iotaRecCmpT (coreKnot (decMode mode) fe id F) fe d.toNat rule lps (decI us) args.toList
        (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat margs.toList) decBool s₀ a₀ dn vis fe MM eb := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d us recP so rl mo mn sn lps rule args margs hS hm4
    hebm hus hlps hrule hsa hsat hrP hplain hsm hsmt hcpm
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (iotaRecCmp_spec p hp.cmp n s₀ mode vis d us recP so rl mo)
  subst hs0
  refine ⟨hloc, ?_⟩
  simp only [irCmpW] at hW
  cases n with
  | zero => rw [callW_zero] at hW; cases hW
  | succ N =>
  have hk' : KnotUpTo p N := hk.mono (Nat.le_succ N)
  have hspn := hS.spn
  have herec := hS.erec
  obtain ⟨-, -, -, hcpw, hfpl, hfne, -, -, -⟩ := decRule_rd herec hrule
  generalize hE0 : s.mem.arr64 EREC = E at *
  -- the pins
  cases c1 : callW p (N + 1) "erec_push" [rdW E (rl + 6), rdW E (rl + 7), rdW E (rl + 3)] s.mem with
  | none => rw [c1] at hW; cases hW
  | some q =>
  obtain ⟨rp, m1⟩ := q
  rw [c1] at hW
  simp only at hW
  have P1 : MemFrame [SPN] [136] s.mem m1 ∧ StackGrew s.mem m1 ∧
      (rdW E (rl + 3) = 1 → rp.headD 0 = spTop s.mem ∧
        ∃ lv pins, rule.fire = .nested lv pins ∧ SpineR m1 (rp.headD 0) (rdW E (rl + 7)) pins.toArray ∧
          (rp.headD 0).toNat + (rdW E (rl + 7)).toNat ≤ (spTop m1).toNat) := by
    by_cases hk1 : rdW E (rl + 3) = 1
    · obtain ⟨lv, pins, hfire, hpins⟩ := hfne hk1
      rw [hk1] at c1
      obtain ⟨fr, gr, hr0, ht1, hsp⟩ := callW_erecPush p hp.erecPush (N + 1) s.mem _ _ pins
        (by rw [hE0]; exact herec) hspn (by rw [hE0]; exact hpins) rp m1 c1
      refine ⟨fr, gr, fun _ => ⟨hr0, lv, pins, hfire, by rw [hr0]; exact hsp, ?_⟩⟩
      have hb := hsp.bound
      have hsz := fr.2.2.1 SPN
      rw [hr0, ht1, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
      exact Nat.le_refl _
    · obtain ⟨-, rfl⟩ := callW_erecPush_no p hp.erecPush (N + 1) s.mem _ _ _ hk1 rp m1 c1
      exact ⟨MemFrame.refl _ _ _, (StackKept.refl _).toGrew, fun h => absurd h hk1⟩
  obtain ⟨fr1, gr1, hpush⟩ := P1
  have hS1 : CoreS dn m1 a₀ vis fe MM eb := hS.frame_stk fr1 (by simp) (by simp)
  have e1 : m1.arr64 EREC = E := by rw [← hE0]; exact fr1.1 EREC (by simp [SPN, EREC]) (by decide)
  rw [e1] at hW
  -- the comparands
  have hsa1 : SpineR m1 so sn args := hsa.keep gr1.2.1 gr1.2.2 hsat hspn
  have hrP1 := SpineR.take hsa1 (rdW E (recP + 6)) hrP
  generalize hargs' : (args.toList.take (rdW E (recP + 6)).toNat).toArray = args' at hrP1
  cases c2 : callW p (N + 1) "rec_fire_args" [rdW E (rl + 3), rp.headD 0, rdW E (rl + 7),
      rdW E (recP + 2), rdW E (recP + 3), us, so, rdW E (recP + 6), rdW E (rl + 2)] m1 with
  | none => rw [c2] at hW; cases hW
  | some q =>
  obtain ⟨ra, m2⟩ := q
  rw [c2] at hW
  simp only at hW
  have htop1 : (spTop s.mem).toNat ≤ (spTop m1).toNat := gr1.1
  obtain ⟨t2, ht2, -, ok2, ⟨M2, hS2, hK2, gr2⟩, xs, res2, hxs⟩ := triple_of_callW
    (recFireArgs_refines' p hp.toIotaProg' hc hw hEI (N + 1) ⟨m1, Locals.init []⟩ a₀ dn vis fe MM eb
      (rdW E (rl + 3)) (rp.headD 0) (rdW E (rl + 7)) (rdW E (recP + 2)) (rdW E (recP + 3)) us so
      (rdW E (recP + 6)) (rdW E (rl + 2)) rule lps args' hS1 hus (by rw [e1]; exact hlps) hrP1
      (fun h => let ⟨_, lv, pins, hf, hsp, _⟩ := hpush h; ⟨lv, pins, hf, hsp⟩)
      (fun h => ⟨hfpl h, by rw [← hcpw]; exact hplain (hfpl h)⟩) hcpw
      (by show so.toNat + (rdW E (recP + 6)).toNat ≤ (spTop m1).toNat; omega)
      (fun h => let ⟨_, _, _, _, _, hb⟩ := hpush h; hb)) c2
  rw [ht2] at hS2 gr2 hxs
  have e2 : m2.arr64 EREC = E := by
    rw [hER _ _ _ _ _ _ (by simp) c2, e1]
  -- the cover
  cases c3 : callW p (N + 1) "stack_cover" [ra.headD 0 + ra.tail.headD 0] m2 with
  | none => rw [c3] at hW; cases hW
  | some q =>
  obtain ⟨rx, m3⟩ := q
  rw [c3] at hW
  simp only at hW
  obtain ⟨fr3, gr3, hcov⟩ := callW_stackCover p hp.stackCover (N + 1) m2 _ rx m3 c3
  have hS3 : CoreS dn m3 _ vis fe M2 eb := hS2.frame_stk fr3 (by simp) (by simp)
  have e3 : m3.arr64 EREC = E := by rw [fr3.1 EREC (by simp) (by decide), e2]
  rw [e3] at hW
  have hxs3 : SpineR m3 (ra.headD 0) (ra.tail.headD 0) xs.toArray := SpineR.of_spn hxs
    (by rw [fr3.1 SPN (by simp) (by decide)])
  have hxb := hxs.bound
  have hsz2 : (m2.arr64 SPN).size = (s.mem.arr64 SPN).size := gr2.2.1.trans gr1.2.1
  have hxt : (ra.headD 0).toNat + (ra.tail.headD 0).toNat ≤ (spTop m3).toNat := by
    have h1 : (ra.headD 0 + ra.tail.headD 0).toNat = (ra.headD 0).toNat + (ra.tail.headD 0).toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have h2 := UInt64.le_iff_toNat_le.mp hcov
    omega
  -- the comparison
  have hgr13 : StackGrew s.mem m3 := gr1.trans (gr2.trans gr3)
  have hsm3 : SpineR m3 mo mn margs := hsm.keep hgr13.2.1 hgr13.2.2 hsmt hspn
  have hcpm' : (rdW E (rl + 2)).toNat ≤ mn.toNat := by rw [← hcpw]; exact hcpm
  have hmt3 : mo.toNat + mn.toNat ≤ (spTop m3).toNat := by
    have := UInt64.le_iff_toNat_le.mp hgr13.1; omega
  cases c4 : callW p (N + 1) "defeq_list" [mode, vis, d, mo, rdW E (rl + 2), ra.headD 0,
      ra.tail.headD 0] m3 with
  | none => rw [c4] at hW; cases hW
  | some q =>
  obtain ⟨rd, m4⟩ := q
  rw [c4] at hW
  simp only at hW
  obtain ⟨ok4, ⟨M4, hS4, hK4, hSt4⟩, res4, hr4⟩ := CoreSpec.of_callW
    (defeqList_refines p hp.toIotaProg' N hk' F (by omega) (by omega) ⟨m3, Locals.init []⟩ _ dn vis fe
      M2 eb mode d mo (rdW E (rl + 2)) (ra.headD 0) (ra.tail.headD 0)
      (margs.toList.take (rdW E (rl + 2)).toNat).toArray xs.toArray hS3 hm4 hebm
      (hsm3.take _ hcpm').toN hxs3.toN
      (fun _ => by show mo.toNat + (rdW E (rl + 2)).toNat ≤ (spTop m3).toNat; omega)
      (fun _ => hxt)) c4
  by_cases g136 : ¬ (136 : Word).toNat < (m4.arr64 CTL).size
  · rw [if_neg g136] at hW; cases hW
  rw [if_pos (Classical.not_not.mp g136)] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  -- the twin
  have hrunA := AM.run_of_ok _ _ ok2
  rw [res2] at hrunA
  have hrunD := AM.run_of_ok _ _ ok4
  rw [res4] at hrunD
  simp only [List.toList_toArray] at hrunD
  have hfa : recFireArgs rule lps (decI us) args'.toList (rdW E (recP + 6)).toNat =
      recFireArgs rule lps (decI us) args.toList (rdW E (recP + 6)).toNat := by
    rw [← hargs', List.toList_toArray]
    exact recFireArgs_take _ _ _ _ _ hplain
  rw [hfa] at hrunA hrunD hS4
  have hrunF : (iotaRecCmpT (coreKnot (decMode mode) fe id F) fe d.toNat rule lps (decI us)
      args.toList (rdW E (recP + 6)).toNat margs.toList).run a₀ =
      .ok (decBool rd, AM.st (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat
        (margs.toList.take (rdW E (rl + 2)).toNat) xs)
        (AM.st (recFireArgs rule lps (decI us) args.toList (rdW E (recP + 6)).toNat) a₀)) := by
    simp only [iotaRecCmpT, StateT.run_bind, hrunA, except_ok_bind]
    rw [hcpw]
    exact hrunD
  obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrunF
  have hgr14 : StackGrew s.mem m4 := hgr13.trans hSt4.toGrew
  refine ⟨hokF, ⟨M4, ?_, hK2.trans hK4, ?_⟩, ?_, ?_⟩
  · rw [hstF, ← hm]; exact hS4.frame_stk (MemFrame.setCtl m4 136 _) (by simp) (by simp)
  · rw [← hm]; exact StackKept.restore hgr14.2.2 hgr14.2.1 (Classical.not_not.mp g136)
  · rw [hresF]; simp only [decBool, hr]
  · unfold ResH; rw [← hr]; exact hr4

end L.Arena
