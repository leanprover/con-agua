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

set_option maxRecDepth 8192 in
/-- `ErecKeptRec` from the core's write set (`CoreErec.lean`). -/
theorem ErecKeptRec.of_closed {p : Prog} (hcl : closedA p coreErecA coreErecC coreFns = true) :
    ErecKeptRec p :=
  fun _ _ _ _ _ _ hf h => callW_erec_closed hcl (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) h

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
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, fun s₀ => Triple.step_exec (erecPushLoop_spec p (k + 1) s₀)] <;>
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
      rw [hgr4.size, hsz3]
    refine SpineR.cons_slot m' (so + j) (c - (j + 1)) w _ hw32 ?_ hys ?_ (by rw [hsize']; exact hspn)
    · have := hgr4.below (so + j) (by rw [hsp3, UInt64.lt_iff_toNat_lt, hsjp1]; omega)
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
  obtain ⟨h136, hW⟩ := of_ite_none' hW
  obtain ⟨hg1, hW⟩ := of_ite_none hW
  obtain ⟨hg2, hW⟩ := of_ite_none hW
  cases hm : epW o c (rdW (m.arr64 CTL) 136) (n + 1) m 0 with
  | none => rw [hm] at hW; cases hW
  | some m₁ =>
  rw [hm] at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
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
      refine ⟨MemFrame.setCtl m 136 x, ⟨?_, by rw [hspn], fun i _ => by simp only [spW, hspn],
          BKept.of_frame (MemFrame.setCtl m 136 x) (by decide) (by decide),
          PoolGrew.of_frame (MemFrame.setCtl m 136 x) (by decide) (by decide)⟩,
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
      us, so, rdW (m1.arr64 EREC) (recP + 5) + 1, rdW (m1.arr64 EREC) (recP + 6),
      rdW (m1.arr64 EREC) (rl + 2)] m1 with
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
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    SpineR s₀.mem mo mn margs → mo.toNat + mn.toNat ≤ (spTop s₀.mem).toNat →
    rule.ctorParams ≤ mn.toNat →
    CoreSpec p (n + 1) "iota_rec_cmp" [mode, vis, d, us, recP, so, rl, mo]
      (iotaRecCmpT (coreKnot (decMode mode) fe id F) fe d.toNat rule lps (decI us) args.toList
        (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat margs.toList) decBool s₀ a₀ dn vis fe MM eb := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d us recP so rl mo mn sn lps rule args margs hS hm4
    hebm hus hlps hrule hsa hsat hmI hsm hsmt hcpm
  refine triple_post (iotaRecCmp_spec p hp.cmp n s₀ mode vis d us recP so rl mo) fun r s' ⟨hloc,
    hW⟩ => ⟨hloc, ?_⟩
  simp only [irCmpW] at hW
  cases n with
  | zero => rw [callW_zero] at hW; cases hW
  | succ N =>
  have hk' : KnotUpTo p N := hk.mono (Nat.le_succ N)
  have hspn := hS.spn
  have herec := hS.erec
  obtain ⟨-, -, -, hcpw, hfpl, hfne, -, -, -⟩ := decRule_rd herec hrule
  generalize hE0 : s₀.mem.arr64 EREC = E at *
  -- the pins
  rcases c1 : callW p (N + 1) "erec_push" [rdW E (rl + 6), rdW E (rl + 7), rdW E (rl + 3)] s₀.mem with _ | ⟨rp, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  have P1 : MemFrame [SPN] [136] s₀.mem m1 ∧ StackGrew s₀.mem m1 ∧
      (rdW E (rl + 3) = 1 → rp.headD 0 = spTop s₀.mem ∧
        ∃ lv pins, rule.fire = .nested lv pins ∧ SpineR m1 (rp.headD 0) (rdW E (rl + 7)) pins.toArray ∧
          (rp.headD 0).toNat + (rdW E (rl + 7)).toNat ≤ (spTop m1).toNat) := by
    by_cases hk1 : rdW E (rl + 3) = 1
    · obtain ⟨lv, pins, hfire, hpins⟩ := hfne hk1
      rw [hk1] at c1
      obtain ⟨fr, gr, hr0, ht1, hsp⟩ := callW_erecPush p hp.erecPush (N + 1) s₀.mem _ _ pins
        (by rw [hE0]; exact herec) hspn (by rw [hE0]; exact hpins) rp m1 c1
      refine ⟨fr, gr, fun _ => ⟨hr0, lv, pins, hfire, by rw [hr0]; exact hsp, ?_⟩⟩
      have hb := hsp.bound
      have hsz := fr.2.2.1 SPN
      rw [hr0, ht1, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
      exact Nat.le_refl _
    · obtain ⟨-, rfl⟩ := callW_erecPush_no p hp.erecPush (N + 1) s₀.mem _ _ _ hk1 rp m1 c1
      exact ⟨MemFrame.refl _ _ _, (StackKept.refl _).toGrew, fun h => absurd h hk1⟩
  obtain ⟨fr1, gr1, hpush⟩ := P1
  have hS1 : CoreS dn m1 a₀ vis fe MM eb := hS.frame_stk fr1 (by simp) (by simp)
  have e1 : m1.arr64 EREC = E := by rw [← hE0]; exact fr1.1 EREC (by simp [SPN, EREC]) (by decide)
  rw [e1] at hW
  -- the comparands
  have hsa1 : SpineR m1 so sn args := hsa.keep gr1.size gr1.below hsat hspn
  have hsn : rdW E (recP + 5) + 1 = sn := by
    apply UInt64.toNat_inj.mp
    have := sn.toNat_lt
    rw [UInt64.toNat_add]; simp; omega
  rcases c2 : callW p (N + 1) "rec_fire_args" [rdW E (rl + 3), rp.headD 0, rdW E (rl + 7),
      rdW E (recP + 2), rdW E (recP + 3), us, so, rdW E (recP + 5) + 1, rdW E (recP + 6),
      rdW E (rl + 2)] m1 with _ | ⟨ra, m2⟩ <;> simp only [c2, reduceCtorEq] at hW
  have htop1 : (spTop s₀.mem).toNat ≤ (spTop m1).toNat := gr1.1
  obtain ⟨t2, ht2, -, ok2, ⟨M2, hS2, hK2, gr2⟩, xs, res2, hxs⟩ := triple_of_callW
    (recFireArgs_refines' p hp.toIotaProg' hc hw hEI (N + 1) ⟨m1, Locals.init []⟩ a₀ dn vis fe MM eb
      (rdW E (rl + 3)) (rp.headD 0) (rdW E (rl + 7)) (rdW E (recP + 2)) (rdW E (recP + 3)) us so
      (rdW E (recP + 5) + 1) (rdW E (recP + 6)) (rdW E (rl + 2)) rule lps args hS1 hus
      (by rw [e1]; exact hlps) (by rw [hsn]; exact hsa1)
      (fun h => let ⟨_, lv, pins, hf, hsp, _⟩ := hpush h; ⟨lv, pins, hf, hsp⟩)
      hfpl hcpw
      (by rw [hsn]; show so.toNat + sn.toNat ≤ (spTop m1).toNat; omega)
      (fun h => let ⟨_, _, _, _, _, hb⟩ := hpush h; hb)) c2
  rw [ht2] at hS2 gr2 hxs
  have e2 : m2.arr64 EREC = E := by
    rw [hER _ _ _ _ _ _ (by simp) c2, e1]
  -- the cover
  rcases c3 : callW p (N + 1) "stack_cover" [ra.headD 0 + ra.tail.headD 0] m2 with _ | ⟨rx, m3⟩ <;>
    simp only [c3, reduceCtorEq] at hW
  obtain ⟨fr3, gr3, hcov⟩ := callW_stackCover p hp.stackCover (N + 1) m2 _ rx m3 c3
  have hS3 : CoreS dn m3 _ vis fe M2 eb := hS2.frame_stk fr3 (by simp) (by simp)
  have e3 : m3.arr64 EREC = E := by rw [fr3.1 EREC (by simp) (by decide), e2]
  rw [e3] at hW
  have hxs3 : SpineR m3 (ra.headD 0) (ra.tail.headD 0) xs.toArray := SpineR.of_spn_core hxs
    (by rw [fr3.1 SPN (by simp) (by decide)])
  have hxb := hxs.bound
  have hsz2 : (m2.arr64 SPN).size = (s₀.mem.arr64 SPN).size := gr2.size.trans gr1.size
  have hxt : (ra.headD 0).toNat + (ra.tail.headD 0).toNat ≤ (spTop m3).toNat := by
    have h1 : (ra.headD 0 + ra.tail.headD 0).toNat = (ra.headD 0).toNat + (ra.tail.headD 0).toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have h2 := UInt64.le_iff_toNat_le.mp hcov
    omega
  -- the comparison
  have hgr13 : StackGrew s₀.mem m3 := gr1.trans (gr2.trans gr3)
  have hsm3 : SpineR m3 mo mn margs := hsm.keep hgr13.size hgr13.below hsmt hspn
  have hcpm' : (rdW E (rl + 2)).toNat ≤ mn.toNat := by rw [← hcpw]; exact hcpm
  have hmt3 : mo.toNat + mn.toNat ≤ (spTop m3).toNat := by
    have := UInt64.le_iff_toNat_le.mp hgr13.1; omega
  rcases c4 : callW p (N + 1) "defeq_list" [mode, vis, d, mo, rdW E (rl + 2), ra.headD 0,
      ra.tail.headD 0] m3 with _ | ⟨rd, m4⟩ <;> simp only [c4, reduceCtorEq] at hW
  obtain ⟨hrunD, ⟨M4, hS4, hK4, hSt4⟩, hr4⟩ := CoreSpec.run
    (defeqList_refines p hp.toIotaProg' N hk' F (by omega) (by omega) ⟨m3, Locals.init []⟩ _ dn vis fe
      M2 eb mode d mo (rdW E (rl + 2)) (ra.headD 0) (ra.tail.headD 0)
      (margs.toList.take (rdW E (rl + 2)).toNat).toArray xs.toArray hS3 hm4 hebm
      (hsm3.take _ hcpm').toN hxs3.toN
      (fun _ => by show mo.toNat + (rdW E (rl + 2)).toNat ≤ (spTop m3).toNat; omega)
      (fun _ => hxt)) c4
  by_cases g136 : ¬ (136 : Word).toNat < (m4.arr64 CTL).size
  · rw [if_neg g136] at hW; cases hW
  rw [if_pos (Classical.not_not.mp g136)] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  -- the twin
  have hrunA := AM.run_of_ok _ _ ok2
  rw [res2] at hrunA
  simp only [List.toList_toArray] at hrunD
  have hrunF : (iotaRecCmpT (coreKnot (decMode mode) fe id F) fe d.toNat rule lps (decI us)
      args.toList (rdW E (recP + 6)).toNat margs.toList).run a₀ =
      .ok (decBool rd, AM.st (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat
        (margs.toList.take (rdW E (rl + 2)).toNat) xs)
        (AM.st (recFireArgs rule lps (decI us) args.toList (rdW E (recP + 6)).toNat) a₀)) := by
    simp only [iotaRecCmpT, StateT.run_bind, hrunA, except_ok_bind]
    rw [hcpw]
    exact hrunD
  obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrunF
  have hgr14 : StackGrew s₀.mem m4 := hgr13.trans hSt4.toGrew
  refine ⟨hokF, ⟨M4, ?_, hK2.trans hK4, ?_⟩, ?_, ?_⟩
  · rw [hstF, ← hm]; exact hS4.frame_stk (MemFrame.setCtl m4 136 _) (by simp) (by simp)
  · rw [← hm]; exact StackKept.restoreG hgr14 (Classical.not_not.mp g136)
  · rw [hresF]; simp only [decBool, hr]
  · unfold ResH; rw [← hr]; exact hr4

/-! ## `iota_rec_vck(mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn, cmpL)` -/

/-- The index slice's length word of `iota_rec_vck`. -/
def ixLen (mI rP : Word) : Word := (mI - rP) * Cmp.ule.evalW rP mI

/-- Model of `iota_rec_vck`, after the certificate check. -/
def irVckTail (p : Prog) (n : Nat) (m : Mem) (mode vis d recP so rl mo mn tyC : Word) :
    Option (Word × Mem) :=
  match callW p n "iota_certs_full" [mode, vis, d, tyC, mo, mn] m with
  | none => none
  | some (rf, m4) =>
  if rf.headD 0 = 0 then some (0, m4) else
  match callW p n "iota_index_ok" [mode, vis, d, rdW (m4.arr64 EREC) (recP + 5),
      rdW (m4.arr64 EREC) (recP + 6), rdW (m4.arr64 EREC) (rl + 2), tyC, mo, mn,
      so + (rdW (m4.arr64 EREC) (recP + 6) -
        ixLen (rdW (m4.arr64 EREC) (recP + 6)) (rdW (m4.arr64 EREC) (recP + 5))),
      ixLen (rdW (m4.arr64 EREC) (recP + 5)) (rdW (m4.arr64 EREC) (recP + 6))] m4 with
  | none => none
  | some (ri, m5) => some (ri.headD 0, m5)

/-- Model of `iota_rec_vck`. -/
def irVckW (p : Prog) (n : Nat) (m : Mem) (mode vis d us recP so usj ctorP rl mo mn cmpL : Word) :
    Option (Word × Mem) :=
  match callW p n "lvls_eq_c" [usj, cmpL] m with
  | none => none
  | some (rq, m1) =>
  if rq.headD 0 = 0 then none else
  if rq.headD 0 = 1 then some (0, m1) else
  match callW p n "iota_rec_cmp" [mode, vis, d, us, recP, so, rl, mo] m1 with
  | none => none
  | some (rc, m2) =>
  if rc.headD 0 = 0 then some (0, m2) else
  match callW p n "const_ty_at" [rdW (m2.arr64 EREC) (ctorP + 1), rdW (m2.arr64 EREC) (ctorP + 2),
      rdW (m2.arr64 EREC) (ctorP + 3), rdW (m2.arr64 EREC) (ctorP + 4), usj] m2 with
  | none => none
  | some (rt, m3) => irVckTail p n m3 mode vis d recP so rl mo mn (rt.headD 0)

theorem iotaRecVck_spec (p : Prog) (hp : p.lookup "iota_rec_vck" = some iotaRecVckL) (n : Nat)
    (s₀ : St) (mode vis d us recP so usj ctorP rl mo mn cmpL : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_rec_vck" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn, cmpL]
    ⦃fun r s' => LocEq s' s₀ ∧
      irVckW p n s₀.mem mode vis d us recP so usj ctorP rl mo mn cmpL = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaRecVckL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "lvls_eq_c", callW_spec p n "iota_rec_cmp", callW_spec p n "const_ty_at",
    callW_spec p n "iota_certs_full", callW_spec p n "iota_index_ok"] <;>
  simp_all [-UInt64.toNat_add, irVckW, irVckTail, ixLen, EREC, CTL, BinOp.eval, getElem_rdW',
    Cmp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]

/-- `lvls_eq_c` cannot run on fuel below two. -/
theorem lvlsEqC_small (p : Prog) (hp : p.lookup "lvls_eq_c" = some lvlsEqCL) (n : Nat) (hn : n < 2)
    (vs : List Word) (m : Mem) : callW p n "lvls_eq_c" vs m = none := by
  rcases Nat.lt_or_ge n 1 with h0 | h1
  · have : n = 0 := by omega
    subst this; exact callW_zero _ _ _ _
  · have : n = 1 := by omega
    subst this
    cases hc : callW p 1 "lvls_eq_c" vs m with
    | none => rfl
    | some q =>
      exfalso
      obtain ⟨t, -, hF⟩ := triple_of_callW (p := p) (n := 1) (f := "lvls_eq_c") (args := vs)
        (s₀ := ⟨m, Locals.init []⟩) (Q := fun _ _ => False) (by
          rw [invoke_eq _ hp]
          simp only [callFn, lvlsEqCL]
          vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
            callW_spec p 0 "lsq_find", callW_spec p 0 "lvls_eq_rec"] <;>
          simp_all [callW_zero]) hc
      exact hF

/-- A slice `[a, b)` of a spine slice. -/
theorem SpineR.slice {m : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (a b : Word) (ha : a.toNat ≤ cnt.toNat) (hb : b.toNat ≤ cnt.toNat)
    (hspn : (m.arr64 SPN).size < 2 ^ 63) :
    SpineR m (off + a) (UInt64.ofNat (b.toNat - a.toNat))
      ((xs.toList.take b.toNat).drop a.toNat).toArray := by
  have hbd := h.bound
  have hsz := h.size
  have hoa : (off + a).toNat = off.toNat + a.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hl : (UInt64.ofNat (b.toNat - a.toNat)).toNat = b.toNat - a.toNat := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hidx : ∀ i : Nat, i < b.toNat - a.toNat →
      off + a + i.toUInt64 = off + (a.toNat + i).toUInt64 := by
    intro i hi
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, Nat.toUInt64, UInt64.toNat_ofNat', Nat.reducePow]
    omega
  refine ⟨?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · simp [hl, hsz]; omega
  · rw [hoa, hl]; omega
  · rw [hl] at hi
    rw [hidx i hi]
    exact h.lt _ (by omega)
  · have hi' : i < b.toNat - a.toNat := by simp [hsz] at hi; omega
    rw [hidx i hi']
    have := h.get (a.toNat + i) (by rw [hsz]; omega)
    rw [← this]
    simp [List.getElem_drop, List.getElem_take]

theorem ixLen_eq (mI rP : Word) : ixLen mI rP = UInt64.ofNat (mI.toNat - rP.toNat) := by
  unfold ixLen Cmp.evalW
  by_cases h : rP ≤ mI
  · have : Cmp.ule.eval rP mI = true := by simp [Cmp.eval, h]
    rw [if_pos this, UInt64.mul_one]
    apply UInt64.toNat_inj.mp
    have := mI.toNat_lt
    rw [UInt64.toNat_sub_of_le _ _ h, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  · have : Cmp.ule.eval rP mI = false := by simp [Cmp.eval, h]
    rw [if_neg (by simp [this]), UInt64.mul_zero]
    have : mI.toNat - rP.toNat = 0 := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h); omega
    rw [this]; rfl

/-- The index slice's offset: `so + min rP mI`. -/
theorem ixOff_toNat (mI rP : Word) : (rP - ixLen rP mI).toNat = min rP.toNat mI.toNat := by
  have hl : (ixLen rP mI).toNat = rP.toNat - mI.toNat := by
    rw [ixLen_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by have := rP.toNat_lt; omega)]
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hl]; omega), hl]
  omega

theorem take_drop_min_le (xs : List EIdx) (a b : Nat) :
    (xs.take b).drop (min a b) = (xs.take b).drop a := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.drop_eq_nil_of_le (by simp; omega),
      List.drop_eq_nil_of_le (by simp; omega)]

section vckRun
variable (r : CoreFnsA) (fe : IFEnv) (depth mI rP : Nat) (lps : List NIdx) (us : LsIdx)
  (args : List EIdx) (usj : LsIdx) (cvj : IConstantVal) (rl : IRecRule) (margs : List EIdx)
  (cmpL : LsIdx)

theorem liftFueled_run_some {α : Type} (w : String) (x : α) (a : AState) :
    (liftFueled w (some x)).run a = .ok (x, a) := by
  simp [liftFueled]; rfl

theorem vckT_run_lvl (a a1 : AState) (h1 : (lvlsEq? usj cmpL).run a = .ok (some false, a1)) :
    (iotaRecVckT r fe depth mI rP lps us args usj cvj rl margs cmpL).run a = .ok (false, a1) := by
  rw [iotaRecVckT_eq]
  simp only [StateT.run_bind, h1, except_ok_bind, liftFueled_run_some, Bool.false_eq_true,
    ↓reduceIte]
  rfl

theorem vckT_run_cmp (a a1 a2 : AState) (h1 : (lvlsEq? usj cmpL).run a = .ok (some true, a1))
    (h2 : (iotaRecCmpT r fe depth rl lps us args rP margs).run a1 = .ok (false, a2)) :
    (iotaRecVckT r fe depth mI rP lps us args usj cvj rl margs cmpL).run a = .ok (false, a2) := by
  rw [iotaRecVckT_eq]
  simp only [StateT.run_bind, h1, except_ok_bind, liftFueled_run_some, ↓reduceIte, h2,
    Bool.false_eq_true]
  rfl

theorem vckT_run_cert (a a1 a2 a3 a4 : AState) (tyC : EIdx)
    (h1 : (lvlsEq? usj cmpL).run a = .ok (some true, a1))
    (h2 : (iotaRecCmpT r fe depth rl lps us args rP margs).run a1 = .ok (true, a2))
    (h3 : (constTyAt cvj usj).run a2 = .ok (tyC, a3))
    (h4 : (iotaCertsFull r fe depth tyC margs).run a3 = .ok (false, a4)) :
    (iotaRecVckT r fe depth mI rP lps us args usj cvj rl margs cmpL).run a = .ok (false, a4) := by
  rw [iotaRecVckT_eq]
  simp only [StateT.run_bind, h1, except_ok_bind, liftFueled_run_some, ↓reduceIte, h2, h3, h4,
    Bool.false_eq_true]
  rfl

theorem vckT_run_idx (a a1 a2 a3 a4 a5 : AState) (tyC : EIdx) (b : Bool)
    (h1 : (lvlsEq? usj cmpL).run a = .ok (some true, a1))
    (h2 : (iotaRecCmpT r fe depth rl lps us args rP margs).run a1 = .ok (true, a2))
    (h3 : (constTyAt cvj usj).run a2 = .ok (tyC, a3))
    (h4 : (iotaCertsFull r fe depth tyC margs).run a3 = .ok (true, a4))
    (h5 : (iotaIndexOk r fe depth mI rP rl.ctorParams tyC margs ((args.take mI).drop rP)).run a4 =
      .ok (b, a5)) :
    (iotaRecVckT r fe depth mI rP lps us args usj cvj rl margs cmpL).run a = .ok (b, a5) := by
  rw [iotaRecVckT_eq]
  simp only [StateT.run_bind, h1, except_ok_bind, liftFueled_run_some, ↓reduceIte, h2, h3, h4,
    h5]

end vckRun

/-! ### The record pool across `iota_rec_cmp` -/

theorem epW_frame (o c so : Word) : ∀ (k : Nat) (m : Mem) (j : Word) (m' : Mem),
    epW o c so k m j = some m' → MemFrame [SPN] [136] m m' := by
  intro k
  induction k with
  | zero => intro m j m' h; simp [epW] at h
  | succ k ih =>
    intro m j m' h
    by_cases hj : j < c
    · by_cases h1 : (o + j).toNat < (m.arr64 EREC).size
      · by_cases h2 : (so + j).toNat < (m.arr64 SPN).size ∧ (136 : Word).toNat < (m.arr64 CTL).size
        · rw [epW_cont o c so k m j hj h1 h2] at h
          have f1 : MemFrame [SPN] [136] m (m.set64 SPN (so + j) (m.arr64 EREC)[(o + j).toNat]) :=
            (MemFrame.set64 m SPN (by decide) _ _).mono (fun b hb => hb) (fun x hx => by simp at hx)
          have f2 := (MemFrame.setCtl (m.set64 SPN (so + j) (m.arr64 EREC)[(o + j).toNat]) 136
            (so + j + 1)).mono (A' := [SPN]) (fun b hb => by simp at hb) (fun x hx => hx)
          exact (f1.trans f2).trans (ih _ _ _ h)
        · rw [epW_bad2 o c so k m j hj h1 h2] at h; cases h
      · rw [epW_bad1 o c so k m j hj h1] at h; cases h
    · rw [epW_end o c so k m j hj] at h; cases h; exact MemFrame.refl _ _ _

theorem callW_erecPush_frame (p : Prog) (hp : p.lookup "erec_push" = some erecPushL) (n : Nat)
    (m : Mem) (o c kd : Word) (r : List Word) (m' : Mem)
    (h : callW p n "erec_push" [o, c, kd] m = some (r, m')) : MemFrame [SPN] [136] m m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (erecPush_spec p hp n ⟨m, Locals.init []⟩ o c kd) h
  rw [ht] at hW
  simp only [epTop] at hW
  by_cases hk : kd ≠ 1
  · rw [if_pos hk] at hW; cases hW; exact MemFrame.refl _ _ _
  rw [if_neg hk] at hW
  split at hW
  · split at hW
    · cases hW
    split at hW
    · cases hW
    split at hW
    · cases hW
    · rename_i hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      rw [← hW.2]; exact epW_frame _ _ _ _ _ _ _ hm
  · cases hW

/-- **`iota_rec_cmp` leaves the record pool alone.** -/
theorem callW_iotaRecCmp_erec (p : Prog) (hp : IotaRecProg' p) (hER : ErecKeptRec p)
    (hEK : ErecKeptKnot p) (n : Nat) (m : Mem) (vs : List Word) (r : List Word) (m' : Mem)
    (hvs : vs.length = 8) (h : callW p n "iota_rec_cmp" vs m = some (r, m')) :
    m'.arr64 EREC = m.arr64 EREC := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  match vs, hvs with
  | [mode, vis, d, us, recP, so, rl, mo], _ =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW
    (iotaRecCmp_spec p hp.cmp n ⟨m, Locals.init []⟩ mode vis d us recP so rl mo) h
  rw [ht] at hW
  simp only [irCmpW] at hW
  split at hW
  · cases hW
  rename_i rp m1 c1
  split at hW
  · cases hW
  rename_i ra m2 c2
  split at hW
  · cases hW
  rename_i rx m3 c3
  split at hW
  · cases hW
  rename_i rd m4 c4
  split at hW
  · simp only [Option.some.injEq, Prod.mk.injEq] at hW
    rw [← hW.2, Mem.arr64_set64_ne _ _ _ _ _ (by decide), hEK _ _ _ _ _ _ (by simp) c4,
      (callW_stackCover p hp.stackCover n m2 _ rx m3 c3).1.1 EREC (by simp) (by decide),
      hER _ _ _ _ _ _ (by simp) c2,
      (callW_erecPush_frame p hp.erecPush n m _ _ _ rp m1 c1).1 EREC (by simp [SPN, EREC]) (by decide)]
  · cases hW

/-- **`iota_rec_vck` refines the checks past `iotaCase3`.** -/
theorem iotaRecVck_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d us recP so usj ctorP rl mo mn cmpL sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (args margs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW us → HW usj →
    HW cmpL →
    hslice? (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps →
    decRule (s₀.mem.arr64 EREC) rl.toNat = some rule →
    decCV (s₀.mem.arr64 EREC) (ctorP.toNat + 1) = some cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    SpineR s₀.mem mo mn margs → mo + mn = spTop s₀.mem → rule.ctorParams ≤ mn.toNat →
    CoreSpec p (n + 1) "iota_rec_vck" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn, cmpL]
      (iotaRecVckT (coreKnot (decMode mode) fe id F) fe d.toNat
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
        (decI us) args.toList (decI usj) cvj rule margs.toList (decI cmpL)) decBool s₀ a₀ dn vis fe
      MM eb := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d us recP so usj ctorP rl mo mn cmpL sn lps rule
    cvj args margs hS hm4 hebm hus husj hcmpL hlps hrule hcv hsa hsat hmI hsm hsmt hcpm
  refine triple_post (iotaRecVck_spec p hp.vck n s₀ mode vis d us recP so usj ctorP rl mo mn cmpL)
    fun r s' ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  simp only [irVckW] at hW
  have hspn := hS.spn
  have herec := hS.erec
  obtain ⟨-, -, -, hcpw, -, -, -, -, -⟩ := decRule_rd herec hrule
  obtain ⟨hnn, hname, hlpsj, -, hty, htype⟩ := decCV_rd1 herec hcv
  generalize hE0 : s₀.mem.arr64 EREC = E at *
  have hmsz : (mo + mn).toNat = mo.toNat + mn.toNat := by
    have := hsm.bound; rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  -- the levels
  rcases c1 : callW p n "lvls_eq_c" [usj, cmpL] s₀.mem with _ | ⟨rq, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · rw [lvlsEqC_small p hp.lvl.cs n h] at c1; cases c1
    · exact h
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, hr1⟩ := CoreSpec.run
    (lvlsEqC_refines p hp.lvl N ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb hS usj cmpL husj
      hcmpL) c1
  have e1 : m1.arr64 EREC = E := by rw [hER _ _ _ _ _ _ (by simp) c1, hE0]
  obtain ⟨q0, hW⟩ := of_ite_none hW
  by_cases q1 : rq.headD 0 = 1
  · rw [if_pos q1] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    have hdo : decO (rq.headD 0) = some false := by rw [q1]; rfl
    rw [hdo] at hrun1
    refine CoreRef.of_run (vckT_run_lvl (coreKnot (decMode mode) fe id F) fe d.toNat _ _ lps (decI
      us) args.toList (decI usj) cvj rule margs.toList (decI cmpL) a₀ _ hrun1) (hm ▸ ⟨M1, hS1, hK1,
      hSt1⟩) ?_ ?_
    · simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg q1] at hW
  have hdo : decO (rq.headD 0) = some true := by unfold decO; rw [if_neg q0, if_neg q1]
  rw [hdo] at hrun1
  -- the parameters
  have hsa1 : SpineR m1 so sn args := hsa.keep hSt1.size hSt1.below hsat hspn
  have hsm1 : SpineR m1 mo mn margs := hsm.keep hSt1.size hSt1.below (by rw [← hsmt]; omega) hspn
  rcases c2 : callW p (N + 2) "iota_rec_cmp" [mode, vis, d, us, recP, so, rl, mo] m1 with _ | ⟨rc, m2⟩ <;>
    simp only [c2, reduceCtorEq] at hW
  have hcmp := iotaRecCmp_refines' p hp hc hw hEI hER (N + 1) (hk.mono (by omega)) F (by omega)
    (by omega) ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d us recP so rl mo mn sn lps rule args
    margs hS1 hm4 hebm hus
  simp only [e1] at hcmp
  obtain ⟨hrun2, ⟨M2, hS2, hK2, hSt2⟩, hr2⟩ := CoreSpec.run (hcmp hlps hrule hsa1
    (by rw [hSt1.1]; exact hsat) hmI hsm1 (by rw [hSt1.1, ← hsmt]; omega) hcpm) c2
  have e2 : m2.arr64 EREC = E := by
    rw [callW_iotaRecCmp_erec p hp hER hEK _ _ _ _ _ rfl c2, e1]
  have hSt12 := hSt1.trans hSt2
  by_cases g0 : rc.headD 0 = 0
  · rw [if_pos g0] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [decBool_f_m2c g0] at hrun2
    refine CoreRef.of_run (vckT_run_cmp (coreKnot (decMode mode) fe id F) fe d.toNat _ _ lps (decI us)
      args.toList (decI usj) cvj rule margs.toList (decI cmpL) a₀ _ _ hrun1 hrun2)
      (hm ▸ ⟨M2, hS2, hK1.trans hK2, hSt12⟩) ?_ ?_
    · simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg g0] at hW
  have hb : decBool rc = true := by unfold decBool; exact bne_iff_ne.mpr g0
  rw [hb] at hrun2
  -- the constructor's type
  rw [e2] at hW
  rcases c3 : callW p (N + 2) "const_ty_at" [rdW E (ctorP + 1), rdW E (ctorP + 2), rdW E (ctorP + 3),
      rdW E (ctorP + 4), usj] m2 with _ | ⟨rt, m3⟩ <;> simp only [c3, reduceCtorEq] at hW
  obtain ⟨ok3, ⟨M3, hS3, hK3, hSt3⟩, res3, hr3⟩ := CoreSpec.of_callW
    (constTyAt_refines' p hp.toIotaProg' hw.instLP (N + 2) ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb
      (rdW E (ctorP + 1)) (rdW E (ctorP + 2)) (rdW E (ctorP + 3)) (rdW E (ctorP + 4)) usj
      cvj.levelParams hS2 hnn hty husj (by rw [e2]; exact hlpsj)) c3
  have hcvj : (⟨decI (rdW E (ctorP + 1)), cvj.levelParams, decE (rdW E (ctorP + 4))⟩ : IConstantVal) =
      cvj := by
    cases cvj; simp only at hname htype ⊢; rw [hname, htype]; rfl
  rw [hcvj] at ok3 res3 hS3
  have hrun3 := AM.run_of_ok _ _ ok3
  rw [res3] at hrun3
  have e3 : m3.arr64 EREC = E := by rw [hER _ _ _ _ _ _ (by simp) c3, e2]
  have hSt13 := hSt12.trans hSt3
  -- the telescope
  simp only [irVckTail] at hW
  have hsm3 : SpineR m3 mo mn margs := hsm.keep hSt13.size hSt13.below (by rw [← hsmt]; omega) hspn
  rcases c4 : callW p (N + 2) "iota_certs_full" [mode, vis, d, rt.headD 0, mo, mn] m3 with _ | ⟨rf, m4⟩ <;>
    simp only [c4, reduceCtorEq] at hW
  obtain ⟨hrun4, ⟨M4, hS4, hK4, hSt4⟩, hr4⟩ := CoreSpec.run
    (iotaCertsFull_refines' p hp.toIotaProg4 hw.instList (N + 1) (hk.mono (by omega)) F (by omega) (by omega)
      ⟨m3, Locals.init []⟩ _ dn vis fe M3 eb mode d (rt.headD 0) mo mn margs hS3 hm4 hebm hr3 hsm3
      (by rw [hSt13.1]; exact hsmt)) c4
  have e4 : m4.arr64 EREC = E := by rw [hER _ _ _ _ _ _ (by simp) c4, e3]
  have hSt14 := hSt13.trans hSt4
  by_cases f0 : rf.headD 0 = 0
  · rw [if_pos f0] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [decBool_f_m2c f0] at hrun4
    refine CoreRef.of_run (vckT_run_cert (coreKnot (decMode mode) fe id F) fe d.toNat _ _ lps (decI
      us) args.toList (decI usj) cvj rule margs.toList (decI cmpL) a₀ _ _ _ _ _ hrun1 hrun2 hrun3
      hrun4) (hm ▸ ⟨M4, hS4, hK1.trans (hK2.trans (hK3.trans hK4)), hSt14⟩) ?_ ?_
    · simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg f0] at hW
  rw [decBool_t_m2c f0] at hrun4
  -- the indices
  rw [e4] at hW
  have hsa4 : SpineR m4 so sn args := hsa.keep hSt14.size hSt14.below hsat hspn
  have hsm4 : SpineR m4 mo mn margs := hsm.keep hSt14.size hSt14.below (by rw [← hsmt]; omega) hspn
  have hmIs : (rdW E (recP + 5)).toNat ≤ sn.toNat := by omega
  have hoff := ixOff_toNat (rdW E (recP + 5)) (rdW E (recP + 6))
  have hidx := SpineR.slice hsa4 (rdW E (recP + 6) - ixLen (rdW E (recP + 6)) (rdW E (recP + 5)))
    (rdW E (recP + 5)) (by rw [hoff]; omega) hmIs (by rw [hSt14.size]; exact hspn)
  have hl : UInt64.ofNat ((rdW E (recP + 5)).toNat -
      (rdW E (recP + 6) - ixLen (rdW E (recP + 6)) (rdW E (recP + 5))).toNat) =
      ixLen (rdW E (recP + 5)) (rdW E (recP + 6)) := by
    rw [hoff, ixLen_eq]; congr 1; omega
  rw [hl, hoff, take_drop_min_le] at hidx
  have hsat' := hsa.bound
  have hxo : (so + (rdW E (recP + 6) - ixLen (rdW E (recP + 6)) (rdW E (recP + 5)))).toNat +
      (ixLen (rdW E (recP + 5)) (rdW E (recP + 6))).toNat ≤ (spTop m4).toNat := by
    have htq : (spTop ({ mem := s₀.mem, loc := Locals.init [] } : St).mem).toNat =
        (spTop s₀.mem).toNat := rfl
    rw [hSt14.1, UInt64.toNat_add, hoff, Nat.mod_eq_of_lt (by omega), ixLen_eq, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega)]
    omega
  rcases c5 : callW p (N + 2) "iota_index_ok" [mode, vis, d, rdW E (recP + 5), rdW E (recP + 6),
      rdW E (rl + 2), rt.headD 0, mo, mn,
      so + (rdW E (recP + 6) - ixLen (rdW E (recP + 6)) (rdW E (recP + 5))),
      ixLen (rdW E (recP + 5)) (rdW E (recP + 6))] m4 with _ | ⟨ri, m5⟩ <;>
    simp only [c5, reduceCtorEq] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨hrun5, ⟨M5, hS5, hK5, hSt5⟩, hr5⟩ := CoreSpec.run
    (iotaIndexOk_refines' p hp.toIotaProg' hc.inst1 (N + 1) (hk.mono (by omega)) F (by omega) (by omega)
      ⟨m4, Locals.init []⟩ _ dn vis fe M4 eb mode d (rdW E (recP + 5)) (rdW E (recP + 6))
      (rdW E (rl + 2)) (rt.headD 0) mo mn
      (so + (rdW E (recP + 6) - ixLen (rdW E (recP + 6)) (rdW E (recP + 5))))
      (ixLen (rdW E (recP + 5)) (rdW E (recP + 6))) margs _ hS4 hm4 hebm hr3 hsm4 hidx
      (by rw [hSt14.1, ← hsmt]; omega) hxo) c5
  simp only [List.toList_toArray, ← hcpw] at hrun5 hS5
  refine CoreRef.of_run (vckT_run_idx (coreKnot (decMode mode) fe id F) fe d.toNat _ _ lps (decI
    us) args.toList (decI usj) cvj rule margs.toList (decI cmpL) a₀ _ _ _ _ _ _ _ hrun1 hrun2 hrun3
    hrun4 hrun5) (hm ▸ ⟨M5, hS5, hK1.trans (hK2.trans (hK3.trans (hK4.trans hK5))), hSt14.trans
    hSt5⟩) ?_ ?_
  · simp only [decBool, ← hr]
  · unfold ResH; rw [← hr]; exact hr5

end L.Arena
