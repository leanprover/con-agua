import ConAgua.Front.IndApplyRefine
import ConAgua.Arena.IndPartsSpec.BlockSplitRecs
import ConAgua.Arena.InferBodyIntern
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr

/-!
# `ind_params_ok(nP, off, len)` refines `indParamsOk` (lane `indproofs4`)

`L.Checker.indParamsOkL` (`Checker/Entry.lean`) walks the block's `EREC` slice of constant records
(`decEBlk`): a type former's telescope to a sort (`pi_sort_tele_len`, the front's `sortTeleW`,
refining `piSortTeleLen?`: `sortTeleW_ok`) has at least `nP` binders, a constructor declares
exactly `nP` parameters. The loop is a named block (`ipoLoop`) with a recursive model (`ipoW`);
everything reads only, so the memory and the twin's state are unchanged.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The loop as a named block -/

/-- The loop of `indParamsOkL`, named for its spec. -/
-- con-ron: none — `indParamsOkL`'s own loop (`rfl`), a named block for the proof
def ipoLoop : Stmt := lblk (np, o, l, j, p, k, ok, n) {
  while j < l {
    p := EREC.u64[o + j];
    k := EREC.u64[p];
    if k == 3 {
      (ok, n) := call pi_sort_tele_len(⟪CWF⟫, EREC.u64[p + 4]);
      if ok != 0 && n < np { return 0 }
    };
    if k == 4 {
      if EREC.u64[p + 5] != np { return 0 }
    };
    j += 1
  }
}

/-- `indParamsOkL`, with its loop spliced from `ipoLoop`. -/
-- con-ron: none — `indParamsOkL` itself (`rfl`), its loop a named block for the proof
def indParamsOkL' : FunDecl := lfn (np, o, l) locals (j, p, k, ok, n) {
  j := 0;
  ⟪ipoLoop⟫;
  return 1
}

theorem indParamsOkL_eq : L.Checker.indParamsOkL = indParamsOkL' := rfl

/-! ## The model -/

/-- The constructor check, then the next record. -/
def ipoK (m : Mem) (np pw : Word) (rest : Option Sig) : Option Sig :=
  if rdW (m.arr64 EREC) pw = 4 ∧ rdW (m.arr64 EREC) (pw + 5) ≠ np then some (.ret [0]) else rest

/-- After `pi_sort_tele_len`. -/
def ipoT (m : Mem) (np pw : Word) (rest : Option Sig) : Option (Word × Word) → Option Sig
  | none => none
  | some (ok, n) => if ok ≠ 0 ∧ n < np then some (.ret [0]) else ipoK m np pw rest

/-- **The model of `ind_params_ok`' loop** at L fuel `k`, from record `j`: its signal. -/
def ipoW : Nat → Mem → Word → Word → Word → Word → Option Sig
  | 0, _, _, _, _, _ => none
  | k + 1, m, np, o, l, j =>
    if j < l then
      if rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (o + j)) = 3 then
        ipoT m np (rdW (m.arr64 EREC) (o + j)) (ipoW k m np o l (j + 1))
          (L.Front.Ind.sortTeleW k m CWF (rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (o + j) + 4)))
      else ipoK m np (rdW (m.arr64 EREC) (o + j)) (ipoW k m np o l (j + 1))
    else some .normal

section arms
variable (k : Nat) (m : Mem) (np o l j pw ok n : Word) (rest : Option Sig)
theorem ipoK_bad (h : rdW (m.arr64 EREC) pw = 4 ∧ rdW (m.arr64 EREC) (pw + 5) ≠ np) :
    ipoK m np pw rest = some (.ret [0]) := by simp only [ipoK]; rw [ite_eq_left h]
theorem ipoK_ok (h : ¬ (rdW (m.arr64 EREC) pw = 4 ∧ rdW (m.arr64 EREC) (pw + 5) ≠ np)) :
    ipoK m np pw rest = rest := by simp only [ipoK]; rw [ite_eq_right h]
theorem ipoT_none : ipoT m np pw rest none = none := rfl
theorem ipoT_bad (h : ok ≠ 0 ∧ n < np) : ipoT m np pw rest (some (ok, n)) = some (.ret [0]) := by
  simp only [ipoT]; rw [ite_eq_left h]
theorem ipoT_ok (h : ¬ (ok ≠ 0 ∧ n < np)) : ipoT m np pw rest (some (ok, n)) = ipoK m np pw rest := by
  simp only [ipoT]; rw [ite_eq_right h]
theorem ipoW_exit (h : ¬ j < l) : ipoW (k + 1) m np o l j = some .normal := by
  simp only [ipoW]; rw [ite_eq_right h]
theorem ipoW_ind (h : j < l) (h3 : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (o + j)) = 3) :
    ipoW (k + 1) m np o l j = ipoT m np (rdW (m.arr64 EREC) (o + j)) (ipoW k m np o l (j + 1))
      (L.Front.Ind.sortTeleW k m CWF (rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (o + j) + 4))) := by
  simp only [ipoW]; rw [ite_eq_left h, ite_eq_left h3]
theorem ipoW_other (h : j < l) (h3 : ¬ rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (o + j)) = 3) :
    ipoW (k + 1) m np o l j = ipoK m np (rdW (m.arr64 EREC) (o + j)) (ipoW k m np o l (j + 1)) := by
  simp only [ipoW]; rw [ite_eq_left h, ite_eq_right h3]
end arms

attribute [ind_grind] ipoK_bad ipoK_ok ipoT_none ipoT_bad ipoT_ok ipoW_exit ipoW_ind ipoW_other

/-- `pi_sort_tele_len` with its two lookups only (the front's `sortTele_spec`). -/
theorem sortTele_specI (p : Prog) (hps : p.lookup "pi_sort_tele_len" = some L.Front.Ind.piSortTeleLen)
    (hev : p.lookup "e_view" = some eView) (n : Nat) : ∀ (s₀ : St) (f h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_sort_tele_len" [f, h]
    ⦃fun r s' => s' = s₀ ∧ L.Front.Ind.sortTeleW n s₀.mem f h = some (r.headD 0, r.tail.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ f h; rw [invoke_eq _ hps]; simp only [callFn, L.Front.Ind.piSortTeleLen]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ f h
    rw [invoke_eq _ hps]
    simp only [callFn, L.Front.Ind.piSortTeleLen]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        eView_spec p hev n] <;> finish [L.Front.Ind.sortTeleW]

theorem ipoLoop_spec (p : Prog) (hps : p.lookup "pi_sort_tele_len" = some L.Front.Ind.piSortTeleLen)
    (hev : p.lookup "e_view" = some eView) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p k ipoLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧
      ipoW k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) = some r; ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := ipoLoop) rfl]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, ih,
        sortTele_specI p hps hev k] <;>
      finish (gen := 40) (instances := 20000) [CWF]

theorem ipoW_ne_brk : ∀ (k : Nat) (m : Mem) (np o l j : Word), ipoW k m np o l j ≠ some .brk := by
  intro k
  induction k with
  | zero => intro m np o l j h; simp [ipoW] at h
  | succ k ih =>
    intro m np o l j h
    simp only [ipoW] at h
    split at h
    · split at h
      · simp only [ipoT] at h
        split at h
        · cases h
        · split at h
          · cases h
          · simp only [ipoK] at h; split at h
            · cases h
            · exact ih _ _ _ _ _ h
      · simp only [ipoK] at h; split at h
        · cases h
        · exact ih _ _ _ _ _ h
    · cases h

/-- The function's result from its loop's signal. -/
def ipoR : Option Sig → Option Word
  | some .normal => some 1
  | some (.ret vs) => some (vs.headD 0)
  | _ => none

theorem ipoR_normal : ipoR (some .normal) = some 1 := rfl
theorem ipoR_ret (vs : List Word) : ipoR (some (.ret vs)) = some (vs.headD 0) := rfl

theorem ipo_spec (p : Prog) (hps : p.lookup "pi_sort_tele_len" = some L.Front.Ind.piSortTeleLen)
    (hev : p.lookup "e_view" = some eView) (hp : p.lookup "ind_params_ok" = some L.Checker.indParamsOkL)
    (k : Nat) (s₀ : St) (np o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "ind_params_ok" [np, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ ipoR (ipoW (k + 1) s₀.mem np o l 0) = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp, indParamsOkL_eq]
  simp only [callFn, indParamsOkL']
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      fun s => Triple.step_exec (ipoLoop_spec p hps hev (k + 1) s)] <;>
    finish (gen := 40) (instances := 20000) [ipoR_normal, ipoR_ret, loc_init4, ipoW_ne_brk]

/-! ## The relation to the twin -/

theorem decEBlk_get {dn : NIdx → Option ConLeche.Name} {m : Mem} {o l : Nat} {blk : List IConstantInfo}
    (h : decEBlk dn m o l = some blk) (j : Nat) (hj : j < l) :
    ∃ q, nat? (erA m) (o + j) = some q ∧
      decCI (erA m) dn q = some (blk[j]'(by rw [mapM_opt_length _ _ _ h]; simpa using hj)) := by
  have := mapM_opt_get _ (List.range l) blk h j (by simpa using hj)
  simp only [List.getElem_range, Option.bind_eq_bind, Option.bind_eq_some_iff] at this
  exact this

theorem rdW_of_nat? {a : Array Word} {i q : Nat} (h : nat? a i = some q) (hi : i < 2 ^ 64) :
    rdW a (UInt64.ofNat i) = UInt64.ofNat q ∧ q < 2 ^ 64 := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  have : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using hi)
  simp only [rdW, this, hw, Option.getD_some]
  exact ⟨by simp, w.toNat_lt⟩

theorem ipo_twin_other (nP : Nat) (ci : IConstantInfo) (rest : List IConstantInfo) (a : AState)
    (h1 : ∀ cv caps, ci ≠ .indInfo cv caps) (h2 : ∀ cv x y, ci ≠ .ctorInfo cv x y) :
    (indParamsOk nP (ci :: rest)).run a = (indParamsOk nP rest).run a := by
  cases ci with
  | indInfo cv caps => exact absurd rfl (h1 cv caps)
  | ctorInfo cv x y => exact absurd rfl (h2 cv x y)
  | _ => rfl

/-- **`ind_params_ok`' loop refines `indParamsOk`** on the records from `j`: reading only, the
verdict `true` exactly when the loop falls through. -/
theorem ipoW_ok (dn : NIdx → Option ConLeche.Name) {m : Mem} {a : AState} (hR : ArenaR m a)
    (np o l : Word) (blk : List IConstantInfo) (hdec : decEBlk dn m o.toNat l.toNat = some blk)
    (hb : o.toNat + l.toNat < 2 ^ 64) (hEs : (m.arr64 EREC).size < 2 ^ 64) :
    ∀ (k : Nat) (j : Word) (r : Sig), ipoW k m np o l j = some r → j ≤ l →
      (indParamsOk np.toNat (blk.drop j.toNat)).run a = .ok (decide (r = .normal), a) := by
  have hlen : blk.length = l.toNat := by rw [mapM_opt_length _ _ _ hdec]; simp
  intro k
  induction k with
  | zero => intro j r h; simp [ipoW] at h
  | succ k ih =>
  intro j r h hjl
  by_cases hj : j < l
  rotate_left
  · rw [ipoW_exit (h := hj)] at h
    cases h
    have : j.toNat = l.toNat := by
      have := UInt64.le_iff_toNat_le.mp hjl
      have : ¬ j.toNat < l.toNat := fun h' => hj (UInt64.lt_iff_toNat_lt.mpr h')
      omega
    rw [this, ← hlen, List.drop_length]; rfl
  have hjn : j.toNat < l.toNat := UInt64.lt_iff_toNat_lt.mp hj
  obtain ⟨q, hq, hci⟩ := decEBlk_get hdec j.toNat hjn
  have hoj : (o + j).toNat = o.toNat + j.toNat := by rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨hpw, hqb⟩ := rdW_of_nat? hq (by omega)
  rw [show (UInt64.ofNat (o.toNat + j.toNat) : Word) = o + j by
    apply UInt64.toNat_inj.mp; rw [hoj]; simp; omega] at hpw
  have hj1n : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hdrop : blk.drop j.toNat = blk[j.toNat]'(by omega) :: blk.drop (j.toNat + 1) :=
    List.drop_eq_getElem_cons (by omega)
  have hj1 : j + 1 ≤ l := UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_add]; simp; omega)
  have hqT : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  obtain ⟨wk, hwk, hk⟩ := ciD hci
  have hkw : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (o + j)) = wk := by
    rw [show rdW (m.arr64 EREC) (o + j) = UInt64.ofNat q from hpw]; simp only [rdW, hqT]; rw [show (m.arr64 EREC)[q]? = some wk from hwk]; rfl
  have hpw' : rdW (m.arr64 EREC) (o + j) = UInt64.ofNat q := hpw
  have hqs : q < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp hwk).1
  rw [hdrop]
  -- the step of the twin: `ok` on the record, then the rest
  have hrest : ∀ r', ipoW k m np o l (j + 1) = some r' →
      (indParamsOk np.toNat (blk.drop (j.toNat + 1))).run a = .ok (decide (r' = .normal), a) :=
    fun r' h' => by rw [← hj1n]; exact ih (j + 1) r' h' hj1
  have other : ∀ ci, wk ≠ 3 → wk ≠ 4 →
      (∀ cv caps, ci ≠ .indInfo cv caps) → (∀ cv x y, ci ≠ .ctorInfo cv x y) →
      (indParamsOk np.toNat (ci :: blk.drop (j.toNat + 1))).run a = .ok (decide (r = .normal), a) := by
    intro ci hw3 hw4 h1 h2
    rw [ipoW_other (h := hj) (h3 := by rw [hkw]; exact hw3),
      ipoK_ok (h := by rw [hkw]; exact fun e => hw4 e.1)] at h
    rw [ipo_twin_other _ _ _ _ h1 h2]
    exact hrest r h
  have n3 : ∀ x : Nat, x ≠ 3 → wk.toNat = x → wk ≠ 3 := fun x hx h0 e => hx (by rw [← h0, e]; rfl)
  have n4 : ∀ x : Nat, x ≠ 4 → wk.toNat = x → wk ≠ 4 := fun x hx h0 e => hx (by rw [← h0, e]; rfl)
  rcases hk with ⟨h0, cv, -, hx⟩ | ⟨h0, cv, v, hi, -, -, -, hx⟩ | ⟨h0, cv, -, hx⟩ |
    ⟨h0, cv, caps, hcv, -, hx⟩ | ⟨h0, cv, npc, nf, -, hnpc, -, hx⟩ |
    ⟨h0, cv, mi, rp, ro, rc, rules, -, -, -, -, -, -, hx⟩
  · rw [hx]; exact other _ (n3 0 (by decide) h0) (n4 0 (by decide) h0) (fun _ _ e => by cases e) (fun _ _ _ e => by cases e)
  · rw [hx]; exact other _ (n3 1 (by decide) h0) (n4 1 (by decide) h0) (fun _ _ e => by cases e) (fun _ _ _ e => by cases e)
  · rw [hx]; exact other _ (n3 2 (by decide) h0) (n4 2 (by decide) h0) (fun _ _ e => by cases e) (fun _ _ _ e => by cases e)
  · -- a type former
    rw [hx]
    have hw3 : wk = 3 := UInt64.toNat_inj.mp (by rw [h0]; rfl)
    rw [ipoW_ind (h := hj) (h3 := by rw [hkw]; exact hw3)] at h
    obtain ⟨-, -, hty⟩ := decCV_some hcv
    have hq4 : q + 1 + 3 = q + 4 := by omega
    rw [hq4] at hty
    have hq4b : q + 4 < 2 ^ 64 := by
      cases hw4 : (erA m)[q + 4]? with
      | none => simp [hd?, hw4] at hty
      | some w => have := (Array.getElem?_eq_some_iff.mp hw4).1; simp only [erA] at this; omega
    obtain ⟨w, hwr, -, hwd⟩ := erH_rdW hty hq4b
    have hp4 : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (o + j) + 4) = w := by
      rw [hpw', ← hwr]; congr 1; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_add] <;> omega
    rw [hp4] at h
    rcases hst : L.Front.Ind.sortTeleW k m CWF w with _ | ⟨ok, n⟩
    · rw [hst, ipoT_none] at h; cases h
    rw [hst] at h
    obtain ⟨hrun, hnlt⟩ := L.Front.Ind.sortTeleW_ok m a hR k CWF w ok n hst
    rw [CWF_eq, decE_eq, hwd] at hrun
    simp only [indParamsOk, StateT.run_bind, hrun, except_ok_bind]
    by_cases hbad : ok ≠ 0 ∧ n < np
    · rw [ipoT_bad (h := hbad)] at h
      cases h
      have hn : ¬ np.toNat ≤ n.toNat := by have := UInt64.lt_iff_toNat_lt.mp hbad.2; omega
      simp [hbad.1, hn]; rfl
    · rw [ipoT_ok (h := hbad), ipoK_ok (h := by rw [hkw, hw3]; exact fun e => absurd e.1 (by decide))] at h
      have hres := hrest r h
      by_cases h0' : ok = 0
      · simp [h0', hres]
      · have hnn : ¬ n < np := fun e => hbad ⟨h0', e⟩
        have : np.toNat ≤ n.toNat := by
          have : ¬ n.toNat < np.toNat := fun e => hnn (UInt64.lt_iff_toNat_lt.mpr e)
          omega
        simp [h0', this, hres]
  · -- a constructor
    rw [hx]
    have hw4 : wk = 4 := UInt64.toNat_inj.mp (by rw [h0]; rfl)
    rw [ipoW_other (h := hj) (h3 := by rw [hkw, hw4]; decide)] at h
    have hq5b : q + 5 < 2 ^ 64 := by
      simp only [nat?, Option.map_eq_some_iff] at hnpc
      obtain ⟨w, hw, -⟩ := hnpc
      have := (Array.getElem?_eq_some_iff.mp hw).1; simp only [erA] at this; omega
    obtain ⟨hr5, hnb⟩ := rdW_of_nat? hnpc hq5b
    have hp5 : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (o + j) + 5) = UInt64.ofNat npc := by
      rw [hpw', ← hr5]; congr 1; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_add] <;> omega
    have hnpcT : (UInt64.ofNat npc : Word).toNat = npc := UInt64.toNat_ofNat_of_lt' hnb
    simp only [indParamsOk, StateT.run_bind]
    by_cases hne : UInt64.ofNat npc ≠ np
    · rw [ipoK_bad (h := by rw [hkw, hw4, hp5]; exact ⟨rfl, hne⟩)] at h
      cases h
      have : (npc == np.toNat) = false := by
        simp only [beq_eq_false_iff_ne]; intro e; apply hne; apply UInt64.toNat_inj.mp; rw [hnpcT, e]
      simp [this]; rfl
    · rw [ipoK_ok (h := by rw [hkw, hw4, hp5]; exact fun e => hne e.2)] at h
      have hres := hrest r h
      have : (npc == np.toNat) = true := by
        simp only [beq_iff_eq]; have := Classical.not_not.mp hne; rw [← this, hnpcT]
      simp [this, hres]
  · rw [hx]; exact other _ (n3 5 (by decide) h0) (n4 5 (by decide) h0) (fun _ _ e => by cases e) (fun _ _ _ e => by cases e)

theorem ipoW_sig : ∀ (k : Nat) (m : Mem) (np o l j : Word) (sg : Sig), ipoW k m np o l j = some sg →
    sg = .normal ∨ sg = .ret [0] := by
  intro k
  induction k with
  | zero => intro m np o l j sg h; simp [ipoW] at h
  | succ k ih =>
    intro m np o l j sg h
    simp only [ipoW] at h
    split at h
    · split at h
      · simp only [ipoT] at h
        split at h
        · cases h
        · split at h
          · cases h; exact .inr rfl
          · simp only [ipoK] at h; split at h
            · cases h; exact .inr rfl
            · exact ih _ _ _ _ _ _ h
      · simp only [ipoK] at h; split at h
        · cases h; exact .inr rfl
        · exact ih _ _ _ _ _ _ h
    · cases h; exact .inl rfl

/-- **`ind_params_ok(nP, off, len)` refines `indParamsOk`** under the stage relation, the block's
`EREC` slice decoded: reading only (memory and twin state unchanged), the word `1` exactly when the
twin answers `true`. -/
@[refines ConRon.Arena.indParamsOk]
theorem indParamsOk_refines (p : Prog)
    (hps : p.lookup "pi_sort_tele_len" = some L.Front.Ind.piSortTeleLen)
    (hev : p.lookup "e_view" = some eView) (hp : p.lookup "ind_params_ok" = some L.Checker.indParamsOkL)
    (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (np o l : Word) (blk : List IConstantInfo) (hS : StageR dn vis fe s₀.mem a₀)
    (hblk : DecB (fun m => decEBlk dn m o.toNat l.toNat) s₀.mem blk) (hb : o.toNat + l.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "ind_params_ok" [np, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ AM.ok (indParamsOk np.toNat blk) a₀ ∧
      AM.st (indParamsOk np.toNat blk) a₀ = a₀ ∧
      (r.headD 0 != 0) = AM.res (indParamsOk np.toNat blk) a₀ ∧ (r.headD 0).toNat ≤ 1; ⊤⦄ := by
  refine triple_post (ipo_spec p hps hev hp k s₀ np o l) ?_
  rintro r s' ⟨hl, hm, hR⟩
  have hdec : decEBlk dn s₀.mem o.toNat l.toNat = some blk := hblk.get (decEBlk_mono _ _ _)
  cases hw : ipoW (k + 1) s₀.mem np o l 0 with
  | none => rw [hw] at hR; cases hR
  | some sg =>
  rw [hw] at hR
  have hrun := ipoW_ok dn hS.1.arena.1 np o l blk hdec hb hS.2.2.2.2.1 (k + 1) 0 sg hw (by simp)
  simp only [UInt64.toNat_zero, List.drop_zero] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hl, hm, hok, hst, ?_⟩
  rw [hres]
  rcases ipoW_sig _ _ _ _ _ _ _ hw with rfl | rfl
  · simp only [ipoR, Option.some.injEq] at hR; rw [← hR]; decide
  · simp only [ipoR, Option.some.injEq, List.headD_cons] at hR; rw [← hR]; decide

end L.Ind
