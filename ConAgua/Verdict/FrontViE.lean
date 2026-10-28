import ConAgua.Verdict.FrontE
import ConAgua.Front.IndApplyRefine3
import ConAgua.Checker.NoVerdictTree

/-!
# `validateIndD`'s leaf checks: one model and one refinement each (lane `unify-kit`, helper `vi`)

`vi_unsafe`, `vi_np_go`, `vi_ctor` and `vi_rec_idx` have unified models (`l_model … unified`;
`vi_ctor`'s and `vi_rec_idx`'s callees outside the verdict closure lifted, `nv`). Their ok halves
are facts about the records (no type is unsafe, the `numParams` agree, the twin's constructor
checks pass, the recursor's indices agree), not twin runs, so each refinement is a `RefC`
(`Arena/Verdict.lean`): `unsafe_ref` (its claim `validateIndD`'s record verdict), `npGo_ref`,
`ctor_ref` (`CtorPost`/`CtorErr`: `CtorOK`/`CtorFail`), `recIdx_ref` (`RecIdxPost`/`RecIdxFail`).
The callers' word models read these functions through their runs (`callW`); their ok refinements
take the ok half by `RefC.run_okW`, their error claims the error half by `RefC.run_err`.
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)

set_option experimental.vcgen true

namespace L.Front.Ind
open L.Front

/-- `expr_get` as a table lookup (`lkW`), for the unified models' lifted calls. -/
theorem exprGetL_spec (p : Prog) (hL : IndApplyLookups p) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "expr_get" [i]
    ⦃fun r s' => s' = s₀ ∧ lkW s₀.mem EID i = some (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨h1, h2, h3⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (exprGet_spec p hL.decl.expr n s₀ i)
  refine ⟨h1, ?_⟩
  subst h3; subst h1
  simp [lkW, h2]

/-! ## The models -/

l_model viUnsafe_specE (p : Prog) (hf : p.lookup "vi_unsafe" = some viUnsafe)
  fns [hf ↦ viUnsafeE] grind [arena_grind] extra [L.Arena.ld64_rdW_specE] unified

l_model viNpGo_specE (p : Prog) (hf : p.lookup "vi_np_go" = some viNpGo)
  fns [hf ↦ viNpGoE] grind [arena_grind] extra [L.Arena.ld64_rdW_specE] unified

l_model viCtor_specE (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_ctor ↦ viCtorE]
  specs [findLast_spec p hL n, nameGetL_spec p hL n, exprGetL_spec p hL n, tele_spec p hL n]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE] simp []
  unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model recIdx_specE (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_rec_idx ↦ recIdxE]
  specs [sortTele_spec p hL n]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE]
  unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## `vi_unsafe` -/

/-- **`vi_unsafe`'s ok half**: the memory unchanged, no type record from `j` on is unsafe. -/
structure UnsafePost (m : Mem) (tys : List IndTypeRec) (j : Word) (v : Word × Mem) : Prop where
  mem : v.2 = m
  safe : ∀ k (hk : k < tys.length), j.toNat ≤ k → tys[k].isUnsafe = false

/-- **`vi_unsafe`, both outcomes**: its decline is `validateIndD`'s first check
(`tys.any isUnsafe`, a record verdict). -/
theorem unsafe_ref {b : ByteArray} {m : Mem} {tys : List IndTypeRec} {to tn : Word}
    (hL : ListF (TyF b m) m 11 to.toNat tys) (htn : tn.toNat = tys.length)
    (hto : to.toNat + 11 * tys.length < 2 ^ 63) (p : Prog) (st : StateD) (cts : List IndCtorRec)
    (rcs : List IndRecRec) (a : AState) :
    ∀ n j, RefC True (viUnsafeE p n m to tn j)
      (UnsafePost m tys j)
      (VerdictClaimL (ConRon.Arena.Frontend.validateIndD st tys cts rcs) a) := by
  intro n
  induction n with
  | zero => intro j; simp only [viUnsafeE, RefC_error]; exact fun _ hk => absurd Err.cls_outOfFuel hk
  | succ n ih =>
    intro j
    by_cases hle : tn ≤ j
    · rw [viUnsafeE.arm1 p n m to tn j hle]
      exact ⟨rfl, fun k hk hjk => by have := UInt64.le_iff_toNat_le.mp hle; omega⟩
    have hj := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
    have hj1 := wsucc j tn (UInt64.not_le.mp hle)
    have hix : (to + 11 * j + 7).toNat = to.toNat + 11 * j.toNat + 7 := widx _ _ _ _ (by simp; omega)
    obtain ⟨-, -, -, h7, -, -⟩ := hL.2.2 j.toNat (by omega)
    by_cases h0 : rdW (m.arr64 IFR) (to + 11 * j + 7) = 0
    · rw [viUnsafeE.arm2 p n m to tn j hle h0]
      have ih1 := ih (j + 1)
      rcases h1 : viUnsafeE p n m to tn (j + 1) with e | ⟨u, m₁⟩ <;> rw [h1] at ih1
      · rw [viUnsafeE.k_vi_unsafe.none]; exact ih1
      obtain ⟨rfl, ih2⟩ := ih1
      rw [viUnsafeE.k_vi_unsafe.arm1]
      refine ⟨rfl, fun k hk hjk => ?_⟩
      by_cases hkj : k = j.toNat
      · subst hkj
        rw [wd_eq, hix] at h0
        rw [h0] at h7
        cases hu : tys[j.toNat].isUnsafe
        · rfl
        · rw [hu] at h7; simp [BoolW] at h7
      · exact ih2 k hk (by rw [hj1]; omega)
    · rw [viUnsafeE.abort1 p n m to tn j hle h0]
      intro _ _
      have hu : tys[j.toNat].isUnsafe = true := by
        rw [wd_eq, hix] at h0
        cases hu : tys[j.toNat].isUnsafe
        · rw [hu] at h7; simp [BoolW] at h7; exact absurd h7 h0
        · rfl
      have hany : tys.any (·.isUnsafe) = true := List.any_eq_true.mpr ⟨_, List.getElem_mem _, hu⟩
      refine .inr ⟨.declined "unsafe inductive declaration", a, ?_, ?_⟩
      · show (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = _
        simp [ConRon.Arena.Frontend.validateIndD, hany]
        rfl
      · simp [RecordVerdict.toError, Err.cls, R_UNSAFE_INDUCTIVE_DECLARATION]


/-! ## `vi_np_go` -/

/-- **`vi_np_go`'s ok half**: the memory unchanged, every type record from `j` on has
`numParams = d`. -/
structure NpGoPost (m : Mem) (tys : List IndTypeRec) (d j : Word) (v : Word × Mem) : Prop where
  mem : v.2 = m
  np : ∀ k (hk : k < tys.length), j.toNat ≤ k → tys[k].numParams = d.toNat

/-- **`vi_np_go`'s error half**: an error of class `≠ 0` (the decline) means some type record from
`j` on has `numParams ≠ d`. -/
def NpGoFail (tys : List IndTypeRec) (d j : Word) (e : Err) : Prop :=
  e.cls ≠ 0 → e = .abort R_INDUCTIVE_BLOCK_WHOSE ∧
    ∃ k, ∃ hk : k < tys.length, j.toNat ≤ k ∧ tys[k].numParams ≠ d.toNat

/-- **`vi_np_go`, both outcomes.** -/
theorem npGo_ref {b : ByteArray} {m : Mem} {tys : List IndTypeRec} {to tn d : Word}
    (hL : ListF (TyF b m) m 11 to.toNat tys) (htn : tn.toNat = tys.length)
    (hto : to.toNat + 11 * tys.length < 2 ^ 63) (p : Prog) :
    ∀ n j, RefC True (viNpGoE p n m to tn d j)
      (NpGoPost m tys d j) (NpGoFail tys d j) := by
  intro n
  induction n with
  | zero => intro j; simp only [viNpGoE, RefC_error]; exact fun _ hk => absurd Err.cls_outOfFuel hk
  | succ n ih =>
    intro j
    by_cases hle : tn ≤ j
    · rw [viNpGoE.arm1 p n m to tn d j hle]
      exact ⟨rfl, fun k hk hjk => by have := UInt64.le_iff_toNat_le.mp hle; omega⟩
    have hj := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
    have hj1 := wsucc j tn (UInt64.not_le.mp hle)
    have hix : (to + 11 * j + 10).toNat = to.toNat + 11 * j.toNat + 10 := widx _ _ _ _ (by simp; omega)
    obtain ⟨-, -, -, -, -, h10⟩ := hL.2.2 j.toNat (by omega)
    by_cases h0 : rdW (m.arr64 IFR) (to + 11 * j + 10) = d
    · rw [viNpGoE.arm2 p n m to tn d j hle h0]
      have ih1 := ih (j + 1)
      rcases h1 : viNpGoE p n m to tn d (j + 1) with e | ⟨u, m₁⟩ <;> rw [h1] at ih1
      · rw [viNpGoE.k_vi_np_go.none]
        intro _ hk
        obtain ⟨he, k, hk', hjk, hne⟩ := ih1 trivial hk
        exact ⟨he, k, hk', by rw [hj1] at hjk; omega, hne⟩
      obtain ⟨rfl, ih2⟩ := ih1
      rw [viNpGoE.k_vi_np_go.arm1]
      refine ⟨rfl, fun k hk hjk => ?_⟩
      by_cases hkj : k = j.toNat
      · subst hkj
        rw [wd_eq, hix] at h0
        rw [← h10.1, h0]
      · exact ih2 k hk (by rw [hj1]; omega)
    · rw [viNpGoE.abort1 p n m to tn d j hle h0]
      intro _ _
      refine ⟨rfl, j.toNat, by omega, Nat.le_refl _, fun he => h0 ?_⟩
      rw [wd_eq, hix]
      apply UInt64.toNat_inj.mp
      rw [h10.1, he]

/-! ## `vi_ctor` -/

/-- The twin's `ctorIx` map of the constructor names `CN`. -/
def ctorIxOf (CN : List NIdx) : Std.HashMap NIdx Nat :=
  (CN.foldl (fun (mi : Std.HashMap NIdx Nat × Nat) x => (mi.1.insert x mi.2, mi.2 + 1)) (∅, 0)).1

/-- **The twin's checks of one constructor pass**: record `k` is the last one named `nn` among the
constructor names `CN`, and its `cidx`, `induct` and telescope agree. -/
def CtorOK (st : StateD) (a : AState) (cts : List IndCtorRec) (CN : List NIdx) (nn : NIdx)
    (j : Nat) (T : NIdx) (np fuel : Nat) (k : Nat) : Prop :=
  ∃ hk : k < cts.length,
    (CN.foldl (fun (mi : Std.HashMap NIdx Nat × Nat) x => (mi.1.insert x mi.2, mi.2 + 1)) (∅, 0)).1[nn]? =
      some k ∧
    (∀ ci, cts[k].cidx = some ci → ci = j) ∧
    (∀ iw, cts[k].induct = some iw → (st.name iw).run a = .ok (T, a)) ∧
    ∃ cty, (getDeclD st cts[k].cv.type).run a = .ok (cty, a) ∧
      (ConRon.Arena.Frontend.indPiTeleLen fuel cty).run a = .ok (np + cts[k].numFields, a)

/-- **The twin's checks of constructor `nn` (number `j` of the type named `T`) fail**: no record
of that name, or its `cidx`, its `induct`, or its telescope disagrees (each an `.invalid`). -/
def CtorFail (st : StateD) (a : AState) (cts : List IndCtorRec) (CN : List NIdx) (nn : NIdx)
    (j : Nat) (T : NIdx) (np fuel : Nat) : Prop :=
  (ctorIxOf CN)[nn]? = none ∨
  ∃ k, (ctorIxOf CN)[nn]? = some k ∧ ∃ hk : k < cts.length,
    ((∃ ci, cts[k].cidx = some ci ∧ ci ≠ j) ∨
     ((∀ ci, cts[k].cidx = some ci → ci = j) ∧
      ((∃ iw iwn, cts[k].induct = some iw ∧ (st.name iw).run a = .ok (iwn, a) ∧ iwn ≠ T) ∨
       ((∀ iw, cts[k].induct = some iw → (st.name iw).run a = .ok (T, a)) ∧
        ∃ cty tele, (getDeclD st cts[k].cv.type).run a = .ok (cty, a) ∧
          (ConRon.Arena.Frontend.indPiTeleLen fuel cty).run a = .ok (tele, a) ∧
          np + cts[k].numFields ≠ tele))))

/-- `ifl_find_last` found nothing: no word of the slice is `x`. -/
theorem findLastW_zero : ∀ (n : Nat) (m : Mem) (o x j f k : Word), findLastW n m o x j = some (f, k) →
    o.toNat + j.toNat < 2 ^ 64 → f = 0 → ∀ k', k' < j.toNat → wd m IFL (o.toNat + k') ≠ x := by
  intro n
  induction n with
  | zero => intro m o x j f k h; simp [findLastW] at h
  | succ n ih =>
    intro m o x j f k h hb hf
    simp only [findLastW] at h
    split at h
    · rename_i hj0; subst hj0; intro k' hk'; simp at hk'
    rename_i hj0
    have hj0' : j.toNat ≠ 0 := fun e => hj0 (UInt64.toNat_inj.mp (by simpa using e))
    have hj1 : (j - 1).toNat = j.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
    have hoj : (o + j - 1).toNat = o.toNat + (j.toNat - 1) := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [widx2 _ _ hb]; simp; omega)),
        widx2 _ _ hb]; simp; omega
    split at h
    · cases h; exact absurd hf (by decide)
    · rename_i hx
      rw [wd_eq, hoj] at hx
      have := ih m o x (j - 1) f k h (by rw [hj1]; omega) hf
      rw [hj1] at this
      intro k' hk'
      by_cases hk : k' = j.toNat - 1
      · subst hk; exact hx
      · exact this k' (by omega)

/-- **`vi_ctor`'s ok half**: the memory unchanged, the record's pointer `co + 10 k`, and the twin's
checks of record `k` pass. -/
structure CtorPost (st : StateD) (a : AState) (cts : List IndCtorRec) (m : Mem)
    (nn j tt np fuel cno co : Word) (v : Word × Mem) : Prop where
  mem : v.2 = m
  ok : ∃ k, v.1 = co + 10 * UInt64.ofNat k ∧ CtorOK st a cts (islice m cno.toNat cts.length)
    (decI nn) j.toNat (decI tt) np.toNat fuel.toNat k

/-- **`vi_ctor`'s error half**: an error of class `≠ 0` is a reject (class `1`), and the twin's
checks of the constructor fail (with the type's name handle below `2^32`). -/
def CtorErr (st : StateD) (a : AState) (cts : List IndCtorRec) (m : Mem)
    (nn j tt np fuel cno : Word) (e : Err) : Prop :=
  tt.toNat < 2 ^ 32 → e.cls ≠ 0 → e.cls = 1 ∧
    CtorFail st a cts (islice m cno.toNat cts.length) (decI nn) j.toNat (decI tt) np.toNat fuel.toNat

/-- **`vi_ctor`, both outcomes**: against the twin's constructor lookup and checks. -/
theorem ctor_ref {b : ByteArray} {m : Mem} {a : AState} {st : StateD} (hR : ArenaR m a)
    (hD : StateDR m st) {cts : List IndCtorRec} {nn j tt np fuel cno cn co : Word}
    (hCt : ListF (CtF b m) m 10 co.toNat cts) (hcn : cn.toNat = cts.length)
    (hCN : ∀ k, k < cts.length → (wd m IFL (cno.toNat + k)).toNat < 2 ^ 32)
    (hcnb : cno.toNat + cts.length < 2 ^ 63) (hnn : nn.toNat < 2 ^ 32) (hnp : np.toNat < 10 ^ 18)
    (hco : co.toNat + 10 * cts.length < 2 ^ 63) (p : Prog) (n : Nat) :
    RefC True (viCtorE p n m nn j tt np fuel cno cn co)
      (CtorPost st a cts m nn j tt np fuel cno co) (CtorErr st a cts m nn j tt np fuel cno) := by
  cases n with
  | zero => exact fun _ _ hk => absurd Err.cls_outOfFuel hk
  | succ n =>
  rw [viCtorE.arm1]
  rcases hf : findLastW n m cno nn cn with _ | ⟨f, k⟩
  · rw [liftE_none, viCtorE.k_ifl_find_last.none]; exact fun _ _ hk => absurd Err.cls_oob hk
  rw [liftE_some]
  by_cases hf0 : f = 0
  · rw [viCtorE.k_ifl_find_last.abort1 p n j tt np fuel co m f k hf0]
    refine fun _ _ _ => ⟨by decide, .inl ?_⟩
    unfold ctorIxOf
    rw [ctorIx_last.ctorIx_absent _ ∅ 0 (decI nn) fun k' hk' he => ?_]
    · simp
    rw [islice_length] at hk'
    rw [islice_get] at he
    exact findLastW_zero n m cno nn cn _ _ hf (by omega) hf0 k' (by omega) (decI_inj (hCN k' hk') hnn he)
  obtain ⟨f1, f2, f3⟩ := findLastW_facts n m cno nn cn f k hf (by omega) hf0
  rw [hcn] at f1 f3
  have hkk : (UInt64.ofNat k.toNat) = k := UInt64.ofNat_toNat
  obtain ⟨-, -, hct⟩ := hCt
  obtain ⟨⟨c1, -, c3⟩, c4, c5, c6, c7⟩ := hct k.toNat f1
  -- the record's words
  have hk10 : (10 : Word).toNat = 10 := rfl
  have ix : ∀ s : Word, s.toNat < 10 → (co + 10 * k + s).toNat = co.toNat + 10 * k.toNat + s.toNat := by
    intro s hs; rw [widx _ _ _ _ (by rw [hk10]; omega), hk10]
  have rd : ∀ s : Word, s.toNat < 10 →
      rdW (m.arr64 IFR) (co + 10 * k + s) = wd m IFR (co.toNat + 10 * k.toNat + s.toNat) := by
    intro s hs; rw [wd_eq, ix s hs]
  -- the lookup
  have hfold : ((islice (k := .name) m cno.toNat cts.length).foldl
      (fun (mi : Std.HashMap NIdx Nat × Nat) x => (mi.1.insert x mi.2, mi.2 + 1)) (∅, 0)).1[(decI nn : NIdx)]? =
      some k.toNat := by
    have := ctorIx_last (islice m cno.toNat cts.length) ∅ 0 (decI nn) k.toNat
      (by rw [islice_length]; exact f1) (by rw [islice_get, f2]) (fun k' h1 h2 => by
        rw [islice_get]; intro e
        rw [islice_length] at h2
        exact f3 k' h1 h2 (decI_inj (hCN k' h2) hnn e))
    simpa using this
  -- the `cidx` check
  by_cases g6 : rdW (m.arr64 IFR) (co + 10 * k + 6) ≠ 0 ∧ rdW (m.arr64 IFR) (co + 10 * k + 7) ≠ j
  · rw [viCtorE.k_ifl_find_last.abort2 p n j tt np fuel co m f k hf0 g6.1 g6.2]
    refine fun _ _ _ => ⟨by decide, .inr ⟨k.toNat, hfold, f1, .inl ?_⟩⟩
    rw [rd 6 (by decide), rd 7 (by decide)] at g6
    simp only [show (6 : Word).toNat = 6 from rfl, show (7 : Word).toNat = 7 from rfl] at g6
    cases hci : cts[k.toNat].cidx with
    | none => rw [hci] at c6; exact absurd c6 g6.1
    | some ci =>
      rw [hci] at c6
      obtain ⟨-, e2⟩ := c6
      refine ⟨ci, rfl, fun hcj => g6.2 ?_⟩
      apply UInt64.toNat_inj.mp
      rw [show co.toNat + 10 * k.toNat + 7 = co.toNat + 10 * k.toNat + 6 + 1 by omega, e2.1, hcj]
  have hcidx' : ∀ ci, cts[k.toNat].cidx = some ci → ci = j.toNat := by
    intro ci hci
    rw [hci] at c6
    obtain ⟨e1, e2⟩ := c6
    have : rdW (m.arr64 IFR) (co + 10 * k + 6) ≠ 0 := by
      rw [rd 6 (by decide)]; simp only [show (6 : Word).toNat = 6 from rfl]; rw [e1]; decide
    have hj : rdW (m.arr64 IFR) (co + 10 * k + 7) = j := Classical.byContradiction fun hne => g6 ⟨this, hne⟩
    rw [rd 7 (by decide)] at hj
    simp only [show (7 : Word).toNat = 7 from rfl,
      show co.toNat + 10 * k.toNat + 7 = co.toNat + 10 * k.toNat + 6 + 1 by omega] at hj
    rw [← e2.1, hj]
  have hJ : viCtorE.k_ifl_find_last p n j tt np fuel co m (.ok (f, k)) =
      viCtorE.j1 p n tt np fuel (co + 10 * k) m := by
    by_cases g : rdW (m.arr64 IFR) (co + 10 * k + 6) = 0
    · exact viCtorE.k_ifl_find_last.arm2 p n j tt np fuel co m f k hf0 g
    · exact viCtorE.k_ifl_find_last.arm1 p n j tt np fuel co m f k hf0 g
        (Classical.byContradiction fun hne => g6 ⟨g, hne⟩)
  rw [hJ]
  -- the telescope, after the `induct` check
  have hJ2 : (∀ iw, cts[k.toNat].induct = some iw → (st.name iw).run a = .ok (decI tt, a)) →
      RefC True (viCtorE.j2 p n np fuel (co + 10 * k) m)
        (CtorPost st a cts m nn j tt np fuel cno co) (CtorErr st a cts m nn j tt np fuel cno) := by
    intro hind
    rw [viCtorE.j2.arm1]
    rcases ht : lkW m EID (rdW (m.arr64 IFR) (co + 10 * k + 2)) with _ | t
    · rw [liftE_none, viCtorE.k_expr_get.none]; exact fun _ _ hk => absurd Err.cls_oob hk
    rw [liftE_some, viCtorE.k_expr_get.arm1]
    have hexp := (lkW_expr hD a ht).1
    rw [rd 2 (by decide)] at hexp
    simp only [show (2 : Word).toNat = 2 from rfl] at hexp
    rw [c3.1] at hexp
    rcases hx : teleW n m fuel t with _ | x
    · rw [liftE_none, viCtorE.k_ind_pi_tele_len.none]; exact fun _ _ hk => absurd Err.cls_oob hk
    rw [liftE_some]
    obtain ⟨t1, -⟩ := teleW_ok m a hR n fuel t x hx
    have hw4 : (np + rdW (m.arr64 IFR) (co + 10 * k + 4)).toNat = np.toNat + cts[k.toNat].numFields := by
      rw [rd 4 (by decide)]
      simp only [show (4 : Word).toNat = 4 from rfl]
      rw [widx2 _ _ (by rw [c4.1]; have := c4.2; omega), c4.1]
    by_cases g4 : np + rdW (m.arr64 IFR) (co + 10 * k + 4) = x
    · rw [viCtorE.k_ind_pi_tele_len.arm1 p np _ m x g4]
      refine ⟨rfl, k.toNat, by rw [hkk], f1, hfold, hcidx', hind, decE t, hexp, ?_⟩
      rw [t1, ← g4, hw4]
    · rw [viCtorE.k_ind_pi_tele_len.abort1 p np _ m x g4]
      refine fun _ _ _ => ⟨by decide, .inr ⟨k.toNat, hfold, f1, .inr ⟨hcidx', .inr ⟨hind, _, _, hexp, t1, fun hne => g4 ?_⟩⟩⟩⟩
      apply UInt64.toNat_inj.mp
      rw [hw4, hne]
  by_cases g8 : rdW (m.arr64 IFR) (co + 10 * k + 8) = 0
  · -- no `induct`
    rw [viCtorE.j1.arm2 p n tt np fuel _ m g8]
    refine hJ2 fun iw hiw => ?_
    rw [hiw] at c7
    rw [rd 8 (by decide)] at g8
    simp only [show (8 : Word).toNat = 8 from rfl] at g8
    rw [c7.1] at g8; exact absurd g8 (by decide)
  rw [viCtorE.j1.arm1 p n tt np fuel _ m g8]
  rcases hl : lkW m NID (rdW (m.arr64 IFR) (co + 10 * k + 9)) with _ | x
  · rw [liftE_none, viCtorE.k_name_get.none]; exact fun _ _ hk => absurd Err.cls_oob hk
  rw [liftE_some]
  obtain ⟨hnm, hx32⟩ := lkW_name hD a hl
  rw [rd 9 (by decide)] at hnm
  simp only [show (9 : Word).toNat = 9 from rfl] at hnm
  obtain ⟨iw, hiw, hiwv⟩ : ∃ iw, cts[k.toNat].induct = some iw ∧
      (wd m IFR (co.toNat + 10 * k.toNat + 9)).toNat = iw := by
    cases hiw : cts[k.toNat].induct with
    | none =>
      rw [hiw] at c7
      exfalso; apply g8
      rw [rd 8 (by decide)]; exact c7
    | some iw =>
      rw [hiw] at c7
      refine ⟨iw, rfl, ?_⟩
      rw [show co.toNat + 10 * k.toNat + 9 = co.toNat + 10 * k.toNat + 8 + 1 by omega]; exact c7.2.1
  rw [hiwv] at hnm
  by_cases gt : x = tt
  · rw [viCtorE.k_name_get.arm1 p n tt np fuel _ m x gt]
    refine hJ2 fun iw' hiw' => ?_
    rw [hiw] at hiw'; cases hiw'
    rw [hnm, gt]
  · rw [viCtorE.k_name_get.abort1 p n tt np fuel _ m x gt]
    exact fun _ htt _ => ⟨by decide, .inr ⟨k.toNat, hfold, f1, .inr ⟨hcidx',
      .inl ⟨iw, _, hiw, hnm, fun he => gt (decI_inj hx32 htt he)⟩⟩⟩⟩

/-! ## `vi_rec_idx` -/

/-- **`vi_rec_idx`'s ok half**: the memory unchanged, and every type from `j` on named `T` has a
sort telescope of `nP + nI` binders, if any. -/
structure RecIdxPost (m : Mem) (a : AState) (T ni np tn tyn tyt fuel j : Word) (v : Word × Mem) :
    Prop where
  mem : v.2 = m
  idx : ∀ k, j.toNat ≤ k → k < tn.toNat → wd m IFL (tyn.toNat + k) = T →
    ∃ o, (piSortTeleLen? fuel.toNat (decE (wd m IFL (tyt.toNat + k)))).run a = .ok (o, a) ∧
      ∀ x, o = some x → np.toNat + ni.toNat = x

/-- **`vi_rec_idx`'s error half**: a class-`≠ 0` error is the indices check failing at the first
type `k ≥ j` named `T` whose telescope disagrees, the earlier ones named `T` agreeing. -/
def RecIdxFail (m : Mem) (a : AState) (T ni np tn tyn tyt fuel j : Word) (e : Err) : Prop :=
  e.cls ≠ 0 → e = .abort R_RECURSOR_DECLARES_INDICES ∧
    ∃ k, j.toNat ≤ k ∧ k < tn.toNat ∧ wd m IFL (tyn.toNat + k) = T ∧
      (∀ k', j.toNat ≤ k' → k' < k → wd m IFL (tyn.toNat + k') = T → ∃ o,
        (piSortTeleLen? fuel.toNat (decE (wd m IFL (tyt.toNat + k')))).run a = .ok (o, a) ∧
          ∀ x, o = some x → np.toNat + ni.toNat = x) ∧
      ∃ x, (piSortTeleLen? fuel.toNat (decE (wd m IFL (tyt.toNat + k)))).run a = .ok (some x, a) ∧
        np.toNat + ni.toNat ≠ x

/-- **`vi_rec_idx`, both outcomes.** -/
theorem recIdx_ref {m : Mem} {a : AState} (hR : ArenaR m a) {T ni np tn tyn tyt fuel : Word}
    (hnp : np.toNat < 10 ^ 18) (hni : ni.toNat < 10 ^ 18) (hb : tyn.toNat + tn.toNat ≤ 2 ^ 63) (hb' : tyt.toNat + tn.toNat ≤ 2 ^ 63) (p : Prog) :
    ∀ n j, RefC True (recIdxE p n m T ni np tn tyn tyt fuel j)
      (RecIdxPost m a T ni np tn tyn tyt fuel j) (RecIdxFail m a T ni np tn tyn tyt fuel j) := by
  intro n
  induction n with
  | zero => intro j; simp only [recIdxE, RefC_error]; exact fun _ hk => absurd Err.cls_outOfFuel hk
  | succ n ih =>
    intro j
    by_cases hle : tn ≤ j
    · rw [recIdxE.arm1 p n m T ni np tn tyn tyt fuel j hle]
      exact ⟨rfl, fun k h1 h2 => by have := UInt64.le_iff_toNat_le.mp hle; omega⟩
    have hjn := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
    have hj1 := wsucc j tn (UInt64.not_le.mp hle)
    have ex1 : rdW (m.arr64 IFL) (tyn + j) = wd m IFL (tyn.toNat + j.toNat) := by
      rw [wd_eq, widx2 _ _ (by omega)]
    have ex2 : rdW (m.arr64 IFL) (tyt + j) = wd m IFL (tyt.toNat + j.toNat) := by
      rw [wd_eq, widx2 _ _ (by omega)]
    -- the rest of the loop, given the check at `j`
    have hrest : (wd m IFL (tyn.toNat + j.toNat) = T → ∃ o,
        (piSortTeleLen? fuel.toNat (decE (wd m IFL (tyt.toNat + j.toNat)))).run a = .ok (o, a) ∧
          ∀ x, o = some x → np.toNat + ni.toNat = x) →
        RefC True (recIdxE.j1 p n T ni np tn tyn tyt fuel j m)
          (RecIdxPost m a T ni np tn tyn tyt fuel j) (RecIdxFail m a T ni np tn tyn tyt fuel j) := by
      intro hpre
      rw [recIdxE.j1.arm1]
      have ih1 := ih (j + 1)
      rcases h2 : recIdxE p n m T ni np tn tyn tyt fuel (j + 1) with e | ⟨u, m₁⟩ <;> rw [h2] at ih1
      · rw [recIdxE.k_vi_rec_idx.none]
        intro _ hk
        obtain ⟨he, k, k1, k2, k3, k4, k5⟩ := ih1 trivial hk
        rw [hj1] at k1
        refine ⟨he, k, by omega, k2, k3, fun k' h1 h2 h3 => ?_, k5⟩
        by_cases hkj : k' = j.toNat
        · subst hkj; exact hpre h3
        · exact k4 k' (by rw [hj1]; omega) h2 h3
      · obtain ⟨rfl, ih2⟩ := ih1
        rw [recIdxE.k_vi_rec_idx.arm1]
        refine ⟨rfl, fun k h1 h2 h3 => ?_⟩
        by_cases hkj : k = j.toNat
        · subst hkj; exact hpre h3
        · exact ih2 k (by rw [hj1]; omega) h2 h3
    by_cases hT : rdW (m.arr64 IFL) (tyn + j) = T
    · rw [recIdxE.arm2 p n m T ni np tn tyn tyt fuel j hle hT]
      rw [ex1] at hT
      rcases hs : sortTeleW n m fuel (rdW (m.arr64 IFL) (tyt + j)) with _ | ⟨ok, kk⟩
      · rw [liftE_none, recIdxE.k_pi_sort_tele_len.none]
        exact fun _ hk => absurd Err.cls_oob hk
      rw [liftE_some]
      rw [ex2] at hs
      obtain ⟨s1, -⟩ := sortTeleW_ok m a hR n fuel _ ok kk hs
      by_cases h0 : ok = 0
      · rw [recIdxE.k_pi_sort_tele_len.arm2 p n T ni np tn tyn tyt fuel j m ok kk h0]
        exact hrest fun _ => ⟨_, s1, fun x hx => by rw [ite_eq_left h0] at hx; cases hx⟩
      by_cases hx : np + ni = kk
      · rw [recIdxE.k_pi_sort_tele_len.arm1 p n T ni np tn tyn tyt fuel j m ok kk h0 hx]
        exact hrest fun _ => ⟨_, s1, fun x hx' => by
          simp only [h0, ite_false, Option.some.injEq] at hx'
          rw [← hx', ← hx, widx2 _ _ (by omega)]⟩
      · rw [recIdxE.k_pi_sort_tele_len.abort1 p n T ni np tn tyn tyt fuel j m ok kk h0 hx]
        intro _ _
        refine ⟨rfl, j.toNat, Nat.le_refl _, hjn, hT, fun k' h1 h2 => by omega, kk.toNat, ?_, ?_⟩
        · rw [s1, ite_eq_right h0]
        · intro he
          apply hx
          apply UInt64.toNat_inj.mp
          rw [widx2 _ _ (by omega), he]
    · rw [recIdxE.arm3 p n m T ni np tn tyn tyt fuel j hle hT]
      rw [ex1] at hT
      exact hrest fun h' => absurd h' hT

end L.Front.Ind
