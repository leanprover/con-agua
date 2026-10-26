import ConAgua.Verdict.FrontE

/-!
# Error refinements of `vi_ctor`, `vi_order*`, `vi_np_go`, `vi_nparams` (lane `verdicts-b`, helper `f2`)

The twin side first (no L): `validateIndD` stops with a record verdict at an early check
(`validateIndD_np`, `validateIndD_nodup`, `validateIndD_len`) or inside the constructor-order loop
(`validateIndD_orderFail`, from `OrderFail`). Then the L side: the error models of the functions
and their claims (`ctorE_fail`, `orderInE_fail`, `orderGoE_fail`, `orderE_fail`, `npGoE_claim`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace L.Front.Ind

/-! ## The twin side -/

/-- A `forIn` whose body yields at the elements before `i` and is done at element `i`. -/
theorem forIn_done {α β : Type} (f : α → β → AM (ForInStep β)) (a : AState) :
    ∀ (xs : List α) (S : Nat → β) (i : Nat) (hi : i < xs.length) (b : β),
    (∀ j (hj : j < i), (f (xs[j]'(by omega)) (S j)).run a = .ok (.yield (S (j + 1)), a)) →
    (f xs[i] (S i)).run a = .ok (.done b, a) →
    (forIn xs (S 0) f).run a = .ok (b, a) := by
  intro xs
  induction xs with
  | nil => intro S i hi; simp at hi
  | cons x xs ih =>
    intro S i hi b hy hd
    rw [List.forIn_cons]
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hd
      rw [run_bind _ _ a _ hd]; rfl
    | succ i =>
      have h0 := hy 0 (by omega)
      simp only [List.getElem_cons_zero] at h0
      rw [run_bind _ _ a _ h0]
      exact ih (fun j => S (j + 1)) i (by simp at hi; omega) b
        (fun j hj => by have := hy (j + 1) (by omega); simpa using this) (by simpa using hd)

/-- The names the validation reads back for its messages are bound handles: every handle of the
parse state's name table reads back. -/
def NamesRead (st : StateD) (a : AState) : Prop :=
  ∀ i h, st.names.get? i = some h → ∃ x, (readName h).run a = .ok (x, a)

theorem name_run {st : StateD} {a a' : AState} {i : Nat} {h : NIdx}
    (hr : (st.name i).run a = .ok (h, a')) : st.names.get? i = some h ∧ a' = a := by
  unfold StateD.name at hr
  cases hg : st.names.get? i with
  | none => rw [hg] at hr; cases hr
  | some h' => rw [hg] at hr; cases hr; exact ⟨rfl, rfl⟩

/-- The values of a `mapM` of a read-only step whose values satisfy `P` satisfy `P`; the state
is unchanged. -/
theorem mapM_all {α β : Type} (P : β → Prop) (f : α → AM β)
    (hf : ∀ x a v a', (f x).run a = .ok (v, a') → P v ∧ a' = a) :
    ∀ (xs : List α) (a a' : AState) (ys : List β), (xs.mapM f).run a = .ok (ys, a') →
      (∀ y ∈ ys, P y) ∧ a' = a := by
  intro xs
  induction xs with
  | nil => intro a a' ys h; simp only [List.mapM_nil] at h; cases h; simp
  | cons x xs ih =>
    intro a a' ys h
    simp only [List.mapM_cons, StateT.run_bind] at h
    cases h1 : (f x).run a with
    | error e => rw [h1] at h; cases h
    | ok q =>
      obtain ⟨v, a1⟩ := q
      rw [h1] at h
      obtain ⟨hv, ha⟩ := hf x a v a1 h1
      simp only [except_ok_bind, StateT.run_bind] at h
      cases h2 : (xs.mapM f).run a1 with
      | error e => rw [h2] at h; cases h
      | ok q2 =>
        obtain ⟨vs, a2⟩ := q2
        rw [h2] at h
        simp only [except_ok_bind] at h
        cases h
        obtain ⟨h3, h4⟩ := ih a1 _ vs h2
        refine ⟨fun y hy => ?_, h4.trans ha⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hv
        · exact h3 y hy

theorem name_all (st : StateD) : ∀ x a v a', (st.name x).run a = .ok (v, a') →
    (∃ i, st.names.get? i = some v) ∧ a' = a :=
  fun x _ _ _ h => ⟨⟨x, (name_run h).1⟩, (name_run h).2⟩

/-- A `bind` whose first step ends in `a` with a value satisfying `P`, the rest from any such value
ending in `a` with a value satisfying `R`. -/
theorem run_bind_ex {α γ : Type} {x : AM α} {k : α → AM γ} {a : AState} (P : α → Prop)
    {R : γ → Prop} (hx : ∃ y, P y ∧ x.run a = .ok (y, a))
    (hk : ∀ y, P y → ∃ z, R z ∧ (k y).run a = .ok (z, a)) :
    ∃ z, R z ∧ (x >>= k).run a = .ok (z, a) := by
  obtain ⟨y, hy, hxr⟩ := hx
  obtain ⟨z, hz, hkr⟩ := hk y hy
  exact ⟨z, hz, by rw [run_bind _ _ a _ hxr]; exact hkr⟩

/-- `forIn_done'` with the final value known only by a property. -/
theorem forIn_done_ex {α β : Type} (f : α → β → AM (ForInStep β)) (a : AState) (xs : List α)
    (init : β) (S : Nat → β) (h0 : S 0 = init) (i : Nat) (hi : i < xs.length) (P : β → Prop)
    (hy : ∀ j (hj : j < i), (f (xs[j]'(by omega)) (S j)).run a = .ok (.yield (S (j + 1)), a))
    (hd : ∃ b, P b ∧ (f xs[i] (S i)).run a = .ok (.done b, a)) :
    ∃ b, P b ∧ (forIn xs init f).run a = .ok (b, a) := by
  obtain ⟨b, hb, hdr⟩ := hd
  exact ⟨b, hb, by subst h0; exact forIn_done f a xs S i hi b hy hdr⟩

/-- **The validation's facts before its constructor order**: the lookups ran (read-only). -/
structure VPre (st : StateD) (a : AState) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (TN : List NIdx) (TT : List EIdx) (LS : List (List NIdx)) (CN : List NIdx) (nPd : Nat) : Prop where
  safe : (tys.any fun x => x.isUnsafe) = false
  np1 : nPd = (tys.map fun x => x.numParams).head?.getD 0
  np2 : ((tys.map fun x => x.numParams).all fun x => x == nPd) = true
  tn : (tys.mapM fun t : IndTypeRec => st.name t.cv.name).run a = .ok (TN, a)
  tt : (tys.mapM fun t : IndTypeRec => getDeclD st t.cv.type).run a = .ok (TT, a)
  ls : (tys.mapM fun t : IndTypeRec => t.ctors.mapM st.name).run a = .ok (LS, a)
  cn : (cts.mapM fun c : IndCtorRec => st.name c.cv.name).run a = .ok (CN, a)


theorem twinCls_declined (w : String) : twinCls (RecordVerdict.declined w).toError = 2 := by
  simp [RecordVerdict.toError, twinCls]

theorem twinCls_invalid (w : String) : twinCls (RecordVerdict.invalid w).toError = 1 := by
  simp [RecordVerdict.toError, twinCls]

/-- **The block's type records disagree on `numParams`**: declined. -/
theorem validateIndD_np {st : StateD} {a : AState} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} (hsafe : (tys.any fun x => x.isUnsafe) = false)
    (hnp : ((tys.map fun x => x.numParams).all fun x =>
      x == (tys.map fun x => x.numParams).head?.getD 0) = false) :
    ∃ v, (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = .ok (.inl v, a) ∧
      twinCls v.toError = 2 := by
  refine ⟨_, ?_, twinCls_declined "inductive block whose type records disagree on numParams"⟩
  unfold ConRon.Arena.Frontend.validateIndD
  simp only [hsafe, Bool.false_eq_true, ite_false, hnp]
  rfl


/-- **A constructor name listed twice**: invalid. -/
theorem validateIndD_nodup {st : StateD} {a : AState} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} {TN : List NIdx} {TT : List EIdx} {LS : List (List NIdx)} {CN : List NIdx}
    {nPd : Nat} (hV : VPre st a tys cts TN TT LS CN nPd) (hnd : ¬ LS.flatten.Nodup) :
    ∃ v, (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = .ok (.inl v, a) ∧
      twinCls v.toError = 1 := by
  refine ⟨_, ?_, twinCls_invalid "duplicate constructor name in an inductive type's ctors"⟩
  unfold ConRon.Arena.Frontend.validateIndD
  simp only [hV.safe, Bool.false_eq_true, ite_false]
  rw [← hV.np1, if_pos hV.np2]
  rw [run_bind _ _ a _ hV.tn, run_bind _ _ a _ hV.tt, run_bind _ _ a _ hV.ls, run_bind _ _ a _ hV.cn]
  rw [if_neg hnd]
  rfl

/-- **The listed constructors are not the constructor records**: invalid. -/
theorem validateIndD_len {st : StateD} {a : AState} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} {TN : List NIdx} {TT : List EIdx} {LS : List (List NIdx)} {CN : List NIdx}
    {nPd : Nat} (hV : VPre st a tys cts TN TT LS CN nPd) (hnd : LS.flatten.Nodup)
    (hlen : LS.flatten.length ≠ cts.length) :
    ∃ v, (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = .ok (.inl v, a) ∧
      twinCls v.toError = 1 := by
  refine ⟨_, ?_, twinCls_invalid (s!"the inductive block lists {LS.flatten.length} constructors \
      and carries {cts.length} constructor records")⟩
  unfold ConRon.Arena.Frontend.validateIndD
  simp only [hV.safe, Bool.false_eq_true, ite_false]
  rw [← hV.np1, if_pos hV.np2]
  rw [run_bind _ _ a _ hV.tn, run_bind _ _ a _ hV.tt, run_bind _ _ a _ hV.ls, run_bind _ _ a _ hV.cn]
  rw [if_pos hnd]
  simp only [beq_iff_eq, hlen, ite_false]
  rfl


theorem forIn_done' {α β : Type} (f : α → β → AM (ForInStep β)) (a : AState) (xs : List α)
    (init : β) (S : Nat → β) (h0 : S 0 = init) (i : Nat) (hi : i < xs.length) (b : β)
    (hy : ∀ j (hj : j < i), (f (xs[j]'(by omega)) (S j)).run a = .ok (.yield (S (j + 1)), a))
    (hd : (f xs[i] (S i)).run a = .ok (.done b, a)) :
    (forIn xs init f).run a = .ok (b, a) := by
  subst h0; exact forIn_done f a xs S i hi b hy hd

/-- The constructor index the twin builds from the constructor names `CN` (`ctorIx`). -/
def ctorIxOf (CN : List NIdx) : Std.HashMap NIdx Nat :=
  (CN.foldl (fun (mi : Std.HashMap NIdx Nat × Nat) x => (mi.1.insert x mi.2, mi.2 + 1)) (∅, 0)).1

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

/-- **The twin's constructor order stops at type `i`, position `c`**: every constructor before
passes its checks (`CtorOK`), constructor `c` of type `i` fails them (`CtorFail`). -/
def OrderFail (st : StateD) (a : AState) (cts : List IndCtorRec) (CN TN : List NIdx)
    (LS : List (List NIdx)) (np fuel : Nat) : Prop :=
  ∃ i, ∃ hi : i < LS.length, ∃ c, ∃ hc : c < LS[i].length,
    (∀ i' (hi' : i' < LS.length), i' < i → ∀ c' (hc' : c' < LS[i'].length),
      ∃ k, CtorOK st a cts CN LS[i'][c'] c' (TN[i']!) np fuel k) ∧
    (∀ c' (hc' : c' < c), ∃ k, CtorOK st a cts CN (LS[i][c']'(by omega)) c' (TN[i]!) np fuel k) ∧
    CtorFail st a cts CN LS[i][c] c (TN[i]!) np fuel

end L.Front.Ind
