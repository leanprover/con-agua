import ConAgua.Verdict.FrontE
import ConAgua.Front.IndApplyRefine9
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConRon.Bridge.Frontend.Lines

/-!
# Error refinements of `vi_ctor`, `vi_order*`, `vi_np_go`, `vi_nparams` (lane `verdicts-b`, helper `f2`)

The twin side first (no L): `validateIndD` stops with a record verdict at an early check
(`validateIndD_np`, `validateIndD_nodup`, `validateIndD_len`) or inside the constructor-order loop
(`validateIndD_orderFail`, from `OrderFail`). Then the L side: the error models of the functions
and their claims (`ctorE_fail`, `orderInE_fail`, `orderGoE_fail`, `orderE_fail` with
`orderFail_of_W` to the twin's `OrderFail`; `npGoE_claim`, `viNparams_fail`, `viNparams_refinesE`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

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
      simp only [except_ok_bind] at h
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
  rw [← hV.np1, ite_eq_left hV.np2]
  rw [run_bind _ _ a _ hV.tn, run_bind _ _ a _ hV.tt, run_bind _ _ a _ hV.ls, run_bind _ _ a _ hV.cn]
  rw [ite_eq_right hnd]
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
  rw [← hV.np1, ite_eq_left hV.np2]
  rw [run_bind _ _ a _ hV.tn, run_bind _ _ a _ hV.tt, run_bind _ _ a _ hV.ls, run_bind _ _ a _ hV.cn]
  rw [ite_eq_left hnd]
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

theorem run_bind_exG {α γ δ : Type} {x : AM α} {k : α → AM γ} {a : AState} (g : δ → γ) (P : α → Prop)
    {R : δ → Prop} (hx : ∃ y, P y ∧ x.run a = .ok (y, a))
    (hk : ∀ y, P y → ∃ z, R z ∧ (k y).run a = .ok (g z, a)) :
    ∃ z, R z ∧ (x >>= k).run a = .ok (g z, a) := by
  obtain ⟨y, hy, hxr⟩ := hx
  obtain ⟨z, hz, hkr⟩ := hk y hy
  exact ⟨z, hz, by rw [run_bind _ _ a _ hxr]; exact hkr⟩

/-- **The constructor order stops**: the twin's validation returns an `.invalid` verdict. -/
theorem validateIndD_orderFail {st : StateD} {a : AState} {tys : List IndTypeRec}
    {cts : List IndCtorRec} {rcs : List IndRecRec} {TN : List NIdx} {TT : List EIdx}
    {LS : List (List NIdx)} {CN : List NIdx} {nPd fuel : Nat} (hV : VPre st a tys cts TN TT LS CN nPd)
    (hnd : LS.flatten.Nodup) (hlen : LS.flatten.length = cts.length) (hzl : TN.length = LS.length)
    (hRN : NamesRead st a) (hfuel : a.store.nodeCount + 1 = fuel)
    (hO : OrderFail st a cts CN TN LS nPd fuel) :
    ∃ z, (∃ w, z = Sum.inl (RecordVerdict.invalid w)) ∧
      (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = .ok (z, a) := by
  obtain ⟨i, hi, c, hc, hpre, hpre', hfail⟩ := hO
  subst hfuel
  -- the handles the messages read back
  have hTNr : ∀ y ∈ TN, ∃ x, (readName y).run a = .ok (x, a) := fun y hy => by
    obtain ⟨j, hj⟩ := (mapM_all _ (fun t : IndTypeRec => st.name t.cv.name) (fun t => name_all st t.cv.name) _ a a TN hV.tn).1 y hy
    exact hRN j y hj
  have hLSr : ∀ l ∈ LS, ∀ y ∈ l, ∃ x, (readName y).run a = .ok (x, a) := fun l hl y hy => by
    have := (mapM_all (fun l : List NIdx => ∀ y ∈ l, ∃ j, st.names.get? j = some y) _
      (fun t a v a' h => mapM_all _ _ (name_all st) t.ctors a a' v h) _ a a LS hV.ls).1 l hl y hy
    obtain ⟨j, hj⟩ := this
    exact hRN j y hj
  unfold ConRon.Arena.Frontend.validateIndD
  simp only [hV.safe, Bool.false_eq_true, ite_false]
  rw [← hV.np1, ite_eq_left hV.np2]
  rw [run_bind _ _ a _ hV.tn, run_bind _ _ a _ hV.tt, run_bind _ _ a _ hV.ls, run_bind _ _ a _ hV.cn]
  rw [ite_eq_left hnd]
  simp only [hlen, beq_self_eq_true, ite_true]
  rw [run_bind _ _ a _ (storeFuel_run a)]
  let ordered : List IndCtorRec := LS.flatten.map fun nn => cts[((ctorIxOf CN)[nn]?).getD 0]!
  have hordl : ordered.length = LS.flatten.length := by simp only [ordered, List.length_map]
  have hord : ∀ i' (hi' : i' < LS.length) c' (hc' : c' < LS[i'].length) k,
      (ctorIxOf CN)[LS[i'][c']]? = some k →
      ∃ hp : fpos LS i' + c' < ordered.length, ordered[fpos LS i' + c'] = cts[k]! := by
    intro i' hi' c' hc' k hk
    have hp := fpos_lt LS i' c' hi' hc'
    refine ⟨by rw [hordl]; exact hp, ?_⟩
    simp only [ordered, List.getElem_map]
    rw [← getElem_flatten' LS i' c' hi' hc', hk]; rfl
  refine run_bind_ex (fun b => ∃ w, b.1 = some (Sum.inl (RecordVerdict.invalid w))) ?_ ?_
  rotate_left
  · rintro ⟨r, arr⟩ ⟨w, hw⟩
    simp only at hw; subst hw
    exact ⟨_, ⟨w, rfl⟩, rfl⟩
  have hzl' : (TN.zip LS).length = LS.length := by simp [hzl]
  refine forIn_done_ex _ a _ _ (fun i => ((none : Option (RecordVerdict ⊕ List IndCtorRec × Nat)),
    (ordered.take (fpos LS i)).toArray)) (by simp [fpos]) i (by rw [hzl']; exact hi) _ ?_ ?_
  · -- the types before: every constructor passes
    intro i' hi''
    have hi' : i' < LS.length := by omega
    simp only [List.getElem_zip]
    rw [run_bind _ _ a _ (forIn_yield' _ a _ _ (fun c => ((none : Option (RecordVerdict ⊕ List IndCtorRec × Nat)),
      (ordered.take (fpos LS i' + c)).toArray, c)) ?i0 ?istep)]
    case i0 => simp
    case istep =>
      intro c hc
      obtain ⟨k, hk, hfold, hcidx, hind, cty, hcty, htele⟩ := hpre i' hi' hi'' c hc
      obtain ⟨hp, hord'⟩ := hord i' hi' c hc k hfold
      have hck : cts[k]! = cts[k] := getElem!_pos cts k hk
      rw [hck] at hord'
      have hiT : i' < TN.length := by omega
      have hTNi : TN[i']! = TN[i'] := getElem!_pos TN i' hiT
      rw [hTNi] at hind
      have hA : cts.toArray[k]? = some cts[k] := by simp [hk]
      have hpush : (ordered.take (fpos LS i' + c)).toArray.push cts[k] =
          (ordered.take (fpos LS i' + (c + 1))).toArray := by
        rw [← hord', take_push _ _ hp, Nat.add_assoc]
      simp only [hfold, hA]
      cases hci : cts[k].cidx <;> cases hiw : cts[k].induct
      · simp only [run_bind _ _ a _ hcty, run_bind _ _ a _ htele, beq_self_eq_true, ite_true, hpush]; rfl
      · simp only [run_bind _ _ a _ (hind _ hiw), beq_self_eq_true, ite_true,
          run_bind _ _ a _ hcty, run_bind _ _ a _ htele, hpush]; rfl
      · simp only [hcidx _ hci, beq_self_eq_true, ite_true, run_bind _ _ a _ hcty,
          run_bind _ _ a _ htele, hpush]; rfl
      · simp only [hcidx _ hci, run_bind _ _ a _ (hind _ hiw), beq_self_eq_true, ite_true,
          run_bind _ _ a _ hcty, run_bind _ _ a _ htele, hpush]; rfl
    simp only [fpos_succ LS i' hi']
    rfl
  · simp only [List.getElem_zip]
    refine run_bind_exG ForInStep.done
      (fun (b : Option (RecordVerdict ⊕ List IndCtorRec × Nat) × Array IndCtorRec × Nat) =>
        ∃ w, b.1 = some (Sum.inl (RecordVerdict.invalid w))) ?_ ?_
    rotate_left
    · rintro ⟨r, arr⟩ ⟨w, hw⟩
      simp only at hw; subst hw
      exact ⟨_, ⟨w, rfl⟩, rfl⟩
    refine forIn_done_ex _ a _ _ (fun c => ((none : Option (RecordVerdict ⊕ List IndCtorRec × Nat)),
      (ordered.take (fpos LS i + c)).toArray, c)) (by simp) c hc _ ?_ ?_
    · intro c' hc'
      have hc'' : c' < LS[i].length := by omega
      obtain ⟨k, hk, hfold, hcidx, hind, cty, hcty, htele⟩ := hpre' c' hc'
      obtain ⟨hp, hord'⟩ := hord i hi c' hc'' k hfold
      have hck : cts[k]! = cts[k] := getElem!_pos cts k hk
      rw [hck] at hord'
      have hiT : i < TN.length := by omega
      have hTNi : TN[i]! = TN[i] := getElem!_pos TN i hiT
      rw [hTNi] at hind
      have hA : cts.toArray[k]? = some cts[k] := by simp [hk]
      have hpush : (ordered.take (fpos LS i + c')).toArray.push cts[k] =
          (ordered.take (fpos LS i + (c' + 1))).toArray := by
        rw [← hord', take_push _ _ hp, Nat.add_assoc]
      simp only [hfold, hA]
      cases hci : cts[k].cidx <;> cases hiw : cts[k].induct
      · simp only [run_bind _ _ a _ hcty, run_bind _ _ a _ htele, beq_self_eq_true, ite_true, hpush]; rfl
      · simp only [run_bind _ _ a _ (hind _ hiw), beq_self_eq_true, ite_true,
          run_bind _ _ a _ hcty, run_bind _ _ a _ htele, hpush]; rfl
      · simp only [hcidx _ hci, beq_self_eq_true, ite_true, run_bind _ _ a _ hcty,
          run_bind _ _ a _ htele, hpush]; rfl
      · simp only [hcidx _ hci, run_bind _ _ a _ (hind _ hiw), beq_self_eq_true, ite_true,
          run_bind _ _ a _ hcty, run_bind _ _ a _ htele, hpush]; rfl
    · -- the failing constructor
      have hiT : i < TN.length := by omega
      have hTNi : TN[i]! = TN[i] := getElem!_pos TN i hiT
      rw [hTNi] at hfail
      obtain ⟨xn, hxn⟩ := hLSr LS[i] (List.getElem_mem hi) LS[i][c] (List.getElem_mem hc)
      obtain ⟨xT, hxT⟩ := hTNr TN[i] (List.getElem_mem hiT)
      simp only [CtorFail, ctorIxOf] at hfail
      rcases hfail with hnone | ⟨k, hfold, hk, hfl⟩
      · simp only [hnone]
        refine ⟨?_, ?_, ?_⟩
        rotate_right
        rw [run_bind _ _ a _ hxn]; rfl
        all_goals exact ⟨_, rfl⟩
      have hA : cts.toArray[k]? = some cts[k] := by simp [hk]
      simp only [hfold, hA]
      rcases hfl with ⟨ci, hci, hne⟩ | ⟨hcidx, ⟨iw, iwn, hiw, hiwn, hne⟩ | ⟨hind, cty, tele, hcty, htele, hne⟩⟩
      · simp only [hci, beq_iff_eq, hne, ite_false]
        refine ⟨?_, ?_, ?_⟩
        rotate_right
        rw [run_bind _ _ a _ hxn, run_bind _ _ a _ hxT]; rfl
        all_goals exact ⟨_, rfl⟩
      · obtain ⟨xi, hxi⟩ := hRN iw iwn (name_run hiwn).1
        have hci' : ∀ ci, cts[k].cidx = some ci → (ci == c) = true := fun ci h => by simp [hcidx ci h]
        rcases hci : cts[k].cidx with _ | ci
        · simp only [hiw, run_bind _ _ a _ hiwn, beq_iff_eq, hne, ite_false]
          refine ⟨?_, ?_, ?_⟩
          rotate_right
          rw [run_bind _ _ a _ hxn, run_bind _ _ a _ hxi, run_bind _ _ a _ hxT]; rfl
          all_goals exact ⟨_, rfl⟩
        · simp only [hci' ci hci, ite_true, hiw, run_bind _ _ a _ hiwn, beq_iff_eq, hne, ite_false]
          refine ⟨?_, ?_, ?_⟩
          rotate_right
          rw [run_bind _ _ a _ hxn, run_bind _ _ a _ hxi, run_bind _ _ a _ hxT]; rfl
          all_goals exact ⟨_, rfl⟩
      · have hci' : ∀ ci, cts[k].cidx = some ci → (ci == c) = true := fun ci h => by simp [hcidx ci h]
        have hiw' : ∀ iw, cts[k].induct = some iw → (TN[i] == TN[i]) = true := fun _ _ => by simp
        have htl : (nPd + cts[k].numFields == tele) = false := by simp [hne]
        rcases hci : cts[k].cidx with _ | ci <;> rcases hiw : cts[k].induct with _ | iw
        · simp only [run_bind _ _ a _ hcty, run_bind _ _ a _ htele, beq_iff_eq, hne, ite_false]
          refine ⟨?_, ?_, ?_⟩
          rotate_right
          rw [run_bind _ _ a _ hxn]; rfl
          all_goals exact ⟨_, rfl⟩
        · simp only [run_bind _ _ a _ (hind iw hiw), ite_true,
            run_bind _ _ a _ hcty, run_bind _ _ a _ htele, beq_iff_eq, hne, ite_false]
          refine ⟨?_, ?_, ?_⟩
          rotate_right
          rw [run_bind _ _ a _ hxn]; rfl
          all_goals exact ⟨_, rfl⟩
        · simp only [hci' ci hci, ite_true, run_bind _ _ a _ hcty, run_bind _ _ a _ htele, beq_iff_eq, hne, ite_false]
          refine ⟨?_, ?_, ?_⟩
          rotate_right
          rw [run_bind _ _ a _ hxn]; rfl
          all_goals exact ⟨_, rfl⟩
        · simp only [hci' ci hci, ite_true, run_bind _ _ a _ (hind iw hiw),
            run_bind _ _ a _ hcty, run_bind _ _ a _ htele, beq_iff_eq, hne, ite_false]
          refine ⟨?_, ?_, ?_⟩
          rotate_right
          rw [run_bind _ _ a _ hxn]; rfl
          all_goals exact ⟨_, rfl⟩

theorem validateIndD_orderFail_cls {st : StateD} {a : AState} {tys : List IndTypeRec}
    {cts : List IndCtorRec} {rcs : List IndRecRec} {TN : List NIdx} {TT : List EIdx}
    {LS : List (List NIdx)} {CN : List NIdx} {nPd fuel : Nat} (hV : VPre st a tys cts TN TT LS CN nPd)
    (hnd : LS.flatten.Nodup) (hlen : LS.flatten.length = cts.length) (hzl : TN.length = LS.length)
    (hRN : NamesRead st a) (hfuel : a.store.nodeCount + 1 = fuel)
    (hO : OrderFail st a cts CN TN LS nPd fuel) :
    ∃ v, (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = .ok (.inl v, a) ∧
      twinCls v.toError = 1 := by
  obtain ⟨z, ⟨w, rfl⟩, h⟩ := validateIndD_orderFail (rcs := rcs) hV hnd hlen hzl hRN hfuel hO
  exact ⟨_, h, twinCls_invalid w⟩

/-! ## The L side: the error models -/

l_model viCtor_specE (p : Prog) (hf : p.lookup "vi_ctor" = some viCtor)
  fns [hf ↦ viCtorE] grind [arena_grind] extra [L.Arena.ld64_rdW_specE] simp [] errors
l_model viOrderIn_specE (p : Prog) (hf : p.lookup "vi_order_in" = some viOrderIn)
  fns [hf ↦ viOrderInE] grind [arena_grind] extra [L.Arena.ld64_rdW_specE] simp [] errors
l_model viOrderGo_specE (p : Prog) (hf : p.lookup "vi_order_go" = some viOrderGo)
  fns [hf ↦ viOrderGoE] grind [arena_grind] extra [L.Arena.ld64_rdW_specE] simp [] errors
l_model viOrder_specE (p : Prog) (hf : p.lookup "vi_order" = some viOrder)
  fns [hf ↦ viOrderE] grind [arena_grind] extra [L.Arena.ld64_rdW_specE] simp [] errors
l_model viNpGo_specE (p : Prog) (hf : p.lookup "vi_np_go" = some viNpGo)
  fns [hf ↦ viNpGoE] grind [arena_grind] extra [L.Arena.ld64_rdW_specE] errors
l_model viNparams_specE (p : Prog) (hf : p.lookup "vi_nparams" = some viNparams)
  fns [hf ↦ viNparamsE] grind [arena_grind] extra [L.Arena.ld64_rdW_specE] errors

/-! ## The L side: `vi_np_go`, `vi_nparams` -/

/-- **`vi_np_go`'s error model**: an error of class `≠ 0` (the decline) means some type record
from `j` on has `numParams ≠ d`. -/
theorem npGoE_claim {b : ByteArray} {m : Mem} {tys : List IndTypeRec} {to tn d : Word}
    (hL : ListF (TyF b m) m 11 to.toNat tys) (htn : tn.toNat = tys.length)
    (hto : to.toNat + 11 * tys.length < 2 ^ 63) (p : Prog) :
    ∀ n j e, viNpGoE p n m to tn d j = .error e → e.cls ≠ 0 →
      e = .abort R_INDUCTIVE_BLOCK_WHOSE ∧
      ∃ k, ∃ hk : k < tys.length, j.toNat ≤ k ∧ tys[k].numParams ≠ d.toNat := by
  intro n
  induction n with
  | zero =>
    intro j e h hk
    exfalso; apply hk
    have : viNpGoE p 0 m to tn d j = .error .outOfFuel := by simp [viNpGoE]
    rw [this] at h; cases h; simp
  | succ n ih =>
    intro j e h hk
    by_cases hle : tn ≤ j
    · rw [viNpGoE.arm1 p n m to tn d j hle] at h; cases h
    have hj := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
    have hj1 := wsucc j tn (UInt64.not_le.mp hle)
    have hix : (to + 11 * j + 10).toNat = to.toNat + 11 * j.toNat + 10 := widx _ _ _ _ (by simp; omega)
    by_cases h0 : rdW (m.arr64 IFR) (to + 11 * j + 10) = d
    · rw [viNpGoE.arm2 p n m to tn d j hle h0] at h
      cases h1 : viNpGoE p n m to tn d (j + 1) with
      | error ε =>
        rw [h1, viNpGoE.k_vi_np_go.none] at h
        cases h
        obtain ⟨he, k, hk', hjk, hne⟩ := ih _ _ h1 hk
        exact ⟨he, k, hk', by rw [hj1] at hjk; omega, hne⟩
      | ok q =>
        obtain ⟨u, m₁⟩ := q
        rw [h1, viNpGoE.k_vi_np_go.arm1] at h; cases h
    · rw [viNpGoE.abort1 p n m to tn d j hle h0] at h
      cases h
      refine ⟨rfl, j.toNat, by omega, Nat.le_refl _, ?_⟩
      rw [wd_eq, hix] at h0
      obtain ⟨-, -, -, -, -, h10⟩ := hL.2.2 j.toNat (by omega)
      intro he
      apply h0
      apply UInt64.toNat_inj.mp
      rw [h10.1, he]

/-- **`vi_nparams`' error claim**: a failing call of class `≠ 0` means the type records disagree
on `numParams` (the twin's decline). -/
theorem viNparams_fail (p : Prog) (hp : p.lookup "vi_nparams" = some viNparams)
    (hpg : p.lookup "vi_np_go" = some viNpGo) (n : Nat) (m : Mem)
    {b : ByteArray} {tys : List IndTypeRec} {to tn : Word}
    (hL : ListF (TyF b m) m 11 to.toNat tys) (htn : tn.toNat = tys.length)
    (hto : to.toNat + 11 * tys.length < 2 ^ 63)
    (e : Err) (hc : callE p (n + 1) "vi_nparams" [to, tn] m = .error e) (hk : e.cls ≠ 0) :
    e = .abort R_INDUCTIVE_BLOCK_WHOSE ∧ ((tys.map fun x => x.numParams).all fun x =>
      x == (tys.map fun x => x.numParams).head?.getD 0) = false := by
  have hW := triple_of_callE_err (viNparams_specE p hp (n + 1) ⟨m, Locals.init []⟩ to tn) hc
    (Err.code_ne_of_cls hk)
  by_cases h0 : tn = 0
  · rw [viNparamsE.arm1 p n m to tn h0] at hW; cases hW
  rw [viNparamsE.arm2 p n m to tn h0] at hW
  cases h1 : callE p n "vi_np_go" [to, tn, rdW (m.arr64 IFR) (to + 10), 0] m with
  | ok q => obtain ⟨r, m₁⟩ := q; rw [h1, viNparamsE.k_vi_np_go.arm1] at hW; cases hW
  | error e1 =>
  rw [h1, viNparamsE.k_vi_np_go.none] at hW
  cases hW
  have hW1 := triple_of_callE_err (viNpGo_specE p hpg n ⟨m, Locals.init []⟩ to tn _ 0) h1
    (Err.code_ne_of_cls hk)
  obtain ⟨he, k, hk', -, hne⟩ := npGoE_claim hL htn hto p n 0 _ hW1 hk
  refine ⟨he, ?_⟩
  have h0' : 0 < tys.length := by
    have : tn.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e))
    omega
  have hix : (to + 10).toNat = to.toNat + 10 := widx2 _ _ (by simp; omega)
  obtain ⟨-, -, -, -, -, h10⟩ := hL.2.2 0 h0'
  simp only [Nat.mul_zero, Nat.add_zero] at h10
  have hd : (rdW (m.arr64 IFR) (to + 10)).toNat = tys[0].numParams := by rw [wd_eq, hix, h10.1]
  rw [hd] at hne
  rw [List.all_eq_false]
  refine ⟨tys[k].numParams, List.mem_map.mpr ⟨tys[k], List.getElem_mem hk', rfl⟩, ?_⟩
  cases tys with
  | nil => simp at h0'
  | cons t ts => simpa using hne

/-- **`vi_nparams`' error refinement** (after `vi_unsafe` ran: no unsafe type): the twin's
`numParams` decline. -/
theorem viNparams_refinesE (p : Prog) (hp : p.lookup "vi_nparams" = some viNparams)
    (hpg : p.lookup "vi_np_go" = some viNpGo) (n : Nat) (m : Mem)
    {b : ByteArray} {tys : List IndTypeRec} {to tn : Word}
    (hL : ListF (TyF b m) m 11 to.toNat tys) (htn : tn.toNat = tys.length)
    (hto : to.toNat + 11 * tys.length < 2 ^ 63) (st : StateD) (cts : List IndCtorRec)
    (rcs : List IndRecRec) (a : AState) (hsafe : (tys.any fun x => x.isUnsafe) = false)
    (e : Err) (hc : callE p (n + 1) "vi_nparams" [to, tn] m = .error e) :
    L.Front.VerdictClaimL (ConRon.Arena.Frontend.validateIndD st tys cts rcs) a e := fun hk => by
  obtain ⟨he, hall⟩ := viNparams_fail p hp hpg n m hL htn hto e hc hk
  obtain ⟨v, hv, hcl⟩ := validateIndD_np (st := st) (a := a) (cts := cts) (rcs := rcs) hsafe hall
  refine .inr ⟨v, a, hv, ?_⟩
  rw [hcl, he]; decide

/-! ## The L side: `vi_ctor` -/

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

/-- A name absent from the constructor names has no entry in the twin's `ctorIx`. -/
theorem ctorIx_none (l : List NIdx) (n : NIdx) (h : ∀ k (hk : k < l.length), l[k] ≠ n) :
    (ctorIxOf l)[n]? = none := by
  unfold ctorIxOf
  rw [ctorIx_last.ctorIx_absent l ∅ 0 n h]
  simp

/-- The callees of `vi_ctor`, outside the verdict closure. -/
def CtorNV (p : Prog) : Prop := NVCls p ["ifl_find_last", "name_get", "expr_get", "ind_pi_tele_len"]

/-- **`vi_ctor`'s error model claims the twin's constructor check fails** (`CtorFail`), under the
hypotheses of `ctorW_twin` and the type's name handle below `2^32`. -/
theorem ctorE_fail {p : Prog} (hL : IndApplyLookups p) (hnv : CtorNV p)
    {b : ByteArray} {n : Nat} {m : Mem} {a : AState} {st : StateD} (hR : ArenaR m a)
    (hD : StateDR m st) {cts : List IndCtorRec} {nn j tt np fuel cno cn co : Word}
    (hCt : ListF (CtF b m) m 10 co.toNat cts) (hcn : cn.toNat = cts.length)
    (hCN : ∀ k, k < cts.length → (wd m IFL (cno.toNat + k)).toNat < 2 ^ 32)
    (hcnb : cno.toNat + cts.length < 2 ^ 63) (hnn : nn.toNat < 2 ^ 32) (htt : tt.toNat < 2 ^ 32)
    (hnp : np.toNat < 10 ^ 18) (hco : co.toNat + 10 * cts.length < 2 ^ 63)
    (e : Err) (h : viCtorE p (n + 1) m nn j tt np fuel cno cn co = .error e) (hk : e.cls ≠ 0) :
    CtorFail st a cts (islice m cno.toNat cts.length) (decI nn) j.toNat (decI tt) np.toNat fuel.toNat := by
  rw [viCtorE.arm1] at h
  cases h1 : callE p n "ifl_find_last" [cno, nn, cn] m with
  | error e1 =>
    rw [h1, viCtorE.k_ifl_find_last.none] at h; cases h
    exact absurd (hnv.cls (by simp) h1) hk
  | ok q =>
  obtain ⟨r, m1⟩ := q
  rw [h1] at h
  obtain ⟨s1, hs1, hs1', hfl⟩ := triple_of_callE (findLast_spec p hL n ⟨m, Locals.init []⟩ cno nn cn) h1
  have hm1 : m1 = m := by rw [← hs1, hs1']
  subst hm1
  simp only at hfl
  by_cases hf0 : r.headD 0 = 0
  · left
    apply ctorIx_none
    intro k' hk' he
    rw [islice_length] at hk'
    rw [islice_get] at he
    exact findLastW_zero n m1 cno nn cn _ _ hfl (by omega) hf0 k' (by omega)
      (decI_inj' _ _ (hCN k' hk') hnn he)
  obtain ⟨f1, f2, f3⟩ := findLastW_facts n m1 cno nn cn _ _ hfl (by omega) hf0
  rw [hcn] at f1 f3
  obtain ⟨k, hkdef⟩ : ∃ k, r.tail.headD 0 = k := ⟨_, rfl⟩
  rw [hkdef] at f1 f2 f3
  have hkk : (UInt64.ofNat k.toNat) = k := UInt64.ofNat_toNat
  obtain ⟨-, -, hct⟩ := hCt
  obtain ⟨⟨c1, -, c3⟩, c4, c5, c6, c7⟩ := hct k.toNat f1
  have hk10 : (10 : Word).toNat = 10 := rfl
  have ix : ∀ s : Word, s.toNat < 10 → (co + 10 * k + s).toNat = co.toNat + 10 * k.toNat + s.toNat := by
    intro s hs; rw [widx _ _ _ _ (by rw [hk10]; omega), hk10]
  have rd : ∀ s : Word, s.toNat < 10 → rdW (m1.arr64 IFR) (co + 10 * k + s) = wd m1 IFR (co.toNat + 10 * k.toNat + s.toNat) := by
    intro s hs; rw [wd_eq, ix s hs]
  have hfold : (ctorIxOf (islice (k := .name) m1 cno.toNat cts.length))[(decI nn : NIdx)]? = some k.toNat := by
    have := ctorIx_last (islice m1 cno.toNat cts.length) ∅ 0 (decI nn) k.toNat
      (by rw [islice_length]; exact f1) (by rw [islice_get, f2]) (fun k' h1 h2 => by
        rw [islice_get]; intro e
        rw [islice_length] at h2
        exact f3 k' h1 h2 (decI_inj' _ _ (hCN k' h2) hnn e))
    simpa [ctorIxOf] using this
  right
  refine ⟨k.toNat, hfold, f1, ?_⟩
  -- the `cidx` check
  by_cases g6 : rdW (m1.arr64 IFR) (co + 10 * k + 6) ≠ 0 ∧ rdW (m1.arr64 IFR) (co + 10 * k + 7) ≠ j
  · left
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
  right
  have hcidx' : ∀ ci, cts[k.toNat].cidx = some ci → ci = j.toNat := by
    intro ci hci
    rw [hci] at c6
    obtain ⟨e1, e2⟩ := c6
    have : rdW (m1.arr64 IFR) (co + 10 * k + 6) ≠ 0 := by
      rw [rd 6 (by decide)]; simp only [show (6 : Word).toNat = 6 from rfl]; rw [e1]; decide
    have hj : rdW (m1.arr64 IFR) (co + 10 * k + 7) = j := Classical.byContradiction fun hne => g6 ⟨this, hne⟩
    rw [rd 7 (by decide)] at hj
    simp only [show (7 : Word).toNat = 7 from rfl, show co.toNat + 10 * k.toNat + 7 = co.toNat + 10 * k.toNat + 6 + 1 by omega] at hj
    rw [← e2.1, hj]
  refine ⟨hcidx', ?_⟩
  have hJ : viCtorE.k_ifl_find_last p n j tt np fuel co (.ok (r, m1)) =
      viCtorE.j1 p n tt np fuel (co + 10 * k) m1 := by
    rw [← hkdef] at g6 ⊢
    by_cases g : rdW (m1.arr64 IFR) (co + 10 * r.tail.headD 0 + 6) = 0
    · exact viCtorE.k_ifl_find_last.arm2 p n j tt np fuel co r m1 hf0 g
    · exact viCtorE.k_ifl_find_last.arm1 p n j tt np fuel co r m1 hf0 g
        (Classical.byContradiction fun hne => g6 ⟨g, hne⟩)
  rw [hJ] at h
  -- the telescope, after the `induct` check
  have hJ2 : ∀ e', viCtorE.j2 p n np fuel (co + 10 * k) m1 = .error e' → e'.cls ≠ 0 →
      ∃ cty tele, (getDeclD st cts[k.toNat].cv.type).run a = .ok (cty, a) ∧
        (ConRon.Arena.Frontend.indPiTeleLen fuel.toNat cty).run a = .ok (tele, a) ∧
        np.toNat + cts[k.toNat].numFields ≠ tele := by
    intro e' h2 hk2
    rw [viCtorE.j2.arm1] at h2
    cases h3 : callE p n "expr_get" [rdW (m1.arr64 IFR) (co + 10 * k + 2)] m1 with
    | error e3 =>
      rw [h3, viCtorE.k_expr_get.none] at h2; cases h2
      exact absurd (hnv.cls (by simp) h3) hk2
    | ok q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, viCtorE.k_expr_get.arm1] at h2
    obtain ⟨s3, hs3, hs3', hok3, hr3⟩ :=
      triple_of_callE (exprGet_spec p hL.decl.expr n ⟨m1, Locals.init []⟩ _) h3
    have hm3 : m3 = m1 := by rw [← hs3, hs3']
    subst hm3
    have hlk : lkW m3 EID (rdW (m3.arr64 IFR) (co + 10 * k + 2)) =
        some (tblW m3 EID (rdW (m3.arr64 IFR) (co + 10 * k + 2))) := by
      unfold lkW; simp only at hok3; rw [ite_eq_left hok3]
    have hexp := (lkW_expr hD a hlk).1
    rw [rd 2 (by decide)] at hexp
    simp only [show (2 : Word).toNat = 2 from rfl] at hexp
    rw [c3.1] at hexp
    subst hr3
    simp only [List.headD_cons] at h2
    cases h4 : callE p n "ind_pi_tele_len" [fuel, tblW m3 EID (rdW (m3.arr64 IFR) (co + 10 * k + 2))] m3 with
    | error e4 =>
      rw [h4, viCtorE.k_ind_pi_tele_len.none] at h2; cases h2
      exact absurd (hnv.cls (by simp) h4) hk2
    | ok q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [h4] at h2
    obtain ⟨s4, hs4, hs4', ht4⟩ := triple_of_callE (tele_spec p hL n ⟨m3, Locals.init []⟩ _ _) h4
    have hm4 : m4 = m3 := by rw [← hs4, hs4']
    subst hm4
    simp only at ht4
    obtain ⟨t1, -⟩ := teleW_ok m4 a hR n fuel _ _ ht4
    rw [rd 2 (by decide)] at t1
    simp only [show (2 : Word).toNat = 2 from rfl] at t1
    by_cases g4 : np + rdW (m4.arr64 IFR) (co + 10 * k + 4) = r4.headD 0
    · rw [viCtorE.k_ind_pi_tele_len.arm1 p np _ r4 m4 g4] at h2; cases h2
    refine ⟨_, _, hexp, t1, fun hne => g4 ?_⟩
    rw [rd 4 (by decide)]
    simp only [show (4 : Word).toNat = 4 from rfl]
    apply UInt64.toNat_inj.mp
    rw [widx2 _ _ (by rw [c4.1]; have := c4.2; omega), c4.1, hne]
  by_cases g8 : rdW (m1.arr64 IFR) (co + 10 * k + 8) = 0
  · -- no `induct`
    rw [viCtorE.j1.arm2 p n tt np fuel _ m1 g8] at h
    have hnone : cts[k.toNat].induct = none := by
      cases hiw : cts[k.toNat].induct with
      | none => rfl
      | some iw =>
        rw [hiw] at c7
        rw [rd 8 (by decide)] at g8
        simp only [show (8 : Word).toNat = 8 from rfl] at g8
        rw [c7.1] at g8; exact absurd g8 (by decide)
    exact .inr ⟨fun iw hiw => (by rw [hnone] at hiw; cases hiw), hJ2 e h hk⟩
  rw [viCtorE.j1.arm1 p n tt np fuel _ m1 g8] at h
  cases h5 : callE p n "name_get" [rdW (m1.arr64 IFR) (co + 10 * k + 9)] m1 with
  | error e5 =>
    rw [h5, viCtorE.k_name_get.none] at h; cases h
    exact absurd (hnv.cls (by simp) h5) hk
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5] at h
  obtain ⟨s5, hs5, hs5', hok5, hr5⟩ :=
    triple_of_callE (nameGet_spec p hL.decl.expr.front n ⟨m1, Locals.init []⟩ _) h5
  have hm5 : m5 = m1 := by rw [← hs5, hs5']
  subst hm5
  simp only at hok5
  have hlk : lkW m5 NID (rdW (m5.arr64 IFR) (co + 10 * k + 9)) =
      some (tblW m5 NID (rdW (m5.arr64 IFR) (co + 10 * k + 9))) := by
    unfold lkW; rw [ite_eq_left hok5]
  obtain ⟨hnm, hx32⟩ := lkW_name hD a hlk
  rw [rd 9 (by decide)] at hnm hx32
  simp only [show (9 : Word).toNat = 9 from rfl] at hnm hx32
  have hsome : ∃ iw, cts[k.toNat].induct = some iw ∧
      (wd m5 IFR (co.toNat + 10 * k.toNat + 9)).toNat = iw := by
    cases hiw : cts[k.toNat].induct with
    | none =>
      rw [hiw] at c7
      exfalso; apply g8
      rw [rd 8 (by decide)]; exact c7
    | some iw =>
      rw [hiw] at c7
      refine ⟨iw, rfl, ?_⟩
      rw [show co.toNat + 10 * k.toNat + 9 = co.toNat + 10 * k.toNat + 8 + 1 by omega]; exact c7.2.1
  obtain ⟨iw, hiw, hiwv⟩ := hsome
  rw [hiwv] at hnm
  subst hr5
  by_cases gt : tblW m5 NID (wd m5 IFR (co.toNat + 10 * k.toNat + 9)) = tt
  · rw [viCtorE.k_name_get.arm1 p n tt np fuel _ _ m5 (by rw [rd 9 (by decide)]; simpa using gt)] at h
    refine .inr ⟨fun iw' hiw' => ?_, hJ2 e h hk⟩
    rw [hiw] at hiw'; cases hiw'
    rw [hnm, gt]
  · rw [viCtorE.k_name_get.abort1 p n tt np fuel _ _ m5 (by rw [rd 9 (by decide)]; simpa using gt)] at h
    exact .inl ⟨iw, _, hiw, hnm, fun he => gt (decI_inj' _ _ hx32 htt he)⟩

/-- `vi_ctor`'s errors of class `≠ 0` are its own aborts, all of class `1` (rejects). -/
theorem ctorE_cls {p : Prog} (hnv : CtorNV p) (n : Nat) (m : Mem) (nn j tt np fuel cno cn co : Word)
    (e : Err) (h : viCtorE p n m nn j tt np fuel cno cn co = .error e) (hk : e.cls ≠ 0) : e.cls = 1 := by
  cases n with
  | zero => rw [viCtorE.eq_1] at h; cases h; exact absurd Err.cls_outOfFuel hk
  | succ n =>
  rw [viCtorE.arm1] at h
  cases h1 : callE p n "ifl_find_last" [cno, nn, cn] m with
  | error e1 => rw [h1, viCtorE.k_ifl_find_last.none] at h; cases h; exact absurd (hnv.cls (by simp) h1) hk
  | ok q =>
  obtain ⟨r, m1⟩ := q
  rw [h1, viCtorE.k_ifl_find_last.eq_2] at h
  have hj2 : ∀ c m', viCtorE.j2 p n np fuel c m' = .error e → e.cls = 1 := by
    intro c m' h2
    rw [viCtorE.j2.arm1] at h2
    cases h3 : callE p n "expr_get" [rdW (m'.arr64 IFR) (c + 2)] m' with
    | error e3 => rw [h3, viCtorE.k_expr_get.none] at h2; cases h2; exact absurd (hnv.cls (by simp) h3) hk
    | ok q3 =>
    rw [h3, viCtorE.k_expr_get.arm1] at h2
    cases h4 : callE p n "ind_pi_tele_len" [fuel, q3.1.headD 0] q3.2 with
    | error e4 => rw [h4, viCtorE.k_ind_pi_tele_len.none] at h2; cases h2; exact absurd (hnv.cls (by simp) h4) hk
    | ok q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [h4, viCtorE.k_ind_pi_tele_len.eq_2] at h2
    split at h2
    · cases h2; decide
    · cases h2
  have hj1 : ∀ c m', viCtorE.j1 p n tt np fuel c m' = .error e → e.cls = 1 := by
    intro c m' h2
    rw [viCtorE.j1.eq_1] at h2
    split at h2
    · cases h5 : callE p n "name_get" [rdW (m'.arr64 IFR) (c + 9)] m' with
      | error e5 => rw [h5, viCtorE.k_name_get.none] at h2; cases h2; exact absurd (hnv.cls (by simp) h5) hk
      | ok q5 =>
      obtain ⟨r5, m5⟩ := q5
      rw [h5, viCtorE.k_name_get.eq_2] at h2
      split at h2
      · cases h2; decide
      · exact hj2 _ _ h2
    · exact hj2 _ _ h2
  split at h
  · cases h; decide
  split at h
  · split at h
    · cases h; decide
    · exact hj1 _ _ h
  · exact hj1 _ _ h

/-! ## The L side: `vi_order_in`, `vi_order_go`, `vi_order` -/

section orderE
variable {p : Prog} (hL : IndApplyLookups p) (hnv : CtorNV p)
  {b : ByteArray} {m₀ : Mem} {a : AState} {st : StateD} (hR : ArenaR m₀ a)
  (hD : StateDR m₀ st) {cts : List IndCtorRec} {fo cno co cn fuel np oo : Word}
  (hCt : ListF (CtF b m₀) m₀ 10 co.toNat cts) (hcn : cn.toNat = cts.length)
  (hCN : ∀ k, k < cts.length → (wd m₀ IFL (cno.toNat + k)).toNat < 2 ^ 32)
  (hcnB : cno.toNat + cts.length ≤ oo.toNat) (hnp : np.toNat < 10 ^ 18)
  (hco : co.toNat + 10 * cts.length < 2 ^ 63) (hsz : oo.toNat + cts.length ≤ (m₀.arr64 IFL).size)
  (hsz63 : (m₀.arr64 IFL).size < 2 ^ 63)
include hL hnv hR hD hCt hcn hCN hcnB hnp hco hsz hsz63

/-- **`vi_order_in`'s error model**: an error of class `≠ 0` stops at a constructor `c` of the
type (from `jj` on): the ones before pass the twin's checks, `c` fails them. -/
theorem orderInE_fail : ∀ (n : Nat) (m : Mem) (t tt jj pos : Word) (e : Err),
    viOrderInE p n m fo cno co cn fuel np oo t tt jj pos = .error e → e.cls ≠ 0 →
    IOnly oo.toNat m₀ m → t.toNat + 4 < 2 ^ 63 → jj.toNat ≤ (wd m₀ IFR (t.toNat + 4)).toNat →
    pos.toNat + ((wd m₀ IFR (t.toNat + 4)).toNat - jj.toNat) ≤ cts.length →
    (∀ c, jj.toNat ≤ c → c < (wd m₀ IFR (t.toNat + 4)).toNat →
      fo.toNat + pos.toNat + (c - jj.toNat) < oo.toNat ∧
      (wd m₀ IFL (fo.toNat + pos.toNat + (c - jj.toNat))).toNat < 2 ^ 32) →
    tt.toNat < 2 ^ 32 →
    e.cls = 1 ∧ ∃ c, jj.toNat ≤ c ∧ c < (wd m₀ IFR (t.toNat + 4)).toNat ∧
      (∀ c', jj.toNat ≤ c' → c' < c → ∃ k,
        CtorOK st a cts (islice m₀ cno.toNat cts.length)
          (decI (wd m₀ IFL (fo.toNat + pos.toNat + (c' - jj.toNat)))) c' (decI tt) np.toNat fuel.toNat k) ∧
      CtorFail st a cts (islice m₀ cno.toNat cts.length)
        (decI (wd m₀ IFL (fo.toNat + pos.toNat + (c - jj.toNat)))) c (decI tt) np.toNat fuel.toNat := by
  intro n
  induction n with
  | zero =>
    intro m t tt jj pos e h hk
    rw [viOrderInE.eq_1] at h; cases h; exact absurd Err.cls_outOfFuel hk
  | succ n ih =>
    intro m t tt jj pos e h hk hI ht hjj hpos hfo htt
    have h4 : rdW (m.arr64 IFR) (t + 4) = wd m₀ IFR (t.toNat + 4) := by
      rw [wd_eq, widx2 _ _ (by simp; omega), hI.wdR]; rfl
    by_cases hle : rdW (m.arr64 IFR) (t + 4) ≤ jj
    · rw [viOrderInE.arm1 p n m _ _ _ _ _ _ _ _ _ _ _ hle] at h; cases h
    rw [viOrderInE.arm2 p n m _ _ _ _ _ _ _ _ _ _ _ hle] at h
    rw [h4] at hle
    have hlt' := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
    obtain ⟨hf1, hf2⟩ := hfo jj.toNat (Nat.le_refl _) hlt'
    simp only [Nat.sub_self, Nat.add_zero] at hf1 hf2
    have hfp : (fo + pos).toNat = fo.toNat + pos.toNat := widx2 _ _ (by omega)
    have hop : (oo + pos).toNat = oo.toNat + pos.toNat := widx2 _ _ (by omega)
    have hnn : rdW (m.arr64 IFL) (fo + pos) = wd m₀ IFL (fo.toNat + pos.toNat) := by
      rw [wd_eq, hfp, hI.2 _ hf1]
    rw [hnn] at h
    have hCN' : ∀ k, k < cts.length → (wd m IFL (cno.toNat + k)).toNat < 2 ^ 32 := fun k hk => by
      rw [hI.2 _ (by omega)]; exact hCN k hk
    cases h1 : callE p n "vi_ctor" [wd m₀ IFL (fo.toNat + pos.toNat), jj, tt, np, fuel, cno, cn, co] m with
    | error e1 =>
      rw [h1, viOrderInE.k_vi_ctor.none] at h; cases h
      have hW := triple_of_callE_err (viCtor_specE p hL.vi_ctor n ⟨m, Locals.init []⟩ _ _ _ _ _ _ _ _) h1
        (Err.code_ne_of_cls hk)
      cases n with
      | zero => rw [viCtorE.eq_1] at hW; cases hW; exact absurd Err.cls_outOfFuel hk
      | succ n' =>
      have hfail := ctorE_fail hL hnv (hI.arena hR) (hI.stateDR hD) (hI.listF hCt) hcn hCN' (by omega)
        hf2 htt hnp hco _ hW hk
      rw [hI.islice _ _ hcnB] at hfail
      refine ⟨ctorE_cls hnv _ _ _ _ _ _ _ _ _ _ _ hW hk, jj.toNat, Nat.le_refl _, hlt',
        fun c' h1 h2 => by omega, ?_⟩
      simpa using hfail
    | ok q =>
    obtain ⟨r, m1⟩ := q
    rw [h1, viOrderInE.k_vi_ctor.arm1] at h
    obtain ⟨s1, hs1, hs1', hc⟩ := triple_of_callE (ctor_spec p hL n ⟨m, Locals.init []⟩ _ _ _ _ _ _ _ _) h1
    have hm1 : m1 = m := by rw [← hs1, hs1']
    subst hm1
    simp only at hc
    obtain ⟨k, hk', hck, hfold, hcidx, hind, htele⟩ := ctorW_twin (hI.arena hR) (hI.stateDR hD)
      (hI.listF hCt) hcn hCN' (by omega) hf2 hnp hco hc
    rw [hI.islice _ _ hcnB] at hfold
    have hj1 := wsucc jj _ (UInt64.not_le.mp hle)
    have hp1 : (pos + 1).toNat = pos.toNat + 1 := widx2 _ _ (by simp; omega)
    obtain ⟨hcl, c, y1, y2, y3, y4⟩ := ih (m1.set64 IFL (oo + pos) (r.headD 0)) t tt (jj + 1) (pos + 1) e h hk
      (hI.set _ _ (by rw [hop]; omega)) ht (by rw [hj1]; omega) (by rw [hj1, hp1]; omega)
      (fun c' h1 h2 => by
        rw [hj1] at h1; rw [hp1, hj1]
        have := hfo c' (by omega) h2
        rw [show fo.toNat + (pos.toNat + 1) + (c' - (jj.toNat + 1)) = fo.toNat + pos.toNat + (c' - jj.toNat) by omega]
        exact this) htt
    simp only [hj1, hp1] at y1 y3 y4
    refine ⟨hcl, c, by omega, y2, fun c' h1 h2 => ?_, ?_⟩
    · by_cases hcj : c' = jj.toNat
      · subst hcj
        simp only [Nat.sub_self, Nat.add_zero]
        exact ⟨k, hk', hfold, hcidx, hind, htele⟩
      · obtain ⟨k', e2⟩ := y3 c' (by omega) h2
        rw [show fo.toNat + (pos.toNat + 1) + (c' - (jj.toNat + 1)) = fo.toNat + pos.toNat + (c' - jj.toNat) by omega] at e2
        exact ⟨k', e2⟩
    · rw [show fo.toNat + (pos.toNat + 1) + (c - (jj.toNat + 1)) = fo.toNat + pos.toNat + (c - jj.toNat) by omega] at y4
      exact y4


variable {to tn tyn : Word} (hto : to.toNat + 11 * tn.toNat < 2 ^ 63) (htyn : tyn.toNat + tn.toNat ≤ oo.toNat)
  (hfo : ∀ p, p < psum m₀ to tn.toNat → fo.toNat + p < oo.toNat ∧ (wd m₀ IFL (fo.toNat + p)).toNat < 2 ^ 32)
  (hps : psum m₀ to tn.toNat ≤ cts.length)
  (htt : ∀ k, k < tn.toNat → (wd m₀ IFL (tyn.toNat + k)).toNat < 2 ^ 32)
include hto htyn hfo hps htt

/-- **`vi_order_go`'s error model**: an error of class `≠ 0` stops at constructor `c` of type
`k` (from `ti` on): every constructor before passes the twin's checks, `c` fails them. -/
theorem orderGoE_fail : ∀ (n : Nat) (m : Mem) (ti pos : Word) (e : Err),
    viOrderGoE p n m to tn tyn fo cno co cn fuel np oo ti pos = .error e → e.cls ≠ 0 →
    IOnly oo.toNat m₀ m → ti ≤ tn → pos.toNat = psum m₀ to ti.toNat →
    e.cls = 1 ∧ ∃ k, ti.toNat ≤ k ∧ k < tn.toNat ∧ ∃ c, c < cntF m₀ to k ∧
      (∀ k', ti.toNat ≤ k' → k' < k → ∀ c', c' < cntF m₀ to k' → ∃ kk,
        CtorOK st a cts (islice m₀ cno.toNat cts.length) (decI (wd m₀ IFL (fo.toNat + psum m₀ to k' + c')))
          c' (decI (wd m₀ IFL (tyn.toNat + k'))) np.toNat fuel.toNat kk) ∧
      (∀ c', c' < c → ∃ kk,
        CtorOK st a cts (islice m₀ cno.toNat cts.length) (decI (wd m₀ IFL (fo.toNat + psum m₀ to k + c')))
          c' (decI (wd m₀ IFL (tyn.toNat + k))) np.toNat fuel.toNat kk) ∧
      CtorFail st a cts (islice m₀ cno.toNat cts.length) (decI (wd m₀ IFL (fo.toNat + psum m₀ to k + c)))
        c (decI (wd m₀ IFL (tyn.toNat + k))) np.toNat fuel.toNat := by
  intro n
  induction n with
  | zero =>
    intro m ti pos e h hk
    rw [viOrderGoE.eq_1] at h; cases h; exact absurd Err.cls_outOfFuel hk
  | succ n ih =>
    intro m ti pos e h hk hI hti hpos
    by_cases hle : tn ≤ ti
    · rw [viOrderGoE.arm1 p n m _ _ _ _ _ _ _ _ _ _ _ _ hle] at h; cases h
    rw [viOrderGoE.arm2 p n m _ _ _ _ _ _ _ _ _ _ _ _ hle] at h
    have hlt' := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
    have hti1 := wsucc ti tn (UInt64.not_le.mp hle)
    have htt' : rdW (m.arr64 IFL) (tyn + ti) = wd m₀ IFL (tyn.toNat + ti.toNat) := by
      rw [wd_eq, widx2 _ _ (by omega), hI.2 _ (by omega)]
    rw [htt'] at h
    have hmono := psum_mono m₀ to (ti.toNat + 1) tn.toNat (by omega)
    rw [psum_succ] at hmono
    have ht : (to + 11 * ti).toNat = to.toNat + 11 * ti.toNat := by
      have := widx to 11 ti 0 (by simp; omega); simpa using this
    have hc4 : wd m₀ IFR ((to + 11 * ti).toNat + 4) = wd m₀ IFR (to.toNat + 11 * ti.toNat + 4) := by rw [ht]
    have hfo' : ∀ c, (0 : Word).toNat ≤ c → c < (wd m₀ IFR ((to + 11 * ti).toNat + 4)).toNat →
        fo.toNat + pos.toNat + (c - (0 : Word).toNat) < oo.toNat ∧
        (wd m₀ IFL (fo.toNat + pos.toNat + (c - (0 : Word).toNat))).toNat < 2 ^ 32 := fun c h1 h2 => by
      simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero] at h2 ⊢
      rw [hc4] at h2
      have := hfo (pos.toNat + c) (by rw [hpos]; unfold cntF at hmono; omega)
      rw [Nat.add_assoc]; exact this
    have hpos' : pos.toNat + ((wd m₀ IFR ((to + 11 * ti).toNat + 4)).toNat - (0 : Word).toNat) ≤ cts.length := by
      simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero]; rw [hc4]; unfold cntF at hmono; omega
    cases h1 : callE p n "vi_order_in" [fo, cno, co, cn, fuel, np, oo, to + 11 * ti,
        wd m₀ IFL (tyn.toNat + ti.toNat), 0, pos] m with
    | error e1 =>
      rw [h1, viOrderGoE.k_vi_order_in.none] at h; cases h
      have hW := triple_of_callE_err (viOrderIn_specE p hL.vi_order_in n ⟨m, Locals.init []⟩ _ _ _ _ _ _ _ _ _ _ _) h1
        (Err.code_ne_of_cls hk)
      obtain ⟨hcl, c, -, c2, c3, c4⟩ := orderInE_fail hL hnv hR hD hCt hcn hCN hcnB hnp hco hsz hsz63 n m
        (to + 11 * ti) _ 0 pos _ hW hk hI (by rw [ht]; omega) (by simp) hpos' hfo' (htt _ hlt')
      simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero] at c2 c3 c4
      rw [hc4] at c2
      refine ⟨hcl, ti.toNat, Nat.le_refl _, hlt', c, c2, fun k' h1 h2 => by omega, fun c' hc' => ?_, ?_⟩
      · obtain ⟨kk, hkk⟩ := c3 c' (Nat.zero_le _) hc'
        rw [← hpos]; exact ⟨kk, hkk⟩
      · rw [← hpos]; exact c4
    | ok q =>
    obtain ⟨r, m₁⟩ := q
    rw [h1, viOrderGoE.k_vi_order_in.arm1] at h
    obtain ⟨s1, hs1, -, hin⟩ := triple_of_callE (orderIn_spec p hL n ⟨m, Locals.init []⟩ _ _ _ _ _ _ _ _ _ _ _) h1
    rw [hs1] at hin
    simp only at hin
    obtain ⟨x1, x2, -, x4⟩ := orderInW_twin hR hD hCt hcn hCN hcnB hnp hco hsz hsz63 n m m₁
      (to + 11 * ti) _ 0 pos _ hin hI (by rw [ht]; omega) (by simp) hpos' hfo'
    simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero] at x2
    rw [hc4] at x2
    cases h2 : viOrderGoE p n m₁ to tn tyn fo cno co cn fuel np oo (ti + 1) (r.headD 0) with
    | ok q2 => obtain ⟨u, m₂⟩ := q2; rw [h2, viOrderGoE.k_vi_order_go.arm1] at h; cases h
    | error e2 =>
    rw [h2, viOrderGoE.k_vi_order_go.none] at h; cases h
    obtain ⟨hcl, k, y1, y2, c, y3, y4, y5, y6⟩ := ih m₁ (ti + 1) (r.headD 0) _ h2 hk x1
      (UInt64.le_iff_toNat_le.mpr (by rw [hti1]; exact hlt')) (by rw [hti1, psum_succ, x2, hpos]; rfl)
    rw [hti1] at y1 y4
    refine ⟨hcl, k, by omega, y2, c, y3, fun k' h1 h2 c' hc' => ?_, y5, y6⟩
    by_cases hk' : k' = ti.toNat
    · subst hk'
      obtain ⟨kk, e2⟩ := x4 c' (Nat.zero_le _) (by rw [hc4]; exact hc')
      simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero] at e2
      rw [← hpos]; exact ⟨kk, e2.2⟩
    · exact y4 k' (by omega) h2 c' hc'

end orderE

/-- **Where `vi_order` stops**, on the memory `m` it was called from: constructor `c` of type `k`
fails the twin's checks, every constructor before passes them (`orderW_twin`'s form). -/
def OrderFailW (st : StateD) (a : AState) (cts : List IndCtorRec) (m : Mem) (to tn tyn fo cno : Word)
    (np fuel : Nat) : Prop :=
  ∃ k, k < tn.toNat ∧ ∃ c, c < cntF m to k ∧
    (∀ k', k' < k → ∀ c', c' < cntF m to k' → ∃ kk,
      CtorOK st a cts (islice m cno.toNat cts.length) (decI (wd m IFL (fo.toNat + psum m to k' + c')))
        c' (decI (wd m IFL (tyn.toNat + k'))) np fuel kk) ∧
    (∀ c', c' < c → ∃ kk,
      CtorOK st a cts (islice m cno.toNat cts.length) (decI (wd m IFL (fo.toNat + psum m to k + c')))
        c' (decI (wd m IFL (tyn.toNat + k))) np fuel kk) ∧
    CtorFail st a cts (islice m cno.toNat cts.length) (decI (wd m IFL (fo.toNat + psum m to k + c)))
      c (decI (wd m IFL (tyn.toNat + k))) np fuel

/-- The callees of `vi_order` and below, outside the verdict closure. -/
def OrderNV (p : Prog) : Prop :=
  NVCls p ["ifl_find_last", "name_get", "expr_get", "ind_pi_tele_len", "ifl_alloc"]

theorem OrderNV.ctor {p : Prog} (h : OrderNV p) : CtorNV p := fun g hg => h g (by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
  rcases hg with rfl | rfl | rfl | rfl <;> simp)

/-- **`vi_order`'s error claim**: a failing call of class `≠ 0` stops the twin's constructor order
(`OrderFailW`). Hypotheses of `orderW_twin`, and the type name handles below `2^32`. -/
theorem orderE_fail {p : Prog} (hL : IndApplyLookups p) (hnv : OrderNV p)
    {b : ByteArray} {n : Nat} {m : Mem} {a : AState} {st : StateD}
    (hR : ArenaR m a) (hD : StateDR m st) {cts : List IndCtorRec}
    {to tn tyn fo cno co cn fuel np : Word} (hT : TopOK m)
    (hCt : ListF (CtF b m) m 10 co.toNat cts) (hcn : cn.toNat = cts.length)
    (hCN : ∀ k, k < cts.length → (wd m IFL (cno.toNat + k)).toNat < 2 ^ 32)
    (hcnB : cno.toNat + cts.length ≤ topN m IFL + 1) (hnp : np.toNat < 10 ^ 18)
    (hco : co.toNat + 10 * cts.length < 2 ^ 63) (h1 : 1 ≤ cno.toNat ∧ 1 ≤ fo.toNat ∧ 1 ≤ tyn.toNat)
    (hto : to.toNat + 11 * tn.toNat < 2 ^ 63) (htyn : tyn.toNat + tn.toNat ≤ topN m IFL + 1)
    (hfo : ∀ p, p < psum m to tn.toNat → fo.toNat + p ≤ topN m IFL ∧ (wd m IFL (fo.toNat + p)).toNat < 2 ^ 32)
    (hps : psum m to tn.toNat ≤ cts.length)
    (htt : ∀ k, k < tn.toNat → (wd m IFL (tyn.toNat + k)).toNat < 2 ^ 32)
    (e : Err) (hc : callE p (n + 1) "vi_order" [to, tn, tyn, fo, cno, co, cn, fuel, np] m = .error e)
    (hk : e.cls ≠ 0) :
    e.cls = 1 ∧ OrderFailW st a cts m to tn tyn fo cno np.toNat fuel.toNat := by
  obtain ⟨h1a, h1b, h1c⟩ := h1
  have h := triple_of_callE_err (viOrder_specE p hL.vi_order (n + 1) ⟨m, Locals.init []⟩ _ _ _ _ _ _ _ _ _) hc
    (Err.code_ne_of_cls hk)
  rw [viOrderE.arm1] at h
  cases ha : callE p n "ifl_alloc" [cn] m with
  | error e1 =>
    rw [ha, viOrderE.k_ifl_alloc.none] at h; cases h
    exact absurd (hnv.cls (by simp) ha) hk
  | ok q =>
  obtain ⟨r, m₁⟩ := q
  rw [ha, viOrderE.k_ifl_alloc.arm1] at h
  obtain ⟨s1, hs1, -, hal⟩ := triple_of_callE (iflAlloc_spec p hL.ifl_alloc n ⟨m, Locals.init []⟩ cn) ha
  rw [hs1] at hal
  simp only at hal
  cases hg : callE p n "vi_order_go" [to, tn, tyn, fo, cno, co, cn, fuel, np, r.headD 0, 0, 0] m₁ with
  | ok q2 => obtain ⟨u, m₂⟩ := q2; rw [hg, viOrderE.k_vi_order_go.arm1] at h; cases h
  | error e2 =>
  rw [hg, viOrderE.k_vi_order_go.none] at h; cases h
  have hW := triple_of_callE_err (viOrderGo_specE p hL.vi_order_go n ⟨m₁, Locals.init []⟩ _ _ _ _ _ _ _ _ _ _ _ _) hg
    (Err.code_ne_of_cls hk)
  obtain ⟨a1, a2, a3, a4⟩ := allocW_ok hT hal
  obtain ⟨-, -, a5, -, -⟩ := allocW_factsA (by decide) hT.1 (by have := hT.1; have := hT.2; omega) hal
  rw [hcn] at a4 a5
  have hR₁ : ArenaR m₁ a := ArenaR.frame_ext [IFL, LH] [192] (by decide) (by simp) m m₁ a1.frame a hR
  have hD₁ : StateDR m₁ st := hD.frame a1.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  have hps₁ := psum_congr a1.ifr to
  have hkeep : ∀ i, 1 ≤ i → i ≤ topN m IFL → wd m₁ IFL i = wd m IFL i := a1.keep
  have hCN₁ : ∀ k, k < cts.length → (wd m₁ IFL (cno.toNat + k)).toNat < 2 ^ 32 := fun k hk => by
    rw [hkeep _ (by omega) (by omega)]; exact hCN k hk
  have hCt₁ : ListF (CtF b m₁) m₁ 10 co.toNat cts := hCt.ext a1 (fun _ _ x => x.ext a1)
  rw [← hps₁] at hfo hps
  have hcnt : ∀ k, cntF m₁ to k = cntF m to k := fun k => by simp only [cntF, wd, a1.ifr]
  obtain ⟨hcl, k, -, hk', c, hc', g1, g2, g3⟩ := orderGoE_fail hL hnv.ctor hR₁ hD₁ hCt₁ hcn hCN₁ (by omega) hnp hco
    (by rw [a1.size]; omega) a2.1 hto (by omega)
    (fun p hp => by
      obtain ⟨f1, f2⟩ := hfo p hp
      exact ⟨by omega, by rw [hkeep _ (by omega) f1]; exact f2⟩) hps
    (fun k hk => by rw [hkeep _ (by omega) (by omega)]; exact htt k hk) n m₁ 0 0 _ hW hk
    (IOnly.refl _ _) (UInt64.le_iff_toNat_le.mpr (Nat.zero_le _)) (by simp [psum])
  have hsl := islice_ext (k := .name) a1 cno.toNat cts.length (by omega) hcnB
  have hpos : ∀ k' c', k' < tn.toNat → c' < cntF m to k' → psum m to k' + c' < psum m to tn.toNat := by
    intro k' c' h1 h2
    have := psum_mono m to (k' + 1) tn.toNat (by omega)
    rw [psum_succ] at this; omega
  have hfo' := fun p hp => (hfo p (by rw [hps₁]; exact hp)).1
  simp only [hps₁, hcnt] at g1 g2 g3 hc'
  refine ⟨hcl, k, hk', c, hc', fun k' hk'' c' hc'' => ?_, fun c' hc'' => ?_, ?_⟩
  · obtain ⟨kk, e2⟩ := g1 k' (Nat.zero_le _) hk'' c' hc''
    rw [hsl, hkeep _ (by omega) (by have := hfo' _ (hpos k' c' (by omega) hc''); omega), hkeep _ (by omega) (by omega)] at e2
    exact ⟨kk, e2⟩
  · obtain ⟨kk, e2⟩ := g2 c' hc''
    rw [hsl, hkeep _ (by omega) (by have := hfo' _ (hpos k c' hk' (by omega)); omega), hkeep _ (by omega) (by omega)] at e2
    exact ⟨kk, e2⟩
  · rw [hsl, hkeep _ (by omega) (by have := hfo' _ (hpos k c hk' hc'); omega), hkeep _ (by omega) (by omega)] at g3
    exact g3

/-- **`OrderFailW` is the twin's `OrderFail`** on the lists the validation's lookups returned: the
type names `TN`, the listed constructor names `LS` (flattened at `fo`), the constructor names `CN`
(as `validateW_twin` relates them). -/
theorem orderFail_of_W {st : StateD} {a : AState} {cts : List IndCtorRec} {m : Mem}
    {to tn tyn fo cno : Word} {np fuel : Nat} {TN : List NIdx} {LS : List (List NIdx)} {CN : List NIdx}
    (hO : OrderFailW st a cts m to tn tyn fo cno np fuel) (hlen : LS.length = tn.toNat)
    (hps : ∀ i, i ≤ LS.length → psum m to i = fpos LS i)
    (hcnt : ∀ k (hk : k < LS.length), cntF m to k = LS[k].length)
    (hnn : ∀ i (hi : i < LS.length) c (hc : c < LS[i].length),
      LS[i][c] = decI (wd m IFL (fo.toNat + (fpos LS i + c))))
    (hTN : ∀ i, i < LS.length → TN[i]! = decI (wd m IFL (tyn.toNat + i)))
    (hCN : CN = islice m cno.toNat cts.length) :
    OrderFail st a cts CN TN LS np fuel := by
  obtain ⟨k, hk, c, hc, g1, g2, g3⟩ := hO
  subst hCN
  have hk' : k < LS.length := by omega
  rw [hcnt k hk'] at hc
  refine ⟨k, hk', c, hc, fun i' hi' hik c' hc' => ?_, fun c' hc' => ?_, ?_⟩
  · obtain ⟨kk, e⟩ := g1 i' hik c' (by rw [hcnt i' hi']; exact hc')
    rw [hps i' (by omega), Nat.add_assoc, ← hnn i' hi' c' hc', ← hTN i' hi'] at e
    exact ⟨kk, e⟩
  · obtain ⟨kk, e⟩ := g2 c' hc'
    rw [hps k (by omega), Nat.add_assoc, ← hnn k hk' c' (by omega), ← hTN k hk'] at e
    exact ⟨kk, e⟩
  · rw [hps k (by omega), Nat.add_assoc, ← hnn k hk' c hc, ← hTN k hk'] at g3
    exact g3

end L.Front.Ind
