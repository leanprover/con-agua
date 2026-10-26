import ConAgua.Verdict.FrontE

/-!
# Error refinements of `vi_rec_idx`, `vi_rec`, `vi_recs_go`, `vi_recs` (lane `verdicts-b`, helper `f2`)

The recursor checks of `validateIndD` (its last loop). Every abort of these functions is an
`.invalid` of the twin (class `1`): a recursor record whose counts, `k` or indices disagree with
the block's.

* Twin side (no L): `RecFail`, one recursor record failing the twin's checks (after the earlier
  checks of the same record passed), `RecsFail`, the first failing record of the list (the ones
  before it `RecOK`); `validateIndD_recsFail`: from the facts of the validation before its
  recursor loop (`VFactsR`) and `RecsFail`, `validateIndD` returns an `.invalid` verdict.
* L side: the error models (`l_model … errors`), `recIdxE_claim`, `recE_claim`, `recsGoE_claim`,
  `recsE_claim` (a class-`≠ 0` error means the twin's checks fail there), and the refinements
  `viRecs_refinesE` etc. at a failing `callE`.
-/

open L.Arena
open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option experimental.vcgen true

namespace L.Front.Ind

/-! ## The twin side -/

/-- The names the parse state binds read back (the messages' `readName`). -/
def NamesReadR (st : StateD) (a : AState) : Prop :=
  ∀ i h, (st.name i).run a = .ok (h, a) → ∃ x, (readName h).run a = .ok (x, a)

/-- The prefix of a `str` name node reads back. -/
def ViewReadR (a : AState) : Prop :=
  ∀ h T s, (viewN h).run a = .ok (.str T s, a) → ∃ x, (readName T).run a = .ok (x, a)

/-- **One recursor record fails the twin's checks**: its name is bound, and the first of its
checks that fails is the parameter count, the motive count, the minor count, `k` against
`kExpected?`, or (named `T.rec`) the indices at some type named `T`, the earlier types of that
loop passing. -/
def RecFail (st : StateD) (a : AState) (TN : List NIdx) (TT : List EIdx) (nPd nTypes nCtors : Nat)
    (KE : Option Bool) (fuel : Nat) (rc : IndRecRec) : Prop :=
  ∃ rn, (st.name rc.cv.name).run a = .ok (rn, a) ∧
    (rc.numParams ≠ nPd ∨ rc.numParams = nPd ∧ (rc.numMotives ≠ nTypes ∨ rc.numMotives = nTypes ∧
      (rc.numMinors ≠ nCtors ∨ rc.numMinors = nCtors ∧
        ((∃ kE, KE = some kE ∧ rc.k ≠ kE) ∨ (∀ kE, KE = some kE → rc.k = kE) ∧
          ∃ T, (viewN rn).run a = .ok (.str T "rec", a) ∧
            ∃ j, ∃ hj : j < TN.length, ∃ hj' : j < TT.length,
              (∀ j' (h1 : j' < j), TN[j'] = T → ∃ o,
                (piSortTeleLen? fuel (TT[j']'(by omega))).run a = .ok (o, a) ∧
                ∀ k, o = some k → nPd + rc.numIndices = k) ∧
              TN[j] = T ∧ ∃ k, (piSortTeleLen? fuel TT[j]).run a = .ok (some k, a) ∧
                nPd + rc.numIndices ≠ k))))

/-- **The recursor loop stops at record `j`**: the records before it pass, record `j` fails. -/
def RecsFail (st : StateD) (a : AState) (TN : List NIdx) (TT : List EIdx) (nPd nTypes nCtors : Nat)
    (KE : Option Bool) (fuel : Nat) (rcs : List IndRecRec) : Prop :=
  ∃ j, ∃ hj : j < rcs.length, (∀ i (hi : i < j), RecOK st a TN TT nPd nTypes nCtors KE fuel
    (rcs[i]'(by omega))) ∧ RecFail st a TN TT nPd nTypes nCtors KE fuel rcs[j]

/-- The facts of the validation before its recursor loop: `VFacts` without the recursors. -/
abbrev VFactsR (st : StateD) (a : AState) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (TN : List NIdx) (TT : List EIdx) (LS : List (List NIdx)) (CN : List NIdx) (fuel nPd : Nat)
    (ordered : List IndCtorRec) (KE : Option Bool) : Prop :=
  VFacts st a tys cts [] TN TT LS CN fuel nPd ordered KE

/-- A read-only `forIn` that yields before index `j` and is done at `j`. -/
theorem forIn_done {α β : Type} (f : α → β → AM (ForInStep β)) (a : AState) :
    ∀ (xs : List α) (S : Nat → β) (j : Nat) (hj : j < xs.length) (b : β),
    (∀ i (hi : i < j), (f (xs[i]'(by omega)) (S i)).run a = .ok (.yield (S (i + 1)), a)) →
    (f xs[j] (S j)).run a = .ok (.done b, a) →
    (forIn xs (S 0) f).run a = .ok (b, a)
  | [], _, _, hj, _, _, _ => absurd hj (by simp)
  | x :: xs, S, j, hj, b, h, hd => by
    rw [List.forIn_cons]
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero] at hd
      rw [run_bind _ _ a _ hd]; rfl
    | succ j =>
      have h0 := h 0 (by omega)
      simp only [List.getElem_cons_zero] at h0
      rw [run_bind _ _ a _ h0]
      have := forIn_done f a xs (fun i => S (i + 1)) j (by simp at hj; omega) b
        (fun i hi => by have := h (i + 1) (by omega); simpa using this) (by simpa using hd)
      simpa using this

theorem forIn_done' {α β : Type} (f : α → β → AM (ForInStep β)) (a : AState) (xs : List α)
    (init : β) (S : Nat → β) (h0 : S 0 = init) (j : Nat) (hj : j < xs.length) (b : β)
    (h : ∀ i (hi : i < j), (f (xs[i]'(by omega)) (S i)).run a = .ok (.yield (S (i + 1)), a))
    (hd : (f xs[j] (S j)).run a = .ok (.done b, a)) :
    (forIn xs init f).run a = .ok (b, a) := by
  subst h0; exact forIn_done f a xs S j hj b h hd


/-- A bind of read-only runs, through existentials. -/
theorem run_bind_ex {α β : Type} {x : AM α} {f : α → AM β} {a : AState} {P : α → Prop}
    {Q : β → Prop} (hx : ∃ y, x.run a = .ok (y, a) ∧ P y)
    (hf : ∀ y, P y → ∃ z, (f y).run a = .ok (z, a) ∧ Q z) :
    ∃ z, (x >>= f).run a = .ok (z, a) ∧ Q z := by
  obtain ⟨y, h1, h2⟩ := hx
  obtain ⟨z, h3, h4⟩ := hf y h2
  exact ⟨z, by rw [run_bind _ _ a _ h1]; exact h3, h4⟩

/-- `forIn_done'`, through existentials. -/
theorem forIn_done_ex {α β : Type} (f : α → β → AM (ForInStep β)) (a : AState) (xs : List α)
    (init : β) (S : Nat → β) (h0 : S 0 = init) (j : Nat) (hj : j < xs.length) (P : β → Prop)
    (h : ∀ i (hi : i < j), (f (xs[i]'(by omega)) (S i)).run a = .ok (.yield (S (i + 1)), a))
    (hd : ∃ z, (f xs[j] (S j)).run a = .ok (z, a) ∧ ∃ b, z = .done b ∧ P b) :
    ∃ b, (forIn xs init f).run a = .ok (b, a) ∧ P b := by
  obtain ⟨z, h1, b, rfl, h2⟩ := hd
  exact ⟨b, forIn_done' f a xs init S h0 j hj b h h1, h2⟩

theorem exInv_of {α : Type} {X : AM (RecordVerdict ⊕ α)} {a : AState}
    (h : ∃ z, X.run a = .ok (z, a) ∧ ∃ w, z = .inl (.invalid w)) :
    ∃ w, X.run a = .ok (.inl (.invalid w), a) := by
  obtain ⟨z, h1, w, rfl⟩ := h; exact ⟨w, h1⟩

/-- The verdict a failing recursor loop leaves in its state. -/
def LoopInv (s : Option (RecordVerdict ⊕ List IndCtorRec × Nat) × Unit) : Prop :=
  ∃ w, s.1 = some (.inl (.invalid w))

set_option hygiene false in
/-- The recursor loop of `validateIndD`, once `kExpected?` is `KE`, stopping at the failing record. -/
macro "recsfail_tac" : tactic => `(tactic| (
  rw [hnest, if_neg Bool.false_ne_true]
  obtain ⟨j, hj, hpre, rn, hrn, hfc⟩ := hF
  apply exInv_of
  refine run_bind_ex (P := LoopInv) ?_ ?_
  rotate_left
  · rintro ⟨o, u⟩ ⟨w, hw⟩
    try simp only at hw
    subst hw
    exact ⟨_, rfl, w, rfl⟩
  refine forIn_done_ex _ a _ _
    (fun _ => ((none : Option (RecordVerdict ⊕ List IndCtorRec × Nat)), ())) rfl j hj _ ?rstep ?rdone
  case rstep =>
    intro j hj
    obtain ⟨rn, hrn, h1, h2, h3, hk, v, hv, hin⟩ := hpre j hj
    rw [run_bind _ _ a _ hrn]
    simp only [h1, h2, h3, beq_self_eq_true, if_true]
    rcases hK : KE with _ | kE
    all_goals (try simp only [hk _ hK, beq_self_eq_true, if_true])
    all_goals
      rw [run_bind _ _ a _ hv]
      rcases v with _ | ⟨T, sv⟩ | ⟨T, nv⟩
      · rfl
      · by_cases hsv : sv = "rec"
        · subst hsv
          try simp only []
          rw [run_bind _ _ a _ (forIn_yield' _ a _ _
            (fun _ => ((none : Option (RecordVerdict ⊕ List IndCtorRec × Nat)), ())) rfl ?_)]
          · rfl
          · intro j' hj'
            simp only [List.getElem_zip]
            have hj2 := hj'
            rw [List.length_zip] at hj2
            have hj1 : j' < TN.length := by omega
            by_cases hT : TN[j']'hj1 = T
            · obtain ⟨o, ho, hon⟩ := hin T rfl j' (by omega) (by omega) hT
              simp only [hT, beq_self_eq_true, if_true]
              rw [run_bind _ _ a _ ho]
              cases o with
              | none => rfl
              | some x => simp only [hon x rfl, beq_self_eq_true, if_true]; rfl
            · simp only [hT, beq_iff_eq, if_false]
              rfl
        · split
          · rename_i heq
            simp only [NNodeView.str.injEq] at heq
            exact absurd heq.2 hsv
          · rfl
      · rfl
  case rdone =>
    try simp only []
    rw [run_bind _ _ a _ hrn]
    obtain ⟨xr, hxr⟩ := hRN _ _ hrn
    rcases hfc with hp | ⟨hp, hm | ⟨hm, hn | ⟨hn, hk | ⟨hk, T, hv, jj, hjj, hjj', hpre2, hT, kk, hk2, hne⟩⟩⟩⟩
    · rw [if_neg (by simpa using hp)]
      rw [run_bind _ _ a _ hxr]; exact ⟨_, rfl, _, rfl, _, rfl⟩
    · rw [if_pos (by simpa using hp), if_neg (by simpa using hm)]
      rw [run_bind _ _ a _ hxr]; exact ⟨_, rfl, _, rfl, _, rfl⟩
    · rw [if_pos (by simpa using hp), if_pos (by simpa using hm), if_neg (by simpa using hn)]
      rw [run_bind _ _ a _ hxr]; exact ⟨_, rfl, _, rfl, _, rfl⟩
    · rw [if_pos (by simpa using hp), if_pos (by simpa using hm), if_pos (by simpa using hn)]
      obtain ⟨kE, hKE', hne⟩ := hk
      subst hKE'
      try simp only []
      rw [if_neg (by simpa using hne)]
      rw [run_bind _ _ a _ hxr]; exact ⟨_, rfl, _, rfl, _, rfl⟩
    · rw [if_pos (by simpa using hp), if_pos (by simpa using hm), if_pos (by simpa using hn)]
      obtain ⟨xT, hxT⟩ := hRV _ _ _ hv
      rcases hK : KE with _ | kE
      all_goals (try simp only [hk _ hK, beq_self_eq_true, if_true])
      all_goals
        rw [run_bind _ _ a _ hv]
        try simp only []
        refine run_bind_ex (P := LoopInv) ?_ ?_
        rotate_left
        · rintro ⟨o, u⟩ ⟨w, hw⟩
          try simp only at hw
          subst hw
          exact ⟨_, rfl, _, rfl, ⟨w, rfl⟩⟩
        refine forIn_done_ex _ a _ _
          (fun _ => ((none : Option (RecordVerdict ⊕ List IndCtorRec × Nat)), ())) rfl jj
          (by rw [List.length_zip]; omega) _ ?_ ?_
        · intro j' hj'
          simp only [List.getElem_zip]
          by_cases hT' : TN[j']'(by omega) = T
          · obtain ⟨o, ho, hon⟩ := hpre2 j' hj' hT'
            simp only [hT', beq_self_eq_true, if_true]
            rw [run_bind _ _ a _ ho]
            cases o with
            | none => rfl
            | some x => simp only [hon x rfl, beq_self_eq_true, if_true]; rfl
          · simp only [hT', beq_iff_eq, if_false]
            rfl
        · simp only [List.getElem_zip, hT, beq_self_eq_true, if_true]
          rw [run_bind _ _ a _ hk2]
          try simp only []
          rw [if_neg (by simpa using hne)]
          rw [run_bind _ _ a _ hxr, run_bind _ _ a _ hxT]
          exact ⟨_, rfl, _, rfl, _, rfl⟩))

theorem validateIndD_recsFail {st : StateD} {a : AState} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} {TN : List NIdx} {TT : List EIdx} {LS : List (List NIdx)} {CN : List NIdx}
    {fuel nPd : Nat} {ordered : List IndCtorRec} {KE : Option Bool}
    (hV : VFactsR st a tys cts TN TT LS CN fuel nPd ordered KE)
    (hnest : (tys.any fun x => x.numNested != 0) = false)
    (hF : RecsFail st a TN TT nPd tys.length ordered.length KE fuel rcs)
    (hRN : NamesReadR st a) (hRV : ViewReadR a) :
    ∃ w, (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = .ok (.inl (.invalid w), a) := by
  unfold ConRon.Arena.Frontend.validateIndD
  simp only [hV.safe, Bool.false_eq_true, if_false]
  rw [← hV.np1, if_pos hV.np2]
  rw [run_bind _ _ a _ hV.tn, run_bind _ _ a _ hV.tt, run_bind _ _ a _ hV.ls, run_bind _ _ a _ hV.cn]
  rw [if_pos hV.nodup]
  simp only [hV.flen, beq_self_eq_true, if_true]
  rw [run_bind _ _ a _ (storeFuel_run a), hV.hfuel]
  rw [run_bind _ _ a _ (forIn_yield' _ a _ _ (fun i => ((none : Option (RecordVerdict ⊕ List IndCtorRec × Nat)),
    (ordered.take (fpos LS i)).toArray)) ?h0 ?hstep)]
  case h0 => simp [fpos]
  case hstep =>
    intro i hi
    simp only [List.getElem_zip]
    rw [run_bind _ _ a _ (forIn_yield' _ a _ _ (fun c => ((none : Option (RecordVerdict ⊕ List IndCtorRec × Nat)),
      (ordered.take (fpos LS i + c)).toArray, c)) ?i0 ?istep)]
    case i0 => simp
    case istep =>
      intro c hc
      have hi' : i < LS.length := by simp at hi; omega
      have hiT : i < TN.length := by simp at hi; omega
      obtain ⟨k, hp, hord, hk, hfold, hcidx, hind, cty, hcty, htele⟩ := hV.order i hi' c hc
      have hck : cts[k]! = cts[k] := getElem!_pos cts k hk
      rw [hck] at hord
      have hTNi : TN[i]! = TN[i] := getElem!_pos TN i hiT
      rw [hTNi] at hind
      have hA : cts.toArray[k]? = some cts[k] := by simp [hk]
      have hpush : (ordered.take (fpos LS i + c)).toArray.push cts[k] =
          (ordered.take (fpos LS i + (c + 1))).toArray := by
        rw [← hord, take_push _ _ hp, Nat.add_assoc]
      simp only [hfold, hA]
      cases hci : cts[k].cidx <;> cases hiw : cts[k].induct
      · simp only [run_bind _ _ a _ hcty, run_bind _ _ a _ htele, beq_self_eq_true, if_true, hpush]; rfl
      · simp only [run_bind _ _ a _ (hind _ hiw), beq_self_eq_true, if_true,
          run_bind _ _ a _ hcty, run_bind _ _ a _ htele, hpush]; rfl
      · simp only [hcidx _ hci, beq_self_eq_true, if_true, run_bind _ _ a _ hcty,
          run_bind _ _ a _ htele, hpush]; rfl
      · simp only [hcidx _ hci, run_bind _ _ a _ (hind _ hiw), beq_self_eq_true, if_true,
          run_bind _ _ a _ hcty, run_bind _ _ a _ htele, hpush]; rfl
    have hi' : i < LS.length := by simp at hi; omega
    simp only [fpos_succ LS i hi']
    rfl
  have hzl : (TN.zip LS).length = LS.length := by simp [hV.tnlen, hV.lslen]
  have htk : ordered.take (fpos LS LS.length) = ordered := by
    rw [fpos_full, hV.flen, ← hV.ordlen, List.take_length]
  simp only [hzl, List.toList_toArray, htk]
  split
  · rename_i ty hd c
    obtain ⟨r, v, hr, hv, hnone, hsort⟩ := hV.kyes ty hd c rfl rfl rfl
    rw [run_bind _ _ a _ hr, run_bind _ _ a _ hv]
    rcases hvs : v with _ | _ | ⟨s⟩ | _ | _ | _ | _ | _ | _ | _
    case sort =>
      obtain ⟨L, hL, hKE⟩ := hsort s hvs
      simp only []
      rw [run_bind _ _ a _ hL, ← hKE]
      simp only [pure_bind]
      recsfail_tac
    all_goals
      have hKE : KE = none := hnone (fun s' h' => by rw [hvs] at h'; cases h')
      simp only []
      rw [← hKE]
      simp only [pure_bind]
      recsfail_tac
  · rename_i hne
    have hKE : KE = some false := hV.kno (fun ⟨h1, h2⟩ => by
      obtain ⟨ty, hty⟩ : ∃ ty, TT = [ty] := by
        cases hT : TT with
        | nil => rw [hT] at h1; simp at h1
        | cons x xs => cases xs with
          | nil => exact ⟨x, rfl⟩
          | cons _ _ => rw [hT] at h1; simp at h1
      obtain ⟨hd, hls⟩ : ∃ hd, LS = [[hd]] := by
        cases hL : LS with
        | nil => rw [hL] at h2; simp at h2
        | cons l ls => cases ls with
          | nil => cases l with
            | nil => rw [hL] at h2; simp at h2
            | cons x xs => cases xs with
              | nil => exact ⟨x, rfl⟩
              | cons _ _ => rw [hL] at h2; simp at h2
          | cons _ _ => rw [hL] at h2; simp at h2
      have hol : ordered.length = 1 := by
        rw [hV.ordlen, ← hV.flen, hls]; rfl
      obtain ⟨c, hc⟩ : ∃ c, ordered = [c] := by
        cases ho : ordered with
        | nil => rw [ho] at hol; simp at hol
        | cons x xs => cases xs with
          | nil => exact ⟨x, rfl⟩
          | cons _ _ => rw [ho] at hol; simp at hol
      exact hne ty hd c hty hls hc)
    rw [← hKE]
    simp only [pure_bind]
    recsfail_tac


/-! ## The L side: the error models -/

l_model recIdx_specE (p : Prog) (hf : p.lookup "vi_rec_idx" = some viRecIdx)
  fns [hf ↦ recIdxE] grind [arena_grind] extra [L.Arena.ld64_rdW_specE] errors
l_model rec_specE (p : Prog) (hf : p.lookup "vi_rec" = some viRec)
  fns [hf ↦ recE] grind [arena_grind] extra [L.Arena.ld64_rdW_specE] heartbeats 1000000 simp [] errors
l_model recsGo_specE (p : Prog) (hf : p.lookup "vi_recs_go" = some viRecsGo)
  fns [hf ↦ recsGoE] grind [arena_grind] extra [L.Arena.ld64_rdW_specE] simp [] errors
l_model recs_specE (p : Prog) (hf : p.lookup "vi_recs" = some viRecs)
  fns [hf ↦ recsE] grind [arena_grind] extra [L.Arena.ld64_rdW_specE] simp [] errors

/-- The callees of the recursor checks outside the verdict closure. -/
abbrev recsNV : List FnName := ["name_get", "name_rec_pre", "pi_sort_tele_len", "vi_nested"]

/-- **`vi_rec_idx`'s error model**: a class-`≠ 0` error is the indices check failing at the
first type `k ≥ j` named `T` whose telescope disagrees, the earlier ones named `T` agreeing. -/
theorem recIdxE_claim {p : Prog} (hL : IndApplyLookups p) (hnv : NVCls p recsNV) {m : Mem}
    {a : AState} (hR : ArenaR m a) {T ni np tn tyn tyt fuel : Word}
    (hnp : np.toNat < 10 ^ 18) (hni : ni.toNat < 10 ^ 18) (hb : tyn.toNat + tn.toNat ≤ 2 ^ 63)
    (hb' : tyt.toNat + tn.toNat ≤ 2 ^ 63) :
    ∀ n j e, recIdxE p n m T ni np tn tyn tyt fuel j = .error e → e.cls ≠ 0 →
      e = .abort R_RECURSOR_DECLARES_INDICES ∧
      ∃ k, j.toNat ≤ k ∧ k < tn.toNat ∧ wd m IFL (tyn.toNat + k) = T ∧
        (∀ k', j.toNat ≤ k' → k' < k → wd m IFL (tyn.toNat + k') = T → ∃ o,
          (piSortTeleLen? fuel.toNat (decE (wd m IFL (tyt.toNat + k')))).run a = .ok (o, a) ∧
            ∀ x, o = some x → np.toNat + ni.toNat = x) ∧
        ∃ x, (piSortTeleLen? fuel.toNat (decE (wd m IFL (tyt.toNat + k)))).run a = .ok (some x, a) ∧
          np.toNat + ni.toNat ≠ x := by
  intro n
  induction n with
  | zero =>
    intro j e h hk
    rw [recIdxE.eq_1] at h; cases h; exact absurd (by simp [Err.cls]) hk
  | succ n ih =>
    intro j e h hk
    by_cases hle : tn ≤ j
    · rw [recIdxE.arm1 p n m T ni np tn tyn tyt fuel j hle] at h; cases h
    have hjn := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
    have hj1 := wsucc j tn (UInt64.not_le.mp hle)
    have ex1 : rdW (m.arr64 IFL) (tyn + j) = wd m IFL (tyn.toNat + j.toNat) := by
      rw [wd_eq, widx2 _ _ (by omega)]
    have ex2 : rdW (m.arr64 IFL) (tyt + j) = wd m IFL (tyt.toNat + j.toNat) := by
      rw [wd_eq, widx2 _ _ (by omega)]
    -- the rest of the loop failing
    have hrest : ∀ m₁, m₁ = m → recIdxE.j1 p n T ni np tn tyn tyt fuel j m₁ = .error e →
        (wd m IFL (tyn.toNat + j.toNat) = T → ∃ o,
          (piSortTeleLen? fuel.toNat (decE (wd m IFL (tyt.toNat + j.toNat)))).run a = .ok (o, a) ∧
            ∀ x, o = some x → np.toNat + ni.toNat = x) →
        e = .abort R_RECURSOR_DECLARES_INDICES ∧
        ∃ k, j.toNat ≤ k ∧ k < tn.toNat ∧ wd m IFL (tyn.toNat + k) = T ∧
          (∀ k', j.toNat ≤ k' → k' < k → wd m IFL (tyn.toNat + k') = T → ∃ o,
            (piSortTeleLen? fuel.toNat (decE (wd m IFL (tyt.toNat + k')))).run a = .ok (o, a) ∧
              ∀ x, o = some x → np.toNat + ni.toNat = x) ∧
          ∃ x, (piSortTeleLen? fuel.toNat (decE (wd m IFL (tyt.toNat + k)))).run a = .ok (some x, a) ∧
            np.toNat + ni.toNat ≠ x := by
      intro m₁ hm h1 hpre
      subst hm
      rw [recIdxE.j1.arm1] at h1
      cases h2 : recIdxE p n m₁ T ni np tn tyn tyt fuel (j + 1) with
      | ok q => rw [h2, recIdxE.k_vi_rec_idx.arm1] at h1; cases h1
      | error e2 =>
        rw [h2, recIdxE.k_vi_rec_idx.none] at h1; cases h1
        obtain ⟨he, k, k1, k2, k3, k4, k5⟩ := ih (j + 1) e h2 hk
        rw [hj1] at k1
        refine ⟨he, k, by omega, k2, k3, fun k' h1 h2 h3 => ?_, k5⟩
        by_cases hkj : k' = j.toNat
        · subst hkj; exact hpre h3
        · exact k4 k' (by rw [hj1]; omega) h2 h3
    by_cases hT : rdW (m.arr64 IFL) (tyn + j) = T
    · rw [recIdxE.arm2 p n m T ni np tn tyn tyt fuel j hle hT] at h
      rw [ex1] at hT
      cases h1 : callE p n "pi_sort_tele_len" [fuel, rdW (m.arr64 IFL) (tyt + j)] m with
      | error e1 =>
        rw [h1, recIdxE.k_pi_sort_tele_len.none] at h; cases h
        exact absurd (hnv.cls (by simp) h1) hk
      | ok q =>
        obtain ⟨r, m₁⟩ := q
        rw [h1] at h
        obtain ⟨s', hs', rfl, hW⟩ := triple_of_callE (sortTele_spec p hL n ⟨m, Locals.init []⟩ _ _) h1
        have hm₁ : m₁ = m := by rw [← hs']
        rw [ex2] at hW
        obtain ⟨s1, -⟩ := sortTeleW_ok m a hR n fuel _ _ _ hW
        by_cases h0 : r.headD 0 = 0
        · rw [recIdxE.k_pi_sort_tele_len.arm2 p n T ni np tn tyn tyt fuel j r m₁ h0] at h
          exact hrest m₁ hm₁ h fun _ => ⟨_, s1, fun x hx => by rw [if_pos h0] at hx; cases hx⟩
        by_cases hx : np + ni = r.tail.headD 0
        · rw [recIdxE.k_pi_sort_tele_len.arm1 p n T ni np tn tyn tyt fuel j r m₁ h0 hx] at h
          exact hrest m₁ hm₁ h fun _ => ⟨_, s1, fun x hx' => by
            simp only [h0, if_false, Option.some.injEq] at hx'
            rw [← hx', ← hx, widx2 _ _ (by omega)]⟩
        · rw [recIdxE.k_pi_sort_tele_len.abort1 p n T ni np tn tyn tyt fuel j r m₁ h0 hx] at h
          cases h
          refine ⟨rfl, j.toNat, Nat.le_refl _, hjn, hT, fun k' h1 h2 => by omega, (r.tail.headD 0).toNat, ?_, ?_⟩
          · rw [s1, if_neg h0]
          · intro he
            apply hx
            apply UInt64.toNat_inj.mp
            rw [widx2 _ _ (by omega), he]
    · rw [recIdxE.arm3 p n m T ni np tn tyn tyt fuel j hle hT] at h
      rw [ex1] at hT
      exact hrest m rfl h fun h' => absurd h' hT

end L.Front.Ind
