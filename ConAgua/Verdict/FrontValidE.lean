import ConAgua.Verdict.FrontOrderE
import ConAgua.Verdict.FrontRecsE
import ConAgua.Verdict.FrontRunE
import ConAgua.Front.DeclsPre
import ConRon.Bridge.Promote.Walk

/-!
# `validate_ind_d`'s error refinement (lane `verdicts-b`, helper `f2`)

The assembly of `FrontOrderE.lean` (the constructor order, `numParams`, the duplicate and count
checks) and `FrontRecsE.lean` (the recursors) along `validateW_twin`'s run: a failing
`validate_ind_d` of class `≠ 0` claims `validateIndD`'s verdict (`validateE_claim`), which is
`ValidateClaim` (`FrontRunE.lean`) at the twin facts `XV` every state of the driver has
(`xOfTwin`).
-/

open ConRon.Arena ConRon.Arena.Frontend L.Arena
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Front.Ind

/-! ## The twin facts the messages need -/

theorem readName_run (a : AState) (h : NIdx) (x : ConLeche.Name) (hd : denoteN a.store.ns h = some x) :
    (readName h).run a = .ok (x, a) := by
  simp [readName, StateT.run_bind, StateT.run_get, hd]; rfl

/-- The handles of the parse state's name table read back (`StateDRel`). -/
theorem names_read_of_twin {a : AState} {st : StateD} (hT : L.Front.TwinOK a st) :
    ∀ i h, st.names.get? i = some h → ∃ x, (readName h).run a = .ok (x, a) := by
  intro i h hg
  obtain ⟨-, -, -, -, sc, hrel⟩ := hT
  have := hrel.names i
  rw [hg] at this
  cases hs : sc.names.get? i with
  | none => rw [hs] at this; exact this.elim
  | some n =>
    rw [hs] at this
    exact ⟨n, readName_run a h n this⟩

theorem namesReadR_of_twin {a : AState} {st : StateD} (hT : L.Front.TwinOK a st) (D : Array IDeclaration) :
    NamesReadR (st.pre D) a := by
  intro i h hr
  unfold StateD.name at hr
  cases hg : (st.pre D).names.get? i with
  | none => rw [hg] at hr; cases hr
  | some h' =>
    rw [hg] at hr; cases hr
    exact names_read_of_twin hT i h hg

theorem viewReadR_of_ok {a : AState} (hok : ConRon.Bridge.StateOK a) : ViewReadR a := by
  intro h T s hv
  have hv' : a.store.ns.view h = some (.str T s) := by
    unfold viewN at hv
    cases hw : a.store.ns.view h with
    | none => simp [StateT.run_bind, StateT.run_get, hw] at hv; cases hv
    | some w => simp [StateT.run_bind, StateT.run_get, hw] at hv; cases hv; rfl
  obtain ⟨rk, hrk⟩ := ConRon.Bridge.Frontend.nsWF_of_StateOK hok
  have hc := hrk.childOK h _ hv' T (by simp [NNodeView.children])
  obtain ⟨x, hx⟩ := ConRon.Bridge.denoteN_of_view ⟨rk, ConRon.Arena.NWFAt'.of_wf hrk⟩ hc.1
  exact ⟨x, readName_run a T x hx⟩

/-- `ifl_nodup` returning `0`: two equal words. -/
theorem nodupW_zero : ∀ (n : Nat) (m : Mem) (o l j : Word), nodupW n m o l j = some 0 →
    o.toNat + l.toNat < 2 ^ 64 →
    ∃ i i', j.toNat ≤ i ∧ i < i' ∧ i' < l.toNat ∧ wd m IFL (o.toNat + i) = wd m IFL (o.toNat + i') := by
  intro n
  induction n with
  | zero => intro m o l j h; simp [nodupW] at h
  | succ n ih =>
    intro m o l j h hb
    simp only [nodupW] at h
    split at h
    · cases h
    rename_i hlj
    have hjl := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hlj)
    have hj1 := wsucc j l (UInt64.not_le.mp hlj)
    have hoj : (o + j).toNat = o.toNat + j.toNat := widx2 _ _ (by omega)
    rcases hc : containsW n m o l (rdW (m.arr64 IFL) (o + j)) (j + 1) with _ | c <;> simp only [hc, nodupK, reduceCtorEq] at h
    obtain ⟨c1, -⟩ := containsW_facts n m o l _ _ c hc hb
    rw [hj1] at c1
    split at h
    · rename_i hc0
      obtain ⟨k, k1, k2, k3⟩ := c1 hc0
      refine ⟨j.toNat, k, Nat.le_refl _, by omega, k2, ?_⟩
      rw [k3, wd_eq, hoj]
    · obtain ⟨i, i', h1, h2, h3, h4⟩ := ih m o l (j + 1) h hb
      rw [hj1] at h1
      exact ⟨i, i', by omega, h2, h3, h4⟩

/-- Two equal words make a duplicate in the decoded slice. -/
theorem islice_not_nodup {m : Mem} {o l : Nat} {i i' : Nat} (h2 : i < i') (h3 : i' < l)
    (h4 : wd m IFL (o + i) = wd m IFL (o + i')) : ¬ (islice (k := .name) m o l).Nodup := by
  rw [List.nodup_iff_eq_of_getElem_eq]
  intro hn
  have := hn i i' (by rw [islice_length]; omega) (by rw [islice_length]; omega)
    (by rw [islice_get, islice_get, h4])
  omega

/-- The twin facts `validate_ind_d`'s claim takes. -/
def XV (st : StateD) (a : AState) : Prop := NamesRead st a ∧ NamesReadR st a ∧ ViewReadR a

theorem xOfTwin : ∀ (D : Array IDeclaration) (a : AState) (st : StateD), L.Front.TwinOK a st →
    XV (st.pre D) a := fun D a st hT =>
  ⟨fun i h hg => names_read_of_twin hT i h hg, namesReadR_of_twin hT D, viewReadR_of_ok hT.1⟩

/-- A call at fuel `0` fails with class `0`. -/
theorem callE_zero {p : Prog} {f : FnName} {vs : List Word} {m : Mem} {e : Err}
    (h : callE p 0 f vs m = .error e) : e.cls = 0 := by
  unfold callE at h
  simp only [invoke, lookupFn, StateT.run_bind] at h
  cases hp : p.lookup f with
  | none => simp [hp] at h; cases h; simp [Err.cls]
  | some fd =>
    simp [hp, callFn, exec, StateT.run_bind] at h
    have : StateT.run (throw Err.outOfFuel : M Sig) { mem := m, loc := Locals.init vs } = .error .outOfFuel := rfl
    rw [this] at h
    cases h; simp [Err.cls]

l_model viTail_specE (p : Prog) (hf : p.lookup "vi_tail" = some viTail)
  fns [hf ↦ viTailE] grind [arena_grind] simp [] errors

l_model validate_specE (p : Prog) (hf : p.lookup "validate_ind_d" = some L.Front.Ind.validateIndD)
  fns [hf ↦ validateE] grind [arena_grind] simp [] errors

/-- The callees of `validate_ind_d` and below outside the verdict closure. -/
def validNV : List FnName := ["vi_map", "vi_listed", "ifl_nodup", "store_fuel", "vi_k_expected",
  "ifl_find_last", "name_get", "expr_get", "ind_pi_tele_len", "ifl_alloc", "name_rec_pre",
  "pi_sort_tele_len", "vi_nested"]

theorem R_DUPLICATE_cls : (Err.abort R_DUPLICATE_CONSTRUCTOR_NAME).cls = 1 := by decide
theorem R_BLOCK_cls : (Err.abort R_THE_INDUCTIVE_BLOCK).cls = 1 := by decide

/-- **`validate_ind_d`'s error model claims `validateIndD`'s verdict.** Hypotheses of the ok
refinement `validateW_twin`, the twin facts `XV`, and that the callees outside the verdict
closure claim nothing (`validNV`). -/
theorem validateE_claim {p : Prog} (hL : IndApplyLookups p) (hnv : NVCls p validNV)
    {b : ByteArray} {n : Nat} {m : Mem} {a : AState} {st : StateD}
    (hR : ArenaR m a) (hD : StateDR m st) (hok : ConRon.Bridge.StateOK a) (hT : TopOK m)
    {to tn co cn ro rn : Word} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} (hF : IndFR b m to tn co cn ro rn tys cts rcs) (hIFR : topN m IFR < 2 ^ 62)
    (hX : XV st a) (e : Err) (he : validateE p n m to tn co cn ro rn = .error e) :
    L.Front.VerdictClaimL (ConRon.Arena.Frontend.validateIndD st tys cts rcs) a e := by
  intro hk
  obtain ⟨hRN, hRNR, hVR⟩ := hX
  obtain ⟨hTn, hTy, hCn, hCt, hRn, hRc⟩ := hF
  have hto : to.toNat + 11 * tys.length < 2 ^ 63 := by have := hTy.2.1; omega
  have hco : co.toNat + 10 * cts.length < 2 ^ 63 := by have := hCt.2.1; omega
  have hro : ro.toNat + 11 * rcs.length < 2 ^ 63 := by have := hRc.2.1; omega
  have nv : ∀ g ∈ validNV, ∀ {k args mm ε}, callE p k g args mm = .error ε → ε.cls = 0 :=
    fun g hg _ _ _ _ h => hnv g hg _ _ _ _ h
  cases n with
  | zero => simp only [validateE] at he; cases he; exact absurd rfl hk
  | succ n =>
  rw [validateE.arm1] at he
  -- `vi_unsafe`
  cases h1 : callE p n "vi_unsafe" [to, tn, 0] m with
  | error e1 =>
    rw [h1, validateE.k_vi_unsafe.none] at he; cases he
    cases n with
    | zero => exact absurd (callE_zero h1) hk
    | succ n' => exact viUnsafe_refinesE p hL.vi_unsafe n' m hTy hTn hto st cts rcs a e h1 hk
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, validateE.k_vi_unsafe.arm1] at he
  obtain ⟨s1, hs1, hsm1, hW1⟩ := triple_of_callE (unsafe_spec p hL n ⟨m, Locals.init []⟩ to tn 0) h1
  rw [← hs1, hsm1] at he
  have hu := unsafeW_twin hTy hTn hto n 0 hW1
  have hsafe : (tys.any fun x => x.isUnsafe) = false := by
    rw [List.any_eq_false]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    simp [hu k hk (Nat.zero_le _)]
  -- `vi_nparams`
  cases h2 : callE p n "vi_nparams" [to, tn] m with
  | error e2 =>
    rw [h2, validateE.k_vi_nparams.none] at he; cases he
    cases n with
    | zero => exact absurd (callE_zero h2) hk
    | succ n' =>
      exact viNparams_refinesE p hL.vi_nparams hL.vi_np_go n' m hTy hTn hto st cts rcs a hsafe e h2 hk
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, validateE.k_vi_nparams.arm1] at he
  obtain ⟨s2, hs2, hsm2, hW2⟩ := triple_of_callE (nparams_spec p hL n ⟨m, Locals.init []⟩ to tn) h2
  rw [← hs2, hsm2] at he
  generalize hnp : r2.headD 0 = np at he hW2
  obtain ⟨np1, np2, np3⟩ := nparamsW_twin hTy hTn hto hW2
  -- the type names
  have hidT : ∀ s : Word, s.toNat < 11 → ∀ k (hk : k < tys.length),
      rdW (m.arr64 IFR) (to + 11 * UInt64.ofNat k + s) = wd m IFR (to.toNat + 11 * k + s.toNat) := by
    intro s hs k hk
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    rw [wd_eq, widx _ _ _ _ (by rw [hk']; simp; omega), hk']; rfl
  cases h3 : callE p n "vi_map" [to, tn, 11, 0, 0] m with
  | error e3 =>
    rw [h3, validateE.k_vi_map.none] at he; cases he; exact absurd (nv _ (by decide) h3) hk
  | ok q3 =>
  obtain ⟨r3, m₁⟩ := q3
  rw [h3, validateE.k_vi_map.arm1] at he
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callE (map_spec p hL n ⟨m, Locals.init []⟩ _ _ _ _ _) h3
  rw [hs3] at hW3
  generalize hty : r3.headD 0 = tyn at he hW3
  obtain ⟨t1, t2, t3, -, t5, t6, t7⟩ := mapW_twin hT hW3 a tys (fun t => t.cv.name) st.name
    (by rw [hTn])
    (fun k hk => by
      have := hidT 0 (by decide) k hk
      simp only [Nat.add_zero, show (0 : Word).toNat = 0 from rfl] at this
      rw [this]; exact (hTy.2.2 k hk).1.1.1)
    (fun x w hw => lkW_name hD a (by simpa [mapLk] using hw))
  have hD₁ : StateDR m₁ st := hD.frame t2.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  have hR₁ : ArenaR m₁ a := ArenaR.frame_ext [IFL, LH] [192] (by decide) (by simp) m m₁ t2.frame a hR
  -- the type types
  cases h4 : callE p n "vi_map" [to, tn, 11, 2, 1] m₁ with
  | error e4 =>
    rw [h4, validateE.k_vi_map_2.none] at he; cases he; exact absurd (nv _ (by decide) h4) hk
  | ok q4 =>
  obtain ⟨r4, m₂⟩ := q4
  rw [h4, validateE.k_vi_map_2.arm1] at he
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callE (map_spec p hL n ⟨m₁, Locals.init []⟩ _ _ _ _ _) h4
  rw [hs4] at hW4
  generalize htt : r4.headD 0 = tyt at he hW4
  obtain ⟨u1, u2, u3, -, u5, u6, u7⟩ := mapW_twin t3 hW4 a tys (fun t => t.cv.type) (getDeclD st)
    (by rw [hTn])
    (fun k hk => by
      have := hidT 2 (by decide) k hk
      rw [t2.ifr, this]; exact (hTy.2.2 k hk).1.2.2.1)
    (fun x w hw => by
      have := lkW_expr hD₁ a (by simpa [mapLk] using hw)
      rw [decE_eq] at this; exact this)
  have e12 := t2.trans u2
  have hD₂ : StateDR m₂ st := hD.frame e12.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  -- the listed constructor names
  cases h5 : callE p n "vi_listed" [to, tn] m₂ with
  | error e5 =>
    rw [h5, validateE.k_vi_listed.none] at he; cases he; exact absurd (nv _ (by decide) h5) hk
  | ok q5 =>
  obtain ⟨r5, m₃⟩ := q5
  rw [h5, validateE.k_vi_listed.arm1] at he
  obtain ⟨s5, hs5, -, hW5⟩ := triple_of_callE (listed_spec p hL n ⟨m₂, Locals.init []⟩ _ _) h5
  rw [hs5] at hW5
  generalize hfo : r5.headD 0 = fo at he hW5
  generalize hxx : r5.tail.headD 0 = x at he hW5
  obtain ⟨LS, l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := listedW_twin hD a tys to tn
    (fun k hk => hTy.2.2 k hk) hTn (by omega) hW5 e12 u3
  have e13 := e12.trans l2
  have hD₃ : StateDR m₃ st := hD.frame e13.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  -- the constructor records' names
  cases h6 : callE p n "vi_map" [co, cn, 10, 0, 0] m₃ with
  | error e6 =>
    rw [h6, validateE.k_vi_map_3.none] at he; cases he; exact absurd (nv _ (by decide) h6) hk
  | ok q6 =>
  obtain ⟨r6, m₄⟩ := q6
  rw [h6, validateE.k_vi_map_3.arm1] at he
  obtain ⟨s6, hs6, -, hW6⟩ := triple_of_callE (map_spec p hL n ⟨m₃, Locals.init []⟩ _ _ _ _ _) h6
  rw [hs6] at hW6
  generalize hcno : r6.headD 0 = cno at he hW6
  obtain ⟨v1, v2, v3, -, v5, v6, v7⟩ := mapW_twin l3 hW6 a cts (fun c => c.cv.name) st.name
    (by rw [hCn])
    (fun k hk => by
      have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      rw [e13.ifr, wd_eq, widx _ _ _ _ (by rw [hk']; simp; omega), hk']
      exact (hCt.2.2 k hk).1.1.1)
    (fun x w hw => lkW_name hD₃ a (by simpa [mapLk] using hw))
  have e14 := e13.trans v2
  have hkeep34 : ∀ c, c < LS.flatten.length → wd m₄ IFL (fo.toNat + c) = wd m₃ IFL (fo.toNat + c) :=
    fun c hc => v2.keep _ (by omega) (by omega)
  have hVP : VPre st a tys cts (islice m₁ tyn.toNat tys.length) (islice m₂ tyt.toNat tys.length) LS
      (islice m₄ cno.toNat cts.length) np.toNat :=
    ⟨hsafe, np1, np2, by simpa using t1, by simpa using u1, l1, by simpa using v1⟩
  -- `ifl_nodup`
  cases h7 : callE p n "ifl_nodup" [fo, x, 0] m₄ with
  | error e7 =>
    rw [h7, validateE.k_ifl_nodup.none] at he; cases he; exact absurd (nv _ (by decide) h7) hk
  | ok q7 =>
  obtain ⟨r7, m₅⟩ := q7
  obtain ⟨s7, hs7, hsm7, hW7⟩ := triple_of_callE (nodup_spec p hL n ⟨m₄, Locals.init []⟩ _ _ _) h7
  have hm5 : m₅ = m₄ := by rw [← hs7, hsm7]
  rw [hm5] at h7
  rw [h7] at he
  by_cases hu0 : r7.headD 0 = 0
  · rw [validateE.k_ifl_nodup.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu0] at he; cases he
    rw [hu0] at hW7
    obtain ⟨i, i', -, hii, hi', heq⟩ := nodupW_zero n m₄ fo x 0 hW7 (by have := l3.1; have := l3.2; omega)
    rw [l5] at hi'
    have hnd : ¬ LS.flatten.Nodup := by
      rw [l7]
      exact islice_not_nodup hii hi' (by rw [← hkeep34 _ (by omega), ← hkeep34 _ hi']; exact heq)
    obtain ⟨v, hv, hc⟩ := validateIndD_nodup (rcs := rcs) hVP hnd
    exact .inr ⟨v, a, hv, by rw [hc, R_DUPLICATE_cls]⟩
  have hnd : LS.flatten.Nodup := by
    rw [l7]
    apply islice_nodup (fun c hc => l8 c hc)
    intro i i' hii hi'
    have := nodupW_facts n m₄ fo x 0 _ hW7 (by have := l3.1; have := l3.2; omega) hu0 i i' (Nat.zero_le _)
      hii (by rw [l5]; exact hi')
    rw [hkeep34 _ (by omega), hkeep34 _ hi'] at this
    exact this
  by_cases hxcn : x ≠ cn
  · rw [validateE.k_ifl_nodup.abort2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu0 hxcn] at he; cases he
    have hlen : LS.flatten.length ≠ cts.length := fun h => hxcn (UInt64.toNat_inj.mp (by rw [l5, h, hCn]))
    obtain ⟨v, hv, hc⟩ := validateIndD_len (rcs := rcs) hVP hnd hlen
    exact .inr ⟨v, a, hv, by rw [hc, R_BLOCK_cls]⟩
  have hxcn' : x = cn := Classical.byContradiction hxcn
  rw [validateE.k_ifl_nodup.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu0 hxcn'] at he
  have hflen : LS.flatten.length = cts.length := by rw [← l5, hxcn', hCn]
  -- the tail
  cases h8 : callE p n "vi_tail" [to, tn, co, cn, ro, rn, np, tyn, tyt, fo, cno] m₄ with
  | ok q8 => obtain ⟨_, _⟩ := q8; rw [h8, validateE.k_vi_tail.arm1] at he; cases he
  | error e8 =>
  rw [h8, validateE.k_vi_tail.none] at he; cases he
  have hE := triple_of_callE_err (viTail_specE p hL.vi_tail n ⟨m₄, Locals.init []⟩ _ _ _ _ _ _ _ _ _ _ _) h8
    (Err.code_ne_of_cls hk)
  sorry

end L.Front.Ind
