import ConAgua.Verdict.FrontOrderE
import ConAgua.Verdict.FrontRecsE
import ConAgua.Verdict.FrontRunE
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
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
    XV (st.pre D) a := fun D _a _st hT =>
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
  dsimp only at hW3
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
  dsimp only at hW4
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
  dsimp only at hW5
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
  dsimp only at hW6
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
  cases n with
  | zero => simp only [viTailE] at hE; cases hE; exact absurd rfl hk
  | succ n =>
  rw [viTailE.arm1] at hE
  have hR₄ : ArenaR m₄ a := ArenaR.frame_ext [IFL, LH] [192] (by decide) (by simp) m m₄ e14.frame a hR
  have hD₄ : StateDR m₄ st := hD.frame e14.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  cases h9 : callE p n "store_fuel" [] m₄ with
  | error e9 =>
    rw [h9, viTailE.k_store_fuel.none] at hE; cases hE; exact absurd (nv _ (by decide) h9) hk
  | ok q9 =>
  obtain ⟨r9, m9⟩ := q9
  rw [h9, viTailE.k_store_fuel.arm1] at hE
  obtain ⟨s9, hs9, hsm9, hW9⟩ := triple_of_callE (storeFuel_spec p hL n ⟨m₄, Locals.init []⟩) h9
  have hm9 : m9 = m₄ := by rw [← hs9, hsm9]
  rw [hm9] at hE
  generalize hfu : r9.headD 0 = fuel at hE hW9
  have hfuel := storeFuelW_ok hR₄ hW9
  have hps4 : ∀ i, i ≤ tys.length → psum m₄ to i = fpos LS i := fun i hi => by
    rw [psum_congr e14.ifr]; exact psum_fpos (fun k hk => hTy.2.2 k hk) l9 i hi
  have hLSl : LS.length = tys.length := by have := congrArg List.length l9; simpa using this
  have hcnt : ∀ k (hk : k < tys.length), cntF m₄ to k = tys[k].ctors.length := fun k hk => by
    simp only [cntF, wd, e14.ifr]; exact (hTy.2.2 k hk).2.1
  have hzl : (islice (k := .name) m₁ tyn.toNat tys.length).length = LS.length := by
    rw [islice_length, hLSl]
  have hcntL : ∀ k (hk : k < LS.length), cntF m₄ to k = LS[k].length := fun k hk => by
    have hk' : k < tys.length := by omega
    rw [hcnt k hk']
    have := congrArg (fun l => l[k]?) l9
    simp only [List.getElem?_map, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk',
      Option.map_some, Option.some.injEq] at this
    rw [← this]
  have hnnL : ∀ i (hi : i < LS.length) c (hc : c < LS[i].length),
      LS[i][c] = decI (wd m₄ IFL (fo.toNat + (fpos LS i + c))) := fun i hi c hc => by
    have hpl := fpos_lt LS i c hi hc
    rw [getElem_flatten' LS i c hi hc, List.getElem_of_eq l7, islice_get, hkeep34 _ hpl]
  have hTNL : ∀ i, i < LS.length →
      (islice (k := .name) m₁ tyn.toNat tys.length)[i]! = decI (wd m₄ IFL (tyn.toNat + i)) := fun i hi => by
    have hi' : i < tys.length := by omega
    rw [getElem!_pos _ i (by rw [islice_length]; exact hi'), islice_get,
      ((u2.trans (l2.trans v2)).keep _ (by omega) (by omega))]
  cases h10 : callE p n "vi_order" [to, tn, tyn, fo, cno, co, cn, fuel, np] m₄ with
  | error e10 =>
    rw [h10, viTailE.k_vi_order.none] at hE; cases hE
    cases n with
    | zero => exact absurd (callE_zero h10) hk
    | succ n' =>
    obtain ⟨hc1, hOW⟩ := orderE_fail hL (fun g hg => hnv g (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide)) hR₄ hD₄ v3
      (hCt.ext e14 (fun _ _ x => x.ext e14)) hCn v7
      (by rw [v6, v5]; omega) np3 hco ⟨by omega, by omega, by omega⟩ (by rw [hTn]; omega)
      (by rw [hTn]; omega)
      (fun p hp => by
        rw [hps4 _ (by omega), hTn, ← hLSl, fpos_full] at hp
        refine ⟨by omega, ?_⟩
        rw [hkeep34 p hp]; exact l8 p hp)
      (by rw [hps4 _ (by omega), hTn, ← hLSl, fpos_full, hflen]; exact Nat.le_refl _)
      (fun k hk => by
        rw [((u2.trans (l2.trans v2)).keep _ (by omega) (by omega))]; rw [hTn] at hk; exact t7 k hk)
      e h10 hk
    have hO := orderFail_of_W (LS := LS) (TN := islice (k := .name) m₁ tyn.toNat tys.length) hOW
      (by rw [hLSl, hTn]) (fun i hi => hps4 i (by omega)) hcntL hnnL hTNL rfl
    obtain ⟨v, hv, hc⟩ := validateIndD_orderFail_cls (rcs := rcs) hVP hnd hflen hzl hRN hfuel.symm hO
    exact .inr ⟨v, a, hv, by rw [hc, hc1]⟩
  | ok q10 =>
  obtain ⟨r10, m₅⟩ := q10
  rw [h10, viTailE.k_vi_order.arm1] at hE
  obtain ⟨s10, hs10, -, hW10⟩ := triple_of_callE (order_spec p hL n ⟨m₄, Locals.init []⟩ _ _ _ _ _ _ _ _ _) h10
  rw [hs10] at hW10
  dsimp only at hW10
  generalize hoo : r10.headD 0 = oo at hE hW10
  obtain ⟨o1, o2, o3, o4, o5⟩ := orderW_twin hR₄ hD₄ v3 (hCt.ext e14 (fun _ _ x => x.ext e14)) hCn v7
    (by rw [v6, v5]; omega) np3 hco ⟨by omega, by omega, by omega⟩ (by rw [hTn]; omega)
    (by rw [hTn]; omega)
    (fun p hp => by
      rw [hps4 _ (by omega), hTn, ← hLSl, fpos_full] at hp
      refine ⟨by omega, ?_⟩
      rw [hkeep34 p hp]; exact l8 p hp)
    (by rw [hps4 _ (by omega), hTn, ← hLSl, fpos_full, hflen]; exact Nat.le_refl _) hW10
  cases h11 : callE p n "vi_k_expected" [to, tn, tyt, oo, fuel] m₅ with
  | error e11 =>
    rw [h11, viTailE.k_vi_k_expected.none] at hE; cases hE; exact absurd (nv _ (by decide) h11) hk
  | ok q11 =>
  obtain ⟨r11, m₆⟩ := q11
  rw [h11, viTailE.k_vi_k_expected.arm1] at hE
  obtain ⟨s11, hs11, -, hW11⟩ := triple_of_callE (kExp_spec p hL n ⟨m₅, Locals.init []⟩ _ _ _ _ _) h11
  rw [hs11] at hW11
  dsimp only at hW11
  generalize hke' : r11.headD 0 = ke at hE hW11
  have e15 := e14.trans o2
  have hR₅ : ArenaR m₅ a := ArenaR.frame_ext [IFL, LH] [192] (by decide) (by simp) m m₅ e15.frame a hR
  -- `kExpected?`
  obtain ⟨k1, k2, k3⟩ := kExpW_twin hR₅ hok hW11
  have e56 := iext_of_heap k1
  have e16 := e15.trans e56
  have hR₆ : ArenaR m₆ a := ArenaR.frame_ext [IFL, LH] [192] (by decide) (by simp) m m₆ e16.frame a hR
  have hD₆ : StateDR m₆ st := hD.frame e16.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  have hIFL56 : m₆.arr64 IFL = m₅.arr64 IFL := k1.1 IFL (by decide) (by decide)
  -- the words the twin's lists are read from
  have hTNw : ∀ i, i < tys.length → wd m₆ IFL (tyn.toNat + i) = wd m₁ IFL (tyn.toNat + i) := fun i hi =>
    ((u2.trans (l2.trans (v2.trans (o2.trans e56)))).keep _ (by omega) (by omega))
  have hTTw : ∀ i, i < tys.length → wd m₆ IFL (tyt.toNat + i) = wd m₂ IFL (tyt.toNat + i) := fun i hi =>
    ((l2.trans (v2.trans (o2.trans e56))).keep _ (by omega) (by omega))
  have hTN : islice (k := .name) m₆ tyn.toNat tn.toNat = islice m₁ tyn.toNat tys.length := by
    rw [hTn]; simp only [islice]; apply List.map_congr_left; intro i hi
    simp only [List.mem_range] at hi; rw [hTNw i hi]
  have hTT : islice (k := .expr) m₆ tyt.toNat tn.toNat = islice m₂ tyt.toNat tys.length := by
    rw [hTn]; simp only [islice]; apply List.map_congr_left; intro i hi
    simp only [List.mem_range] at hi; rw [hTTw i hi]
  have hke : ke = 0 ∨ ke = 1 ∨ ke = 2 := by
    by_cases hc : tn = 1 ∧ rdW (m₅.arr64 IFR) (to + 4) = 1
    · obtain ⟨r, v, -, -, hn, hs⟩ := k3 hc.1 hc.2
      by_cases hv : ∃ s, v = .sort s
      · obtain ⟨s, hs'⟩ := hv
        obtain ⟨L, -, hk⟩ := hs s hs'
        rw [hk]; split <;> simp
      · exact .inl (hn (fun s hs' => hv ⟨s, hs'⟩))
    · exact .inr (.inl (k2 (by
        rcases Classical.not_and_iff_not_or_not.mp hc with h | h
        · exact .inl h
        · exact .inr h)))
  cases h12 : callE p n "vi_recs" [to, tn, ro, rn, np, cn, ke, tyn, tyt, fuel] m₆ with
  | ok q12 => obtain ⟨_, _⟩ := q12; rw [h12, viTailE.k_vi_recs.arm1] at hE; cases hE
  | error e12 =>
  rw [h12, viTailE.k_vi_recs.none] at hE; cases hE
  have hTy₆ : ListF (TyF b m₆) m₆ 11 to.toNat tys := hTy.ext e16 (fun _ _ x => x.ext e16)
  have hRc₆ : ListF (RecF b m₆) m₆ 11 ro.toNat rcs := hRc.ext e16 (fun _ _ x => x.ext e16)
  obtain ⟨hc1, hany, hRF⟩ := viRecs_refinesE hL (fun g hg => hnv g (by
      simp only [recsNV, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> decide)) hR₆ hD₆ hTy₆ hTn hto hRc₆ hRn hro np3 hke
    (by have := t3.1; have := t3.2; have := u2.top; have := l2.top; have := v2.top; omega)
    (by have := u3.1; have := u3.2; omega)
    (fun i hi => by rw [hTn] at hi; rw [hTNw i hi]; exact t7 i hi) n e h12 hk
  rw [hTN, hTT, hTn, hCn] at hRF
  -- the order's facts, per type and position
  have hordf : ∀ i (hi : i < LS.length) c (hc : c < LS[i].length), ∃ k,
      ∃ _ : fpos LS i + c < (ordList m₅ oo.toNat co.toNat cts cts.length).length,
        (ordList m₅ oo.toNat co.toNat cts cts.length)[fpos LS i + c] = cts[k]! ∧
        CtorOK st a cts (islice m₄ cno.toNat cts.length) LS[i][c] c
          ((islice (k := .name) m₁ tyn.toNat tys.length)[i]!) np.toNat fuel.toNat k := by
    intro i hi c hc
    have hi' : i < tys.length := by omega
    have hcn' : c < cntF m₄ to i := by
      rw [hcnt i hi']
      have := congrArg (fun l => l[i]?) l9
      simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
        Option.map_some, Option.some.injEq] at this
      rw [← this]; exact hc
    obtain ⟨kk, w1, w2⟩ := o5 i (by omega) c hcn'
    rw [hps4 i (by omega)] at w1 w2
    have hpl := fpos_lt LS i c hi hc
    have hkk : kk < cts.length := w2.1
    refine ⟨kk, by rw [ordList_length]; omega, ?_, ?_⟩
    · rw [ordList_get, ← Nat.add_assoc, ptr_rec cts co kk hkk hco _ w1, getElem!_pos cts kk hkk]
    · have hnn : LS[i][c] = decI (wd m₄ IFL (fo.toNat + (fpos LS i + c))) := by
        rw [getElem_flatten' LS i c hi hc, List.getElem_of_eq l7, islice_get, hkeep34 _ hpl]
      have htt : (islice (k := .name) m₁ tyn.toNat tys.length)[i]! = decI (wd m₄ IFL (tyn.toNat + i)) := by
        rw [getElem!_pos _ i (by rw [islice_length]; exact hi'), islice_get,
          ((u2.trans (l2.trans v2)).keep _ (by omega) (by omega))]
      rw [hnn, htt, ← Nat.add_assoc]
      exact w2
  -- the type records' first constructor count
  have hR4 : rdW (m₅.arr64 IFR) (to + 4) = wd m IFR (to.toNat + 4) := by
    rw [wd_eq, widx2 _ _ (by simp; omega)]; simp only [wd, e15.ifr]; rfl
  have hc0 : ∀ h0 : 0 < tys.length, (wd m IFR (to.toNat + 4)).toNat = tys[0].ctors.length := fun h0 => by
    have := (hTy.2.2 0 h0).2.1; simpa using this
  have hLS0 : ∀ hd, LS = [[hd]] → tys.length = 1 ∧ ∃ h0 : 0 < tys.length, tys[0].ctors.length = 1 := by
    intro hd hL
    have h1 : tys.length = 1 := by rw [← hLSl, hL]; rfl
    refine ⟨h1, by omega, ?_⟩
    have := congrArg (fun l => l[0]?) l9
    rw [hL] at this
    simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, List.length_cons, List.length_nil,
      List.getElem?_map, List.getElem?_eq_getElem (show 0 < tys.length by omega), Option.map_some,
      Option.some.injEq] at this
    rw [← this]
  -- the first ordered constructor's pointer
  have hfirst : ∀ (h0 : 0 < tys.length) (hc : 0 < cntF m₄ to 0), ∃ kk, ∃ hk : kk < cts.length,
      wd m₅ IFL oo.toNat = co + 10 * UInt64.ofNat kk ∧
      ∀ hp : 0 < (ordList m₅ oo.toNat co.toNat cts cts.length).length,
        (ordList m₅ oo.toNat co.toNat cts cts.length)[0] = cts[kk] := by
    intro h0 hc
    obtain ⟨kk, w1, w2⟩ := o5 0 (by omega) 0 hc
    simp only [show psum m₄ to 0 = 0 from rfl, Nat.add_zero] at w1
    refine ⟨kk, w2.1, w1, fun hp => ?_⟩
    rw [ordList_get, Nat.add_zero, ptr_rec cts co kk w2.1 hco _ w1]
  -- the facts
  have hV : VFactsR st a tys cts (islice m₁ tyn.toNat tys.length) (islice m₂ tyt.toNat tys.length) LS
      (islice m₄ cno.toNat cts.length) fuel.toNat np.toNat (ordList m₅ oo.toNat co.toNat cts cts.length)
      (keOf ke) := by
    refine ⟨?_, np1, np2, by simpa using t1, by simpa using u1, l1, by simpa using v1, hnd, hflen,
      hfuel.symm, islice_length _ _ _, islice_length _ _ _, hLSl, ordList_length _ _ _ _ _, hordf,
      ?_, ?_, fun r hr => by split at hr <;> simp at hr⟩
    · rw [List.any_eq_false]
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
      simp [hu k hk (Nat.zero_le _)]
    · intro hnot
      by_cases hc : tn = 1 ∧ rdW (m₅.arr64 IFR) (to + 4) = 1
      · exfalso; apply hnot
        have h1 : tys.length = 1 := by rw [← hTn, hc.1]; rfl
        refine ⟨by rw [islice_length]; exact h1, ?_⟩
        rw [l9]
        cases htys : tys with
        | nil => rw [htys] at h1; simp at h1
        | cons t ts =>
          cases ts with
          | cons _ _ => rw [htys] at h1; simp at h1
          | nil =>
            have := hc0 (by omega)
            rw [← hR4, hc.2] at this
            simp only [htys, List.getElem_cons_zero] at this
            simp [← this]
      · have := k2 (by
          rcases Classical.not_and_iff_not_or_not.mp hc with h | h
          · exact .inl h
          · exact .inr h)
        rw [this]; rfl
    · intro ty hd c hTT hLS hord
      obtain ⟨h1, h0, hlen1⟩ := hLS0 hd hLS
      have htn : tn = 1 := UInt64.toNat_inj.mp (by rw [hTn, h1]; rfl)
      have h4 : rdW (m₅.arr64 IFR) (to + 4) = 1 := by
        rw [hR4]; apply UInt64.toNat_inj.mp; rw [hc0 h0, hlen1]; rfl
      obtain ⟨r, v, hr, hv, hn, hs⟩ := k3 htn h4
      have hty : ty = decE (rdW (m₅.arr64 IFL) tyt) := by
        have := congrArg (fun l => l[0]?) hTT
        simp only [List.getElem?_cons_zero, List.getElem?_eq_getElem (show 0 < (islice (k := .expr) m₂ tyt.toNat tys.length).length by rw [islice_length]; omega),
          Option.some.injEq, islice_get, Nat.add_zero] at this
        rw [← this, decE_eq, wd_eq, (l2.trans (v2.trans o2)).keep _ (by omega) (by omega)]
      obtain ⟨kk, hk, hw, hget⟩ := hfirst h0 (by rw [hcnt 0 h0, hlen1]; decide)
      have hc' : c = cts[kk] := by
        have := hget (by rw [hord]; exact Nat.zero_lt_one)
        simp only [hord, List.getElem_cons_zero] at this
        exact this
      refine ⟨r, v, by rw [hty]; exact hr, hv, fun hns => by rw [hn hns]; rfl, fun s hvs => ?_⟩
      obtain ⟨L, hL, hke'⟩ := hs s hvs
      refine ⟨L, hL, ?_⟩
      have hkw : (UInt64.ofNat kk).toNat = kk :=
        UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      have hnf : rdW (m₅.arr64 IFR) (rdW (m₅.arr64 IFL) oo + 4) = wd m IFR (co.toNat + 10 * kk + 4) := by
        rw [wd_eq (A := IFL), hw, wd_eq, widx _ _ _ _ (by rw [hkw]; simp; omega), hkw]
        simp only [wd, e15.ifr]; rfl
      obtain ⟨-, c4, -⟩ := hCt.2.2 kk hk
      rw [hnf] at hke'
      rw [hke', hc']
      by_cases hz : cts[kk].numFields = 0
      · have hz' : wd m IFR (co.toNat + 10 * kk + 4) = 0 := UInt64.toNat_inj.mp (by rw [c4.1, hz]; rfl)
        by_cases he : L.isEquiv .zero = some true
        · simp [hz', he, hz, keOf]
        · simp [hz', he, hz, keOf]
      · have hz' : wd m IFR (co.toNat + 10 * kk + 4) ≠ 0 := fun e => hz (by rw [← c4.1, e]; rfl)
        simp [hz', hz, keOf]
  rw [← ordList_length m₅ oo.toNat co.toNat cts cts.length] at hRF
  obtain ⟨w, hw⟩ := validateIndD_recsFail hV hany hRF hRNR hVR
  exact .inr ⟨_, a, hw, by rw [twinCls_invalid, hc1]⟩

end L.Front.Ind

namespace L.Front.Ind

theorem validNV_nv : ∀ f ∈ validNV, f ∈ L.Checker.nvFns :=
  _root_.L.Checker.nv_sub (by decide +kernel)

theorem validNV_front : ∀ f ∈ validNV, L.Checker.inFront f = true := by decide

/-- The callees of `validate_ind_d` outside the closure claim nothing in `frontAllProg`. -/
theorem frontAll_validNV : NVCls frontAllProg validNV := by
  intro g hg n args m e h
  rw [callE_frontAll (validNV_front g hg)] at h
  exact callE_nv L.Checker.checkerProg_nv (validNV_nv g hg) n args m h

/-- **`validate_ind_d`'s claim at `frontAllProg`** (`ValidateClaim`, at the twin facts `XV`). -/
theorem validateClaim_frontAll : ValidateClaim frontAllProg XV := by
  intro b n m a st to tn co cn ro rn tys cts rcs e hR hD hok hT hF hIFR hX hc hk
  exact validateE_claim frontAllProg_indApply frontAll_validNV hR hD hok hT hF hIFR hX e
    (triple_of_callE_err (validate_specE frontAllProg frontAllProg_indApply.validate_ind_d n
      ⟨m, Locals.init []⟩ _ _ _ _ _ _) hc (Err.code_ne_of_cls hk)) hk

end L.Front.Ind
