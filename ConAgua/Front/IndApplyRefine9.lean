module

public import ConAgua.Front.IndApplyRefine8
public import ConAgua.Verdict.FrontRecsE
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Checker.NoVerdictTree
import ConAgua.Front.IndApplyRefine
import all ConAgua.Front.IndApply

@[expose] public section

/-!
# The apply step of an `inductive` line against the twin, IX: `validate_ind_d` refines `validateIndD`

`validate_ref`, one refinement for both outcomes of `validate_ind_d`'s unified model (with
`vi_tail`'s, unfolded) on the records of an inductive line (`IndFR`): an ok value establishes the
clean facts `VFacts` of the twin's validation (`IndValidTwin.lean`), so `validateIndD` succeeds
with the ordered constructors, which the model left as record pointers at `oo`; an error of class
`≠ 0` is `validateIndD`'s record verdict at the check that failed (`FrontOrderE.lean`,
`FrontRecsE.lean`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true


namespace L.Front.Ind

theorem psum_fpos {b : ByteArray} {m : Mem} {to : Word} {tys : List IndTypeRec}
    (hF : ∀ k (hk : k < tys.length), TyF b m (to.toNat + 11 * k) tys[k])
    {LS : List (List NIdx)} (hLS : LS.map List.length = tys.map fun t : IndTypeRec => t.ctors.length) :
    ∀ i, i ≤ tys.length → psum m to i = fpos LS i := by
  have hl : LS.length = tys.length := by
    have := congrArg List.length hLS; simpa using this
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [psum_succ, fpos_succ LS i (by omega), ih (by omega)]
    congr 1
    obtain ⟨-, h4, -⟩ := hF i (by omega)
    have := congrArg (fun l => l[i]?) hLS
    simp only [List.getElem?_map, List.getElem?_eq_getElem (show i < LS.length by omega),
      List.getElem?_eq_getElem (show i < tys.length by omega), Option.map_some, Option.some.injEq] at this
    rw [this]; exact h4

theorem ordList_get (m : Mem) (oo co : Nat) (cts : List IndCtorRec) (l p : Nat)
    (hp : p < (ordList m oo co cts l).length) :
    (ordList m oo co cts l)[p] = cts.getD (((wd m IFL (oo + p)).toNat - co) / 10) default := by
  simp [ordList]

/-- A write set of the level heap only is an `IExt`. -/
theorem iext_of_heap {m m' : Mem} (h : MemFrame [LH] [192] m m') : IExt m m' := by
  have hI : m'.arr64 IFL = m.arr64 IFL := h.arr IFL (by decide) (by decide)
  refine ⟨h.mono (by simp) (by simp), by simp [topN, wd, hI], fun i _ _ => by simp [wd, hI]⟩


/-! ## The unified models -/

l_model viTail_specE (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_tail ↦ viTailE]
  specs [storeFuel_spec p hL n, viOrder_specE p hL n, recs_specE p hL n]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE]
  unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model validate_specE (p : Prog) (hL : IndApplyLookups p)
  fns [hL.validate_ind_d ↦ validateE]
  specs [viUnsafe_specE p hL.vi_unsafe n, viNparams_specE p hL n, map_spec p hL n, listed_spec p hL n,
    nodup_spec p hL n, viTail_specE p hL n]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE]
  unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


/-! ## `validate_ind_d` -/

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

/-- The twin facts `validate_ind_d`'s error half takes (the messages' name reads). -/
def XV (st : StateD) (a : AState) : Prop := NamesRead st a ∧ NamesReadR st a ∧ ViewReadR a

theorem R_DUPLICATE_cls : (Err.abort R_DUPLICATE_CONSTRUCTOR_NAME).cls = 1 := by decide
theorem R_BLOCK_cls : (Err.abort R_THE_INDUCTIVE_BLOCK).cls = 1 := by decide

/-- **`validate_ind_d`'s ok half**: `validateIndD` succeeds with the ordered constructors, which
the model left as record pointers at `oo` (the first result word), and `nPd` (the second). -/
structure ValidatePost (st : StateD) (a : AState) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) (co : Word) (m : Mem) (v : List Word × Mem) : Prop where
  twin : ∃ ordered : List IndCtorRec,
    (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = .ok (.inr (ordered, (v.1.tail.headD 0).toNat), a) ∧
      ordered.length = cts.length ∧
      ∀ p (hp : p < ordered.length), ∃ k, ∃ _ : k < cts.length,
        wd v.2 IFL ((v.1.headD 0).toNat + p) = co + 10 * UInt64.ofNat k ∧ ordered[p] = cts[k]
  ext : IExt m v.2
  top : TopOK v.2
  off : 1 ≤ (v.1.headD 0).toNat
  room : (v.1.headD 0).toNat + cts.length ≤ topN v.2 IFL + 1
  np : (v.1.tail.headD 0).toNat < 10 ^ 18

/-- **`validate_ind_d`, both outcomes**: on the records of an inductive line (`IndFR`), the
model's ok value is `validateIndD`'s success (`ValidatePost`), its error (of class `≠ 0`, at the
twin facts `XV`) `validateIndD`'s record verdict. -/
@[refines ConRon.Arena.Frontend.validateIndD]
theorem validate_ref {b : ByteArray} {m : Mem} {a : AState} {st : StateD} (hR : ArenaR m a)
    (hD : StateDR m st) (hok : ConRon.Bridge.StateOK a) (hT : TopOK m)
    {to tn co cn ro rn : Word} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} (hF : IndFR b m to tn co cn ro rn tys cts rcs) (hIFR : topN m IFR < 2 ^ 62)
    (p : Prog) (n : Nat) :
    RefC (XV st a) (validateE p n m to tn co cn ro rn) (ValidatePost st a tys cts rcs co m)
      (L.Front.VerdictClaimL (ConRon.Arena.Frontend.validateIndD st tys cts rcs) a) := by
  obtain ⟨hTn, hTy, hCn, hCt, hRn, hRc⟩ := hF
  have hto : to.toNat + 11 * tys.length < 2 ^ 63 := by have := hTy.2.1; omega
  have hco : co.toNat + 10 * cts.length < 2 ^ 63 := by have := hCt.2.1; omega
  have hro : ro.toNat + 11 * rcs.length < 2 ^ 63 := by have := hRc.2.1; omega
  cases n with
  | zero => simp only [validateE, RefC_error]; exact fun _ hk => absurd Err.cls_outOfFuel hk
  | succ n =>
  rw [validateE.arm1]
  -- `vi_unsafe`
  have h1r := unsafe_ref hTy hTn hto p st cts rcs a n 0
  rcases h1 : viUnsafeE p n m to tn 0 with e1 | ⟨u1, mu⟩ <;> rw [h1] at h1r
  · rw [validateE.k_vi_unsafe.none]; exact fun _ => h1r trivial
  rw [validateE.k_vi_unsafe.arm1]
  obtain ⟨hmu, hu⟩ := h1r
  dsimp only at hmu
  rw [hmu]
  have hsafe : (tys.any fun x => x.isUnsafe) = false := by
    rw [List.any_eq_false]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    simp [hu k hk (Nat.zero_le _)]
  -- `vi_nparams`
  have h2r := nparams_ref hTy hTn hto p n
  rcases h2 : viNparamsE p n m to tn with e2 | ⟨np, mp⟩ <;> rw [h2] at h2r
  · rw [validateE.k_vi_nparams.none]
    intro _ hk
    obtain ⟨he, hall⟩ := h2r trivial hk
    obtain ⟨v, hv, hcl⟩ := validateIndD_np (st := st) (a := a) (cts := cts) (rcs := rcs) hsafe hall
    exact .inr ⟨v, a, hv, by rw [hcl, he]; decide⟩
  rw [validateE.k_vi_nparams.arm1]
  obtain ⟨hmp, np1, np2, np3⟩ := h2r
  dsimp only at hmp np1 np2 np3
  rw [hmp]
  -- the type names
  have hidT : ∀ s : Word, s.toNat < 11 → ∀ k (hk : k < tys.length),
      rdW (m.arr64 IFR) (to + 11 * UInt64.ofNat k + s) = wd m IFR (to.toNat + 11 * k + s.toNat) := by
    intro s hs k hk
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    rw [wd_eq, widx _ _ _ _ (by rw [hk']; simp; omega), hk']; rfl
  rcases h3 : mapW n m to tn 11 0 0 with _ | ⟨⟨tyn, x1⟩, m₁⟩
  · rw [flat3_none, liftE_none, validateE.k_vi_map.none]; exact fun _ hk => absurd Err.cls_oob hk
  rw [flat3_some, liftE_some, validateE.k_vi_map.arm1]
  obtain ⟨t1, t2, t3, -, t5, t6, t7⟩ := mapW_twin hT h3 a tys (fun t => t.cv.name) st.name
    (by rw [hTn])
    (fun k hk => by
      have := hidT 0 (by decide) k hk
      simp only [Nat.add_zero, show (0 : Word).toNat = 0 from rfl] at this
      rw [this]; exact (hTy.2.2 k hk).1.1.1)
    (fun x w hw => lkW_name hD a (by simpa [mapLk] using hw))
  have hD₁ : StateDR m₁ st := hD.frame t2.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  -- the type types
  rcases h4 : mapW n m₁ to tn 11 2 1 with _ | ⟨⟨tyt, x2⟩, m₂⟩
  · rw [flat3_none, liftE_none, validateE.k_vi_map_2.none]; exact fun _ hk => absurd Err.cls_oob hk
  rw [flat3_some, liftE_some, validateE.k_vi_map_2.arm1]
  obtain ⟨u1, u2, u3, -, u5, u6, u7⟩ := mapW_twin t3 h4 a tys (fun t => t.cv.type) (getDeclD st)
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
  rcases h5 : listedW n m₂ to tn with _ | ⟨⟨fo, x⟩, m₃⟩
  · rw [flat3_none, liftE_none, validateE.k_vi_listed.none]; exact fun _ hk => absurd Err.cls_oob hk
  rw [flat3_some, liftE_some, validateE.k_vi_listed.arm1]
  obtain ⟨LS, l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := listedW_twin hD a tys to tn
    (fun k hk => hTy.2.2 k hk) hTn (by omega) h5 e12 u3
  have e13 := e12.trans l2
  have hD₃ : StateDR m₃ st := hD.frame e13.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  -- the constructor records' names
  rcases h6 : mapW n m₃ co cn 10 0 0 with _ | ⟨⟨cno, x3⟩, m₄⟩
  · rw [flat3_none, liftE_none, validateE.k_vi_map_3.none]; exact fun _ hk => absurd Err.cls_oob hk
  rw [flat3_some, liftE_some, validateE.k_vi_map_3.arm1]
  obtain ⟨v1, v2, v3, -, v5, v6, v7⟩ := mapW_twin l3 h6 a cts (fun c => c.cv.name) st.name
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
  -- `ifl_nodup`, the count
  rcases h7 : nodupW n m₄ fo x 0 with _ | u
  · rw [liftE_none, validateE.k_ifl_nodup.none]; exact fun _ hk => absurd Err.cls_oob hk
  rw [liftE_some]
  by_cases hu0 : u = 0
  · rw [validateE.k_ifl_nodup.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu0]
    intro _ _
    rw [hu0] at h7
    obtain ⟨i, i', -, hii, hi', heq⟩ := nodupW_zero n m₄ fo x 0 h7 (by have := l3.1; have := l3.2; omega)
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
    have := nodupW_facts n m₄ fo x 0 u h7 (by have := l3.1; have := l3.2; omega) hu0 i i' (Nat.zero_le _)
      hii (by rw [l5]; exact hi')
    rw [hkeep34 _ (by omega), hkeep34 _ hi'] at this
    exact this
  by_cases hxcn : x ≠ cn
  · rw [validateE.k_ifl_nodup.abort2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu0 hxcn]
    intro _ _
    have hlen : LS.flatten.length ≠ cts.length := fun h => hxcn (UInt64.toNat_inj.mp (by rw [l5, h, hCn]))
    obtain ⟨v, hv, hc⟩ := validateIndD_len (rcs := rcs) hVP hnd hlen
    exact .inr ⟨v, a, hv, by rw [hc, R_BLOCK_cls]⟩
  have hxcn' : x = cn := Classical.byContradiction hxcn
  rw [validateE.k_ifl_nodup.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu0 hxcn']
  have hflen : LS.flatten.length = cts.length := by rw [← l5, hxcn', hCn]
  have hfo3 : fo.toNat + LS.flatten.length ≤ topN m₃ IFL + 1 := by rw [l6, l4]; omega
  -- the tail (`vi_tail`, unfolded)
  cases n with
  | zero => simp only [viTailE, validateE.k_vi_tail.none, RefC_error]; exact fun _ hk => absurd Err.cls_outOfFuel hk
  | succ n =>
  rw [viTailE.arm1]
  rcases h9 : storeFuelW n m₄ with _ | fuel
  · rw [liftE_none, viTailE.k_store_fuel.none, validateE.k_vi_tail.none]
    exact fun _ hk => absurd Err.cls_oob hk
  rw [liftE_some, viTailE.k_store_fuel.arm1]
  have hR₄ : ArenaR m₄ a := ArenaR.frame_ext [IFL, LH] [192] (by decide) (by simp) m m₄ e14.frame a hR
  have hD₄ : StateDR m₄ st := hD.frame e14.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  have hfuel := storeFuelW_ok hR₄ h9
  have hps4 : ∀ i, i ≤ tys.length → psum m₄ to i = fpos LS i := fun i hi => by
    rw [psum_congr e14.ifr]; exact psum_fpos (fun k hk => hTy.2.2 k hk) l9 i hi
  have hLSl : LS.length = tys.length := by have := congrArg List.length l9; simpa using this
  have hcnt : ∀ k (hk : k < tys.length), cntF m₄ to k = tys[k].ctors.length := fun k hk => by
    simp only [cntF, wd, e14.ifr]; exact (hTy.2.2 k hk).2.1
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
  have hzl : (islice (k := .name) m₁ tyn.toNat tys.length).length = LS.length := by
    rw [islice_length, hLSl]
  -- the order
  have hor := order_ref (p := p) (n := n) (fuel := fuel) (st := st) (to := to) (tn := tn) (tyn := tyn)
    (fo := fo) (cno := cno) (co := co) (cn := cn) (np := np) hR₄ hD₄ v3
    (hCt.ext e14 (fun _ _ x => x.ext e14)) hCn v7
    (by rw [v6, v5]; omega) np3 hco ⟨by omega, by omega, by omega⟩ (by rw [hTn]; omega)
    (by rw [hTn]; omega)
    (fun p hp => by
      rw [hps4 _ (by omega), hTn, ← hLSl, fpos_full] at hp
      refine ⟨by omega, ?_⟩
      rw [hkeep34 p hp]; exact l8 p hp)
    (by rw [hps4 _ (by omega), hTn, ← hLSl, fpos_full, hflen]; exact Nat.le_refl _)
  rcases h10 : viOrderE p n m₄ to tn tyn fo cno co cn fuel np with e10 | ⟨oo, m₅⟩ <;> rw [h10] at hor
  · rw [viTailE.k_vi_order.none, validateE.k_vi_tail.none]
    intro hX hk
    obtain ⟨hc1, hOW⟩ := hor trivial
      (fun k hk => by
        rw [((u2.trans (l2.trans v2)).keep _ (by omega) (by omega))]; rw [hTn] at hk; exact t7 k hk) hk
    have hO := orderFail_of_W (LS := LS) (TN := islice (k := .name) m₁ tyn.toNat tys.length) hOW
      (by rw [hLSl, hTn]) (fun i hi => hps4 i (by omega)) hcntL hnnL hTNL rfl
    obtain ⟨v, hv, hc⟩ := validateIndD_orderFail_cls (rcs := rcs) hVP hnd hflen hzl hX.1 hfuel.symm hO
    exact .inr ⟨v, a, hv, by rw [hc, hc1]⟩
  rw [viTailE.k_vi_order.arm1]
  obtain ⟨o1, o2, o3, o4, o5⟩ := hor
  dsimp only at o1 o2 o3 o4 o5
  have e15 := e14.trans o2
  have hR₅ : ArenaR m₅ a := ArenaR.frame_ext [IFL, LH] [192] (by decide) (by simp) m m₅ e15.frame a hR
  have hD₅ : StateDR m₅ st := hD.frame e15.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  -- the words the twin's lists are read from
  have hTNw : ∀ i, i < tys.length → wd m₅ IFL (tyn.toNat + i) = wd m₁ IFL (tyn.toNat + i) := fun i hi =>
    ((u2.trans (l2.trans (v2.trans (o2)))).keep _ (by omega) (by omega))
  have hTTw : ∀ i, i < tys.length → wd m₅ IFL (tyt.toNat + i) = wd m₂ IFL (tyt.toNat + i) := fun i hi =>
    ((l2.trans (v2.trans (o2))).keep _ (by omega) (by omega))
  have hTN : islice (k := .name) m₅ tyn.toNat tn.toNat = islice m₁ tyn.toNat tys.length := by
    rw [hTn]; simp only [islice]; apply List.map_congr_left; intro i hi
    simp only [List.mem_range] at hi; rw [hTNw i hi]
  have hTT : islice (k := .expr) m₅ tyt.toNat tn.toNat = islice m₂ tyt.toNat tys.length := by
    rw [hTn]; simp only [islice]; apply List.map_congr_left; intro i hi
    simp only [List.mem_range] at hi; rw [hTTw i hi]
  -- the order's facts, per type and position
  have hordf : ∀ i (hi : i < LS.length) c (hc : c < LS[i].length), ∃ k,
      ∃ _ : fpos LS i + c < (ordList m₅ oo.toNat co.toNat cts cts.length).length,
        (ordList m₅ oo.toNat co.toNat cts cts.length)[fpos LS i + c] = cts[k]! ∧
        CtorOK st a cts (islice m₄ cno.toNat cts.length) LS[i][c] c
          ((islice (k := .name) m₁ tyn.toNat tys.length)[i]!) np.toNat fuel.toNat k := by
    intro i hi c hc
    have hi' : i < tys.length := by omega
    have hcn' : c < cntF m₄ to i := by rw [hcntL i hi]; exact hc
    obtain ⟨kk, w1, w2⟩ := o5 i (by omega) c hcn'
    rw [hps4 i (by omega)] at w1 w2
    have hpl := fpos_lt LS i c hi hc
    have hkk : kk < cts.length := w2.1
    refine ⟨kk, by rw [ordList_length]; omega, ?_, ?_⟩
    · rw [ordList_get, ← Nat.add_assoc, ptr_rec cts co kk hkk hco _ w1, getElem!_pos cts kk hkk]
    · rw [hnnL i hi c hc, hTNL i hi, ← Nat.add_assoc]
      exact w2
  -- the facts, for any recursor list whose records pass
  have hV : ∀ R : List IndRecRec, (∀ r ∈ (if (tys.any fun x => x.numNested != 0) = true then [] else R),
      RecOK st a (islice m₁ tyn.toNat tys.length) (islice m₂ tyt.toNat tys.length) np.toNat
        tys.length (ordList m₅ oo.toNat co.toNat cts cts.length).length fuel.toNat r) →
      VFacts st a tys cts R (islice m₁ tyn.toNat tys.length) (islice m₂ tyt.toNat tys.length) LS
        (islice m₄ cno.toNat cts.length) fuel.toNat np.toNat (ordList m₅ oo.toNat co.toNat cts cts.length) := by
    intro R hrecs
    refine ⟨hsafe, np1, np2, by simpa using t1, by simpa using u1, l1, by simpa using v1, hnd, hflen,
      hfuel.symm, islice_length _ _ _, islice_length _ _ _, hLSl, ordList_length _ _ _ _ _, hordf,
      hrecs⟩
  -- the recursors
  have hTy₅ : ListF (TyF b m₅) m₅ 11 to.toNat tys := hTy.ext e15 (fun _ _ x => x.ext e15)
  have hRc₅ : ListF (RecF b m₅) m₅ 11 ro.toNat rcs := hRc.ext e15 (fun _ _ x => x.ext e15)
  have hrs := recs_ref (p := p) (n := n) (st := st) hR₅ hD₅ hTy₅ hTn hto hRc₅ hRn hro np3
    (by have := t3.1; have := t3.2; have := u2.top; have := l2.top; have := v2.top; omega)
    (by have := u3.1; have := u3.2; omega)
    (fun i hi => by rw [hTn] at hi; rw [hTNw i hi]; exact t7 i hi)
    (to := to) (cn := cn) (tyn := tyn) (tyt := tyt) (fuel := fuel)
  rcases h12 : recsE p n m₅ to tn ro rn np cn tyn tyt fuel with e12 | ⟨u12, m₇⟩ <;> rw [h12] at hrs
  · rw [viTailE.k_vi_recs.none, validateE.k_vi_tail.none]
    intro hX hk
    obtain ⟨hc1, hany, hRF⟩ := hrs trivial hk
    rw [hTN, hTT, hTn, hCn] at hRF
    rw [← ordList_length m₅ oo.toNat co.toNat cts cts.length] at hRF
    obtain ⟨w, hw⟩ := validateIndD_recsFail (hV [] (fun r hr => by split at hr <;> simp at hr)) hany hRF
      hX.2.1 hX.2.2
    exact .inr ⟨_, a, hw, by rw [twinCls_invalid, hc1]⟩
  rw [viTailE.k_vi_recs.arm1, validateE.k_vi_tail.arm1]
  obtain ⟨hm7, hrecs⟩ := hrs
  dsimp only at hm7
  rw [hm7]
  rw [hTN, hTT, hTn, hCn, ← ordList_length m₅ oo.toNat co.toNat cts cts.length] at hrecs
  refine ⟨⟨_, validateIndD_ok (hV rcs hrecs), ordList_length _ _ _ _ _, fun p hp => ?_⟩, e15,
    ⟨o3.1, o3.2⟩, by simp only [List.headD_cons]; omega,
    by simp only [List.headD_cons]; rw [o4, o1]; omega, np3⟩
  rw [ordList_length] at hp
  obtain ⟨i, c, hi, hc, hpe⟩ := flat_pos LS p (by rw [hflen]; exact hp)
  have hcn' : c < cntF m₄ to i := by rw [hcntL i hi]; exact hc
  obtain ⟨kk, w1, w2⟩ := o5 i (by omega) c hcn'
  rw [hps4 i (by omega), Nat.add_assoc, hpe] at w1
  refine ⟨kk, w2.1, by simp only [wd, List.headD_cons] at w1 ⊢; exact w1, ?_⟩
  rw [ordList_get, ptr_rec cts co kk w2.1 hco _ w1]

end L.Front.Ind
