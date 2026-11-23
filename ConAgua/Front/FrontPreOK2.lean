module

public import ConAgua.Front.FrontPreOK1
public import ConAgua.Front.IndApplyRefine9
import ConAgua.Front.IndFieldsLink3
import ConAgua.Front.IndInstallRefine5
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Checker.NoVerdictTree
import ConAgua.Front.ApplyDeclRefine
import ConAgua.Front.IndApplyRefine
import ConAgua.Front.IndInstallRefine3
import ConAgua.Front.IndInstallRefine4
public import ConAgua.Front.IndApplySpec2
public import ConAgua.Front.IndFieldsSpec
import all ConAgua.Front.IndApply
import ConAgua.L.WordOff

@[expose] public section

/-!
# The frontend's records, word by word, II: an inductive line (lane `pipeline`)

`apply_ind`'s unified model and refinement (`applyInd_ref`): a successful `apply_ind` (on
con-leche's `ok` path of the block's scan) is the twin's `.ind` arm and appends one record of kind
`6` whose block offset is the old top of `DLP` plus one, changing neither the old records nor the
pool up to its old top (`DGrow`); its failure is the line's verdict. `installW_grow` is the first part of
`installW_twin`'s proof (`IndInstallRefine5.lean`, up to the record's push): the frames come out of
the twin's install loop (`instGo_twin`), so the twin's hypotheses stay.
-/

set_option experimental.vcgen true

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open Std.WP
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec CVRec RuleRec DeclRec scanIndDecl)


namespace L.Front.Ind

/-- **`install_ind_d` appends one inductive record.** -/
theorem installW_grow {b : ByteArray} {n : Nat} {m m' : Mem} (a : AState) {st : StateD}
    (hD : StateDR m st)
    {to tn co cn ro rn oo tf np : Word} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} {ordered : List (IndCtorRec × NIdx)}
    (hF : IndFR b m to tn co cn ro rn tys cts rcs) (hIFR : topN m IFR < 2 ^ 62)
    (hIFL : topN m IFL < 2 ^ 62) (hord : ordered.length = cts.length)
    (hoo : oo.toNat + cts.length < 2 ^ 63) (htf : tf.toNat + cts.length < 2 ^ 63)
    (hptr : ∀ p (hp : p < ordered.length), ∃ k, ∃ _ : k < cts.length,
      wd m IFL (oo.toNat + p) = co + 10 * UInt64.ofNat k ∧ (wd m IFL (tf.toNat + p)).toNat < 2 ^ 32 ∧
        ordered[p] = (cts[k], decI (wd m IFL (tf.toNat + p))))
    (h : installW b.data n m to tn oo tf cn ro rn np = some m') : DGrow m m' := by
  obtain ⟨hTn, hTy, hCn, hCt, hRn, hRc⟩ := hF
  have hL := StateDR.lkR hD
  have hps := hL.psize
  have hpt := hL.ptop
  have hTyB := hTy.2.1
  have hCtB := hCt.2.1
  have hRcB := hRc.2.1
  cases n with
  | zero => simp [installW] at h
  | succ n =>
  by_cases hbig : 4294967296 ≤ tn ∨ 4294967296 ≤ cn ∨ 4294967296 ≤ rn
  · rw [installW.abort1 (hc1 := hbig)] at h; cases h
  rw [installW.arm1 (hc1 := hbig)] at h
  have ht32 : tn.toNat < 2 ^ 32 := Classical.byContradiction fun h' =>
    hbig (.inl (UInt64.le_iff_toNat_le.mpr (by simp; omega)))
  have hc32 : cn.toNat < 2 ^ 32 := Classical.byContradiction fun h' =>
    hbig (.inr (.inl (UInt64.le_iff_toNat_le.mpr (by simp; omega))))
  have hr32 : rn.toNat < 2 ^ 32 := Classical.byContradiction fun h' =>
    hbig (.inr (.inr (UInt64.le_iff_toNat_le.mpr (by simp; omega))))
  have hN : (tn + cn + rn).toNat = tys.length + cts.length + rcs.length := by
    rw [UInt64.toNat_add, UInt64.toNat_add]; omega
  rcases h1 : allocW m DLP (tn + cn + rn) with _ | ⟨bo, m₁⟩ <;>
    simp only [h1, installW.k_dind_alloc.none, installW.k_dind_alloc.arm1, reduceCtorEq] at h
  obtain ⟨P1, P2, P3, P4, P5⟩ := allocP_facts hps hpt h1
  rw [hN] at P3 P4
  have hL1 : LkR m₁ st := hL.frame P1.frame (by rw [P3, P1.size DLP]; omega)
  rcases h2 : instTypesW b.data n m₁ bo to tn 0 with _ | m₂ <;>
    simp only [h2, installW.k_inst_types.none, installW.k_inst_types.arm1, reduceCtorEq] at h
  rcases h3 : instCtorsW b.data n m₂ (bo + tn) oo tf cn 0 with _ | m₃ <;>
    simp only [h3, installW.k_inst_ctors.none, installW.k_inst_ctors.arm1, reduceCtorEq] at h
  rcases h4 : instRecsW b.data n m₃ (bo + tn + cn) ro rn 0 with _ | m₄ <;>
    simp only [h4, installW.k_inst_recs.none, installW.k_inst_recs.arm1, installW.k_decl_push_id, reduceCtorEq] at h
  have hifr1 : m₁.arr64 IFR = m.arr64 IFR := P1.other IFR (by decide) (by decide)
  have hifl1 : m₁.arr64 IFL = m.arr64 IFL := P1.other IFL (by decide) (by decide)
  -- the types
  rw [instTypesW_eq] at h2
  obtain ⟨T1, T2, T3, T4, T5⟩ := instGo_twin a tys (tyT st) (fun _ m _ p => typeW b.data m p)
    (fun _ j => to + 11 * j) m₁ bo tn hTn (fun n' mi k q mo hLi hf hk hR => by
      have hifr : mi.arr64 IFR = m.arr64 IFR := by rw [hf.1 IFR (by decide) (by decide), hifr1]
      have hk' := @L.toNat_ofNat_of_lt k (by omega)
      have hw : (to + 11 * UInt64.ofNat k).toNat = to.toNat + 11 * k := by
        have := w_addmul to (UInt64.ofNat k) 11 (by decide) (by rw [hk']; omega)
        rw [hk'] at this; exact this
      rw [getElem!_eq _ _ hk]
      exact typeW_twin a hLi (by rw [hw]; exact ((hTy.2.2 k hk).1).congr hifr) (by rw [hw]; omega) hR)
    n m₁ m₂ 0 hL1 (MemFrame.refl _ _ _) (by simp) (by omega) (by omega) h2
  simp only [UInt64.toNat_zero, Nat.add_zero] at T4 T5
  -- the constructors
  have hbt : (bo + tn).toNat = bo.toNat + tys.length := by rw [L.toNat_add_of_lt _ _ (by omega), hTn]
  rw [instCtorsW_eq] at h3
  obtain ⟨C1, C2, C3, C4, C5⟩ := instGo_twin a ordered (fun c => ctT st c.1 c.2)
    (fun _ m j p => ctorRW b.data m p (rdW (m.arr64 IFL) (tf + j)))
    (fun m j => rdW (m.arr64 IFL) (oo + j)) m₂ (bo + tn) cn (by rw [hCn, hord])
    (fun n' mi p q mo hLi hf hp hR => by
      have hifr : mi.arr64 IFR = m.arr64 IFR := by
        rw [hf.1 IFR (by decide) (by decide), T1.1 IFR (by decide) (by decide), hifr1]
      have hifl : mi.arr64 IFL = m.arr64 IFL := by
        rw [hf.1 IFL (by decide) (by decide), T1.1 IFL (by decide) (by decide), hifl1]
      obtain ⟨k, hk, hw, htt, hok⟩ := hptr p hp
      have hp' := @L.toNat_ofNat_of_lt p (by omega)
      have hrd : rdW (mi.arr64 IFL) (oo + UInt64.ofNat p) = co + 10 * UInt64.ofNat k := by
        rw [hifl, rdW_wdI _ _ _ _ (by rw [hp']; omega), hp', hw]
      have hrdT : rdW (mi.arr64 IFL) (tf + UInt64.ofNat p) = wd m IFL (tf.toNat + p) := by
        rw [hifl, rdW_wdI _ _ _ _ (by rw [hp']; omega), hp']
      have hk' := @L.toNat_ofNat_of_lt k (by omega)
      have hw' : (co + 10 * UInt64.ofNat k).toNat = co.toNat + 10 * k := by
        have := w_addmul co (UInt64.ofNat k) 10 (by decide) (by rw [hk']; omega)
        rw [hk'] at this; exact this
      rw [getElem!_eq _ _ hp, hok]
      rw [hrd, hrdT] at hR
      exact ctorRW_twin a hLi (by rw [hw']; exact (hCt.2.2 k hk).congr hifr) (by rw [hw']; omega) htt hR)
    n m₂ m₃ 0 T3 (MemFrame.refl _ _ _) (by simp) (by rw [hbt]; omega) (by rw [hbt, hord]; omega) h3
  rw [hbt, hord] at C4 C5
  simp only [UInt64.toNat_zero, Nat.add_zero] at C4 C5
  -- the recursors
  have hbtc : (bo + tn + cn).toNat = bo.toNat + tys.length + cts.length := by
    rw [L.toNat_add_of_lt _ _ (by rw [hbt]; omega), hbt, hCn]
  rw [instRecsW_eq] at h4
  obtain ⟨R1, R2, R3, R4, R5⟩ := instGo_twin a rcs (recT st) (fun n m _ p => recRW b.data n m p)
    (fun _ j => ro + 11 * j) m₃ (bo + tn + cn) rn hRn
    (fun n' mi k q mo hLi hf hk hR => by
      have hifr : mi.arr64 IFR = m.arr64 IFR := by
        rw [hf.1 IFR (by decide) (by decide), C1.1 IFR (by decide) (by decide),
          T1.1 IFR (by decide) (by decide), hifr1]
      have hifl : mi.arr64 IFL = m.arr64 IFL := by
        rw [hf.1 IFL (by decide) (by decide), C1.1 IFL (by decide) (by decide),
          T1.1 IFL (by decide) (by decide), hifl1]
      have hk' := @L.toNat_ofNat_of_lt k (by omega)
      have hw : (ro + 11 * UInt64.ofNat k).toNat = ro.toNat + 11 * k := by
        have := w_addmul ro (UInt64.ofNat k) 11 (by decide) (by rw [hk']; omega)
        rw [hk'] at this; exact this
      rw [getElem!_eq _ _ hk]
      exact recRW_twin a hLi (by rw [hw]; exact (hRc.2.2 k hk).congr hifr hifl) (by rw [hw]; omega)
        (by unfold topN wd; rw [hifl]; exact hIFL) hR)
    n m₃ m₄ 0 C3 (MemFrame.refl _ _ _) (by simp) (by rw [hbtc]; omega) (by rw [hbtc]; omega) h4
  rw [hbtc] at R4 R5
  simp only [UInt64.toNat_zero, Nat.add_zero] at R4 R5
  -- the push
  have hfr4 : MemFrame [DLP] [] m m₄ := P1.frame.trans (T1.trans (C1.trans R1))
  have hdecl4 : m₄.arr64 DECL = m.arr64 DECL := hfr4.arr DECL (by decide) (by decide)
  obtain ⟨G1, G2, G3, G4, G5, w0, w1, w2, w3, w4, w5, w6, w7⟩ :=
    pushW_facts m₄ m' _ _ _ _ _ _ _ _ (rdW (m.arr64 DECL) 0) (by rw [hdecl4]) h
      (by rw [hdecl4]; exact hD.decls.dsize)
  have hm'P : m'.arr64 DLP = m₄.arr64 DLP := G1.1 DLP (by simp) (by decide)
  have hs4 : (m₄.arr64 DLP).size = (m.arr64 DLP).size := hfr4.size DLP
  have hkeep : ∀ j, 1 ≤ j → j ≤ topN m DLP → wd m₄ DLP j = wd m DLP j := fun j h1 h2 => by
    rw [R4 j h1 (by omega) (.inl (by omega)), C4 j h1 (by omega) (.inl (by omega)),
      T4 j h1 (by omega) (.inl (by omega)), P1.keep j h1 h2]
  have hc1 : (rdW (m.arr64 DECL) 0 + 1).toNat = (rdW (m.arr64 DECL) 0).toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have hcnt : dcnt m = (rdW (m.arr64 DECL) 0).toNat := rfl
  have hcnt' : dcnt m' = dcnt m + 1 := by
    rw [show dcnt m' = (rdW (m.arr64 DECL) 0 + 1).toNat by unfold dcnt; rw [G4]; rfl, hc1, hcnt]
  refine ⟨fun j h1 h2 => ?_, fun j h1 h2 => ?_, fun x h1 h2 => ?_, ?_⟩
  rotate_right
  · show topN m DLP ≤ topN m' DLP
    have e : topN m' DLP = topN m₄ DLP := by simp only [topN, wd, hm'P]
    rw [e]; omega
  · rw [G5 j h1 (by omega), hdecl4]
  · have h2' : j ≤ topN m DLP := h2
    rw [hm'P]; exact getElem?_of_wd hs4 (by omega) (hkeep j h1 h2')
  · have hx : x = (rdW (m.arr64 DECL) 0).toNat := by omega
    subst hx
    refine ⟨fun h6 => absurd w0 h6, fun _ => ?_⟩
    rw [w2]
    intro h0
    have := congrArg UInt64.toNat h0
    simp only [UInt64.toNat_zero] at this
    omega


theorem DGrow.ofDK {m m₁ m' : Mem} (hk : DK m m₁) (hg : DGrow m₁ m') : DGrow m m' := by
  have hc : dcnt m₁ = dcnt m := by simp only [dcnt, hk.1]
  have ht : dtop m₁ = dtop m := by simp only [dtop, hk.2]
  refine ⟨fun j h1 h2 => ?_, fun j h1 h2 => ?_, fun x h1 h2 => hg.new x (by omega) h2, by
    have := hg.top; omega⟩
  · rw [hg.decl j h1 (by omega), hk.1]
  · rw [hg.dlp j h1 (by omega), hk.2]

/-! ## `apply_ind`: one model and one refinement -/

/-- **`apply_ind`'s unified model**: `ind_fields` and `install_ind_d` (outside the verdict closure)
lifted, `validate_ind_d` through its run (the install needs the input bytes kept, `Keep`, which
comes from the run). -/
l_model applyInd_specE (p : Prog) (hf : p.lookup "apply_ind" = some applyInd)
  fns [hf ↦ applyIndE] specs [callW_spec p n "ind_fields", callW_spec p n "install_ind_d"]
  grind [arena_grind] unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `validateIndD`'s verdict is the `.ind` line's. -/
theorem claimR_of_validate {st : StateD} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} {a : AState} {e : Err}
    (h : VerdictClaimL (ConRon.Arena.Frontend.validateIndD st tys cts rcs) a e) :
    VerdictClaimR (applyRecord st (.decl (.ind tys cts rcs))) a e := by
  intro hk
  have hrun : (applyRecord st (.decl (.ind tys cts rcs))).run a =
      (processLineCoreD st (.ind tys cts rcs)).run a := rfl
  rcases h hk with ⟨ce, hce, hc⟩ | ⟨v, a', hv, hc⟩
  · refine .inl ⟨ce, ?_, hc⟩
    rw [hrun]; unfold processLineCoreD
    simp only [StateT.run_bind, show (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = _ from hce]
    rfl
  · refine .inr ⟨v, a', ?_, hc⟩
    rw [hrun]; unfold processLineCoreD
    simp only [StateT.run_bind, show (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = _ from hv]
    rfl

/-- What `apply_ind`'s error arms assume: the no-verdict closure (the lifted callees,
`validate_ind_d`'s spec) and the twin's name reads (`validate_ref`'s `XV`). -/
structure ApplyIndG (p : Prog) (st : StateD) (a : AState) : Prop where
  nv : closedNV p _root_.L.Checker.nvFns = true
  xv : XV st a

/-- What a successful `apply_ind` from `m` gives at `m'`: the twin's `.ind` arm accepts (the state
`a` unchanged) at a related state, the arena kept, the mode kept, one record appended. -/
structure ApplyIndPost (st : StateD) (a : AState) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) (m m' : Mem) : Prop where
  twin : ∃ st', (processLineCoreD st (.ind tys cts rcs)).run a = .ok (.inl st', a) ∧ StateDR m' st'
  arena : ArenaD m' a
  mode : ModeOK m → ModeOK m'
  grow : DGrow m m'

/-- **`apply_ind` refines the `.ind` arm of `processLineCoreD`, both outcomes**: on con-leche's
`ok` path of the block's scan (`scanIndDecl`), `ind_fields` gives the three lists
(`indFields_link`), `validate_ind_d` the twin's `validateIndD` (`validate_ref`: its verdict
`.inr (ordered, nPd)`, or its record verdict, the line's), `install_ind_d` its `installIndD`
(`installW_twin`, `installW_grow`). -/
@[refines_part ConRon.Arena.Frontend.processLineCoreD "inductive"]
theorem applyInd_ref {p : Prog} (hAL : IndApplyLookups p) (hFI : IndFieldLookups p)
    (hII : IndInstallLookups p) {b : ByteArray} (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) {m : Mem} {a : AState} {st : StateD} (hm : m.arr8 IN = b.data)
    (hA : ArenaD m a) (hD : StateDR m st) (hok : ConRon.Bridge.StateOK a) {v : USize}
    {tys : List IndTypeRec} {cts : List IndCtorRec} {rcs : List IndRecRec} {e : USize}
    (hscan : scanIndDecl b v = .ok (.ind tys cts rcs) e) :
    RefC (ApplyIndG p st a) (applyIndE p n m v.toUInt64) (fun x => ApplyIndPost st a tys cts rcs m x.2)
      (VerdictClaimR (applyRecord st (.decl (.ind tys cts rcs))) a) := by
  have hno := hAL.decl.expr.no_st8
  cases n with
  | zero => simp only [applyIndE, RefC_error]; exact fun _ hk => absurd Err.cls_outOfFuel hk
  | succ n =>
  rw [applyIndE.arm1]
  -- `ind_fields`
  rcases h1 : callW p n "ind_fields" [v.toUInt64] m with _ | ⟨r, m₁⟩
  · rw [liftE_none, applyIndE.k_ind_fields.none]; exact fun _ hk => absurd (by simp) hk
  rw [liftE_some, applyIndE.k_ind_fields.arm1]
  obtain ⟨s1, rfl, ⟨-, hW1⟩, hK1, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (Triple.keep hno (indFields_spec p hFI b.data hsize n ⟨m, Locals.init []⟩ hm v.toUInt64)) h1
  have hifs := hD.ifs
  obtain ⟨to, tn, co, cn, ro, rn, rfl, hF, hfR⟩ :=
    indFields_link b h64 hsize m s1.mem ⟨by omega, by omega⟩ v tys cts rcs e hscan _ hW1
  have hfr1 : MemFrame [IFR, IFL] [] m s1.mem := hfR.1
  have hRoom : Room s1.mem := hfR.2
  simp only [List.headD_cons, List.tail_cons]
  have hA1 : ArenaD s1.mem a :=
    ⟨ArenaR.frame_ext _ _ (by simp [IFR, IFL]) (by simp) _ _ hfr1 _ hA.base,
      DerR.frameT hfr1 (by simp [IFR, IFL]) hA.der⟩
  have hD1 : StateDR s1.mem st := hD.frame hfr1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1 : (s1.mem.arr64 IFR).size = (m.arr64 IFR).size := hfr1.size IFR
  have hs1' : (s1.mem.arr64 IFL).size = (m.arr64 IFL).size := hfr1.size IFL
  have hT1 : TopOK s1.mem := ⟨by have := hRoom.2.1; exact this, Nat.le_of_lt hRoom.2.2.2⟩
  have hIFR1 : topN s1.mem IFR < 2 ^ 62 := by have := hRoom.2.2.1; omega
  have hV := validate_ref hA1.base hD1 hok hT1 hF hIFR1 p n (st := st)
  have hsV := validate_specE p hAL n ⟨s1.mem, Locals.init []⟩ to tn co cn ro rn
  -- `validate_ind_d`
  cases h2 : callE p n "validate_ind_d" [to, tn, co, cn, ro, rn] s1.mem with
  | error e2 =>
    rw [applyIndE.k_validate_ind_d.none]
    exact fun hG => claimR_of_validate
      (RefC.run_err hsV (fun _ h0 h => absurd h0 h) hG.nv hG.xv hV h2)
  | ok q2 =>
  obtain ⟨q, m₂⟩ := q2
  rw [applyIndE.k_validate_ind_d.arm1]
  obtain ⟨s2, hs2, -, hV2⟩ := RefC.run_ok hsV hV h2
  obtain ⟨s2', hs2', -, hK2, -⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (Triple.keep hno (callW_spec p n "validate_ind_d" [to, tn, co, cn, ro, rn] ⟨s1.mem, Locals.init []⟩))
    (callW_of_callE h2)
  rw [hs2] at hV2
  rw [hs2'] at hK2
  obtain ⟨⟨ordered, V1, V4, V7⟩, V2, V3, V5, V6, V5T, V6T, V8⟩ := hV2
  dsimp only at V1 V2 V3 V4 V5 V6 V7 V8 V5T V6T
  -- `install_ind_d`
  rcases h3 : callW p n "install_ind_d" [to, tn, q.headD 0, q.tail.headD 0, cn, ro, rn, q.tail.tail.headD 0] m₂
    with _ | ⟨r3, m₃⟩
  · rw [liftE_none, applyIndE.k_install_ind_d.none]; exact fun _ hk => absurd (by simp) hk
  rw [liftE_some, applyIndE.k_install_ind_d.arm1]
  have hm2 : m₂.arr8 IN = b.data := by rw [hK2.arr8, hK1.arr8]; exact hm
  obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (install_spec p hAL hII b.data hsize n ⟨m₂, Locals.init []⟩ to tn (q.headD 0) (q.tail.headD 0) cn ro rn
      (q.tail.tail.headD 0) hm2) h3
  generalize q.headD 0 = oo at *
  generalize q.tail.tail.headD 0 = np at *
  generalize q.tail.headD 0 = tf at *
  have hfr2 := V2.frame
  have hA2 : ArenaD m₂ a :=
    ⟨ArenaR.frame_ext _ _ (by simp [IFL, LH]) (by simp) _ _ hfr2 _ hA1.base,
      DerR.frameT hfr2 (by simp [IFL, LH]) hA1.der⟩
  have hD2 : StateDR m₂ st := hD1.frame hfr2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hifr2 : m₂.arr64 IFR = s1.mem.arr64 IFR := V2.ifr
  have hs2'' : (m₂.arr64 IFL).size = (m.arr64 IFL).size := by rw [hfr2.size IFL, hs1']
  have hIFR2 : topN m₂ IFR < 2 ^ 62 := by unfold topN wd; rw [hifr2]; exact hIFR1
  have hIFL2 : topN m₂ IFL < 2 ^ 62 := by have := V3.2; omega
  obtain ⟨st', I1, I2, I3, I4⟩ := installW_twin hA2 hD2 (hF.ext V2) hIFR2 hIFL2 V4 (by omega) (by omega) V7 (by omega) hW3
  have hk : DK m m₂ := (DK.ofFrame hfr1 (by decide) (by decide)).trans
    (DK.ofFrame hfr2 (by decide) (by decide))
  refine ⟨⟨st', ?_, I3⟩, I2, fun hmo => MemFrame.modeOK I4 (by simp) (by simp)
    (MemFrame.modeOK hfr2 (by decide) (by decide) (MemFrame.modeOK hfr1 (by simp) (by simp) hmo)),
    DGrow.ofDK hk (installW_grow a hD2 (hF.ext V2) hIFR2 hIFL2 V4 (by omega) (by omega) V7 hW3)⟩
  unfold processLineCoreD
  simp only []
  rw [run_bind _ _ a _ V1]
  simp only []
  rw [run_bind _ _ a _ I1]
  rfl


end L.Front.Ind
