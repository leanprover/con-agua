import ConAgua.Arena.InstLPEntry
import ConAgua.Arena.IndRealAbsT
import ConAgua.Arena.StageTLift
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# `inst_lp_fast` under `CoreS` and under `StageT` (lane `indproofs4`, helper `ilp`)

`inst_lp_fast(f, lo, ll, us, e)` (`InstLP.lean`'s `instLPFastL`, lane `induct`'s convention: the
keys an `IW` slice, the fuel explicit, anything but `coreWalkFuel` aborts): `keys_push_iw` copies
the keys onto the spine stack (`ik_copy`), then the shared walk entry `inst_lp_core`, then the stack
top put back. Lane `whnf`'s `instLP_refines` (`InstLPEntry.lean`) is the same function with the keys
from the record pool (`keys_push`, `ek_copy`); its proof carries over word for word.

* `instLPFastI_refines`: `inst_lp_fast` refines `instLPFast f lps us e` under `CoreS`, `(lo, ll)`
  an `IW` slice decoding to `lps`.
* The model `ilpfF := callF ilpfP "inst_lp_fast"` over the call-closed program `ilpfP` (108
  functions: the walk, the level and expression interning, and what the walk's program bundle
  `ILWEntryProg` names), its write set `ilpfA`/`ilpfC` (no pool, record, pin or stage-memo array,
  none of `AbsOK`'s own memos 51, 155 and epochs 52, 158).
* `ilpfF_okT`: the contract `IndStubs.instLPFast_spec` under `StageT` (the twin's invariants
  `TwinOK` are what `CoreS` needs; `StageR` alone does not carry them), with `AbsOK` kept.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `ik_copy`, `keys_push_iw`, `inst_lp_fast`: the word models -/

/-- **The model of `ik_copy`.** -/
def ikCopyW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, s, d, l =>
    if l = 0 then some m else ikCopyW n (m.set64 SPN d (rdW (m.arr64 LPIW) s)) (s + 1) (d + 1) (l - 1)

theorem ikCopyW_zero (n : Nat) (m : Mem) (s d l : Word) (h : l = 0) :
    ikCopyW (n + 1) m s d l = some m := by simp [ikCopyW, h]
theorem ikCopyW_succ (n : Nat) (m : Mem) (s d l : Word) (h : l ≠ 0) :
    ikCopyW (n + 1) m s d l = ikCopyW n (m.set64 SPN d (rdW (m.arr64 LPIW) s)) (s + 1) (d + 1) (l - 1) := by
  simp [ikCopyW, h]
grind_pattern [arena_grind] ikCopyW_zero => ikCopyW (n + 1) m s d l
grind_pattern [arena_grind] ikCopyW_succ => ikCopyW (n + 1) m s d l

/-- **The model of `keys_push_iw`.** -/
def keysPushIWW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, lo, ll =>
    if m.len64 SPN < spTop m then none
    else if m.len64 SPN - spTop m < ll then none
    else kpK (spTop m) ll (ikCopyW n m lo (spTop m) ll)

/-- **The model of `inst_lp_fast`** at L fuel `n + 1`. -/
def ilpfW (p : Prog) (n : Nat) (m : Mem) (f lo ll us e : Word) : Option (Word × Mem) :=
  if f ≠ 4000000000 then none else ilwLPK₁ p n ll us e (callW p n "keys_push_iw" [lo, ll] m)

section specs
variable (p : Prog) (hkp : p.lookup "keys_push_iw" = some keysPushIW) (hik : p.lookup "ik_copy" = some ikCopy)
  (hf : p.lookup "inst_lp_fast" = some instLPFastL)

include hik in
theorem ikCopy_spec (n : Nat) : ∀ (s₀ : St) (s d l : Word),
    ⦃fun st => st = s₀⦄
    invoke p (exec p n) "ik_copy" [s, d, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ ikCopyW n s₀.mem s d l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ s d l; rw [invoke_eq _ hik]; simp only [callFn, ikCopy]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ s d l
    rw [invoke_eq _ hik]
    simp only [callFn, ikCopy]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish

include hkp hik in
theorem keysPushIW_spec (n : Nat) (s₀ : St) (lo ll : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "keys_push_iw" [lo, ll]
    ⦃fun r s' => LocEq s' s₀ ∧ keysPushIWW n s₀.mem lo ll = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hkp]
  simp only [callFn, keysPushIW]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        ikCopy_spec p hik n] <;>
      finish [keysPushIWW, spTop]

include hf in
theorem instLPFast_specW (n : Nat) (s₀ : St) (f lo ll us e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "inst_lp_fast" [f, lo, ll, us, e]
    ⦃fun r s' => LocEq s' s₀ ∧ ilpfW p n s₀.mem f lo ll us e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hf]
  simp only [callFn, instLPFastL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "keys_push_iw", callW_spec p n "inst_lp_core"] <;>
    finish [ilpfW]

end specs

/-! ## The refinement under `CoreS` (lane `whnf`'s `instLP_refines`, the keys from `IW`) -/

theorem ikCopyW_slice : ∀ (lps : List NIdx) (n : Nat) (m m' : Mem) (s d l : Word),
    hslice? (m.arr64 LPIW) s.toNat l.toNat = some lps → d.toNat + l.toNat ≤ (m.arr64 SPN).size →
    (m.arr64 SPN).size < 2 ^ 63 → s.toNat + l.toNat < 2 ^ 64 → ikCopyW n m s d l = some m' →
    hslice? (m'.arr64 SPN) d.toNat l.toNat = some lps ∧ MemFrame [SPN] [] m m' ∧
      ∀ i : Word, i.toNat < d.toNat → rdW (m'.arr64 SPN) i = rdW (m.arr64 SPN) i := by
  intro lps
  induction lps with
  | nil =>
    intro n m m' s d l hs hb hsz hsl hW
    have hl : l.toNat = 0 := by
      rcases hk' : l.toNat with _ | j
      · rfl
      · rw [hk', lp_hslice_succ] at hs
        simp only [Option.bind_eq_bind] at hs
        cases e : (hd? (m.arr64 LPIW) s.toNat : Option NIdx) with
        | none => simp [e] at hs
        | some x =>
          cases e' : (hslice? (m.arr64 LPIW) (s.toNat + 1) j : Option (List NIdx)) with
          | none => simp [e, e'] at hs
          | some xs => simp [e, e'] at hs
    have hl0 : l = 0 := UInt64.toNat_inj.mp (by simpa using hl)
    subst hl0
    rcases n with _ | n
    · simp [ikCopyW] at hW
    rw [ikCopyW_zero n m s d 0 rfl] at hW; cases hW
    exact ⟨by simp [hslice?], MemFrame.refl _ _ _, fun _ _ => rfl⟩
  | cons x xs ih =>
    intro n m m' s d l hs hb hsz hsl hW
    rcases hk' : l.toNat with _ | j
    · rw [hk'] at hs; simp [hslice?] at hs
    rw [hk', lp_hslice_succ] at hs
    simp only [Option.bind_eq_bind] at hs
    cases e : (hd? (m.arr64 LPIW) s.toNat : Option NIdx) with
    | none => simp [e] at hs
    | some x' =>
    cases e' : (hslice? (m.arr64 LPIW) (s.toNat + 1) j : Option (List NIdx)) with
    | none => simp [e, e'] at hs
    | some xs' =>
    simp only [e, e', Option.bind_some, Option.pure_def, Option.some.injEq, List.cons.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have hl0 : l ≠ 0 := fun h0 => by subst h0; simp at hk'
    rcases n with _ | n
    · simp [ikCopyW] at hW
    rw [ikCopyW_succ n m s d l hl0] at hW
    have hd1 : (d + 1).toNat = d.toNat + 1 := L.Arena.toNat_succ_lt (by omega)
    have hs1 : (s + 1).toNat = s.toNat + 1 := L.Arena.toNat_succ_lt (by omega)
    have hlm : (l - 1).toNat = j := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    have hsz₁ : ((m.set64 SPN d (rdW (m.arr64 LPIW) s)).arr64 SPN).size = (m.arr64 SPN).size :=
      Mem.size_arr64_set64 _ _ _ _
    have herec : (m.set64 SPN d (rdW (m.arr64 LPIW) s)).arr64 LPIW = m.arr64 LPIW :=
      Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    obtain ⟨hk', hf', hb'⟩ := ih n _ m' (s + 1) (d + 1) (l - 1) (by rw [herec, hs1, hlm]; exact e')
      (by rw [hsz₁, hd1, hlm]; omega) (by rw [hsz₁]; exact hsz) (by rw [hs1, hlm]; omega) hW
    have hdl : d.toNat < (m.arr64 SPN).size := by omega
    have hd : rdW (m'.arr64 SPN) d = rdW (m.arr64 LPIW) s := by
      rw [hb' d (by rw [hd1]; omega), rdW_set64]; simp [hdl]
    refine ⟨?_, (MemFrame.set64 _ _ (by decide) _ _).trans hf', ?_⟩
    · rw [lp_hslice_succ]
      have hsize : d.toNat < (m'.arr64 SPN).size := by rw [hf'.2.2.1 SPN, hsz₁]; exact hdl
      have hd' : (hd? (m'.arr64 SPN) d.toNat : Option NIdx) = some x' := by
        rw [← e]; simp only [hd?]
        have h1 : (m'.arr64 SPN)[d.toNat]? = some (rdW (m'.arr64 SPN) d) := by simp [rdW, hsize]
        have h2 : (m.arr64 LPIW)[s.toNat]? = some (rdW (m.arr64 LPIW) s) := by
          cases ee : (m.arr64 LPIW)[s.toNat]? with
          | none => simp [hd?, ee] at e
          | some v => simp [rdW, ee]
        rw [h1, h2, hd]
      rw [hd1, hlm] at hk'
      simp [hd', hk']
    · intro i hi
      rw [hb' i (by rw [hd1]; omega), rdW_set64]
      have : ¬ d = i := fun e => by subst e; omega
      simp [this]

/-- **`inst_lp_fast(f, lo, ll, us, e)` refines `instLPFast f lps us e`** under `CoreS`, the keys
`lps` a slice of the work pool `IW` (the fuel word `coreWalkFuel`, else the call aborts). -/
theorem instLPFastI_refines (p : Prog) (hp : ILWEntryProg p)
    (hkp : p.lookup "keys_push_iw" = some keysPushIW) (hik : p.lookup "ik_copy" = some ikCopy)
    (hf : p.lookup "inst_lp_fast" = some instLPFastL) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb f po pl us e : Word) (lps : List NIdx) (hS : CoreS dn s₀.mem a₀ vis fe M eb) (he : HW e)
    (hus : HW us) (hlps : hslice? (s₀.mem.arr64 LPIW) po.toNat pl.toNat = some lps)
    (hsz0 : (s₀.mem.arr64 LPIW).size < 2 ^ 64) :
    CoreSpec p n "inst_lp_fast" [f, po, pl, us, e]
      (instLPFast f.toNat lps (decI us) (decE e)) decH s₀ a₀ dn vis fe M eb := by
  apply CoreSpec.of_call
  intro rs m' hc
  rcases n with _ | k
  · rw [callW_zero] at hc; cases hc
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (instLPFast_specW p hf k _ f po pl us e) hc
  rw [hs'] at hW
  change ilpfW p k s₀.mem f po pl us e = some (rs.headD 0, m') at hW
  unfold ilpfW at hW
  obtain ⟨hf0, hW⟩ := of_ite_none hW
  obtain rfl : f = 4000000000 := by simpa using hf0
  rw [show (4000000000 : Word).toNat = coreWalkFuel from rfl]
  generalize s₀.mem = m at hS hlps hW hsz0
  -- `keys_push_iw`
  rcases h1 : callW p k "keys_push_iw" [po, pl] m with _ | ⟨bs, m₁⟩
  · rw [h1] at hW; cases hW
  rw [h1, ilwLPK₁_some] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (keysPushIW_spec p hkp hik k _ po pl) h1
  rw [hs1] at hW1
  change keysPushIWW k m po pl = some (bs.headD 0, m₁) at hW1
  rcases k with _ | k
  · simp [keysPushIWW] at hW1
  simp only [keysPushIWW] at hW1
  have hsz := hS.spn
  have hlen : (m.len64 SPN).toNat = (m.arr64 SPN).size := L.Front.toNat_ofNat_size _ (by omega)
  by_cases t1 : m.len64 SPN < spTop m
  · simp [t1] at hW1
  by_cases t2 : m.len64 SPN - spTop m < pl
  · simp [t1, t2] at hW1
  simp only [t1, t2, ↓reduceIte] at hW1
  have t1' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp t1)
  have t2' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp t2)
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp t1), hlen] at t2'
  rw [hlen] at t1'
  cases hcp : ikCopyW k m po (spTop m) pl with
  | none => rw [hcp] at hW1; simp [kpK] at hW1
  | some mc =>
  rw [hcp, kpK_some] at hW1
  obtain ⟨hb, rfl⟩ := Prod.mk.inj (Option.some.inj hW1)
  have hnw : po.toNat + pl.toNat < 2 ^ 64 := by
    rcases hslice?_bound_fsz _ _ _ _ hlps with h0 | h0
    · have := po.toNat_lt; omega
    · omega
  obtain ⟨hsl, hfc, hbc⟩ := ikCopyW_slice lps k m mc po (spTop m) pl hlps (by omega) hsz hnw hcp
  have hctl := hS.ctl136
  have hfm : MemFrame [SPN] [136] m (mc.set64 CTL 136 (spTop m + pl)) :=
    (hfc.mono (by simp) (by simp)).trans ((MemFrame.setCtl _ _ _).mono (by simp) (by simp))
  have hS₁ : CoreS dn (mc.set64 CTL 136 (spTop m + pl)) a₀ vis fe M eb :=
    hS.frame_stk hfm (by simp) (by simp)
  have hspn₁ : (mc.set64 CTL 136 (spTop m + pl)).arr64 SPN = mc.arr64 SPN :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have htop₁ : (spTop (mc.set64 CTL 136 (spTop m + pl))).toNat = (spTop m).toNat + pl.toNat := by
    have hc' : (136 : Word).toNat < (mc.arr64 CTL).size := by rw [hfc.2.2.1 CTL]; simpa using hctl
    simp only [spTop]; rw [rdW_set64]; simp only [hc', and_self, ↓reduceIte]
    rw [UInt64.toNat_add]; simp only [spTop] at t1' t2' ⊢; omega
  -- the core
  rw [← hb] at hW
  rcases h2 : callW p (k + 1) "inst_lp_core" [spTop m, pl, us, e] (mc.set64 CTL 136 (spTop m + pl)) with _ | ⟨r2, m₂⟩
  · rw [h2] at hW; cases hW
  rw [h2, ilwLPK₂_some] at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨hok, ⟨M', hS₂, hK₂, hSt₂⟩, hres, hw⟩ := ilwCore_ok hp k hS₁ he hus (by rw [hspn₁]; exact hsl)
    (Nat.le_of_eq htop₁.symm) h2
  -- the stack top put back
  have hfb : MemFrame [] [136] m₂ (m₂.set64 CTL 136 (spTop m)) := MemFrame.setCtl _ _ _
  have hS₃ := hS₂.frame_stk hfb (by simp) (by simp)
  refine ⟨hok, ⟨M', hS₃, hK₂, ?_⟩, by rw [hres]; simp only [decH, hr], by unfold ResH; rw [← hr]; exact hw⟩
  have hc₂ : (136 : Word).toNat < (m₂.arr64 CTL).size := by simpa using hS₂.ctl136
  have hspn₃ : (m₂.set64 CTL 136 (spTop m)).arr64 SPN = m₂.arr64 SPN :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨?_, ?_, fun i hi => ?_, (BKept.of_frame hfm (by decide) (by decide)).trans
      (hSt₂.bstk.trans (BKept.of_frame hfb (by decide) (by decide))),
    (PoolGrew.of_frame hfm (by decide) (by decide)).trans
      (hSt₂.pool.trans (PoolGrew.of_frame hfb (by decide) (by decide)))⟩
  · simp only [spTop]; rw [rdW_set64]; simp only [hc₂, and_self, ↓reduceIte]
  · rw [hspn₃, hSt₂.size, hspn₁, hfc.2.2.1 SPN]
  · have hi' : i.toNat < (spTop m).toNat := UInt64.lt_iff_toNat_lt.mp hi
    simp only [spW]
    rw [hspn₃]
    have := hSt₂.below i (UInt64.lt_iff_toNat_lt.mpr (by rw [htop₁]; omega))
    simp only [spW] at this
    rw [this, hspn₁, hbc i hi']


/-! ## The program and the model -/

/-- `inst_lp_fast`'s call closure in the checker's program, with what the walk's program bundle
`ILWEntryProg` names (the spine reads, `keys_push`, the level-list substitutions; their closure). -/
def ilpfP : Prog :=
  [("inst_lp_fast", L.Arena.instLPFastL), ("get_app_fn", L.Arena.getAppFnL),
   ("get_app_args", L.Arena.getAppArgsL), ("get_app_spine", L.Arena.getAppSpineL),
   ("head_and_args", L.Arena.headAndArgsL), ("mk_app_n", L.Arena.mkAppNL),
   ("mk_app_n_from", L.Arena.mkAppNFromL), ("pi_result", L.Arena.piResultL),
   ("peel_pis", L.Arena.peelPisL), ("app_count", L.Arena.appCountL),
   ("app_fill", L.Arena.appFillL), ("app_fill_n", L.Arena.appFillNL),
   ("caps_never_zero", L.Arena.capsNeverZeroL), ("keys_push", L.Arena.keysPush),
   ("ek_copy", L.Arena.ekCopy), ("lp_substpw", L.Arena.lpSubstPW), ("lp_spw", L.Arena.lpSpw),
   ("lv_zero", L.Arena.lvZero), ("lh_push", L.Arena.lhPush), ("sle_go", L.Arena.sleGo),
   ("slp_go", L.Arena.slpGo), ("rec_fire_levels", L.Arena.recFireLevelsL),
   ("inst_lp", L.Arena.instLPL), ("keys_ok", L.Arena.keysOk), ("keys_push_iw", L.Arena.keysPushIW),
   ("inst_lp_core", L.Arena.instLPCore), ("mk_app", L.Arena.mkApp), ("ls_node", L.Arena.lsNode),
   ("lp_lookup", L.Arena.lpLookup), ("lv_node", L.Arena.lvNode), ("lv_sub_int", L.Arena.lvSubInt),
   ("lv_intern", L.Arena.lvIntern), ("intern_param", L.Arena.internParam),
   ("spn_ls", L.Arena.spnLs), ("ik_copy", L.Arena.ikCopy), ("der_b", L.Arena.derB),
   ("ilp_clear", L.Arena.memoClearG L.Arena.lpSch),
   ("ilpl_clear", L.Arena.memoClearG L.Arena.lplSch),
   ("ilpls_clear", L.Arena.memoClearG L.Arena.lplsSch), ("lp_go", L.Arena.lpGo),
   ("intern_app", L.Arena.internApp), ("lp_substl", L.Arena.lpSubstL),
   ("intern_zero", L.Arena.internZero), ("intern_succ", L.Arena.internSucc),
   ("intern_max", L.Arena.internMax), ("intern_imax", L.Arena.internImax),
   ("param_find", L.Arena.paramFind), ("param_push", L.Arena.paramPush),
   ("spn_pool", L.Arena.spnPool), ("intern_ls", L.Arena.internLs), ("sl_memo", L.Arena.slMemo),
   ("intern_sort", L.Arena.internSort), ("sls_memo", L.Arena.slsMemo),
   ("intern_const", L.Arena.internConst), ("lp_fvar", L.Arena.lpFVar), ("lp_app", L.Arena.lpApp),
   ("lp_lam", L.Arena.lpLam), ("lp_forall", L.Arena.lpForall), ("lp_let", L.Arena.lpLet),
   ("lp_proj", L.Arena.lpProj), ("app_find", L.Arena.appFind), ("app_push", L.Arena.appPush),
   ("lh_mk", L.Arena.lhMk), ("zero_find", L.Arena.zeroFind), ("zero_push", L.Arena.zeroPush),
   ("succ_find", L.Arena.succFind), ("succ_push", L.Arena.succPush), ("max_find", L.Arena.maxFind),
   ("max_push", L.Arena.maxPush), ("imax_find", L.Arena.imaxFind), ("imax_push", L.Arena.imaxPush),
   ("lit_hash", L.Arena.litHash), ("ls_find", L.Arena.lsFind), ("ls_push", L.Arena.lsPush),
   ("ilpl_find", L.Arena.memoFindG L.Arena.lplSch), ("ilpl_put", L.Arena.memoPutG L.Arena.lplSch),
   ("sort_find", L.Arena.sortFind), ("sort_push", L.Arena.sortPush),
   ("ilpls_find", L.Arena.memoFindG L.Arena.lplsSch), ("sls_go", L.Arena.slsGo),
   ("ilpls_put", L.Arena.memoPutG L.Arena.lplsSch), ("const_find", L.Arena.constFind),
   ("const_push", L.Arena.constPush), ("ilp_find", L.Arena.memoFindG L.Arena.lpSch),
   ("intern_fvar", L.Arena.internFVar), ("ilp_put", L.Arena.memoPutG L.Arena.lpSch),
   ("mk_lam", L.Arena.mkLam), ("mk_forall", L.Arena.mkForall), ("lp_let_tail", L.Arena.lpLetTail),
   ("mk_proj", L.Arena.mkProj), ("ls_match", L.Arena.lsMatch), ("fvar_find", L.Arena.fvarFind),
   ("fvar_push", L.Arena.fvarPush), ("intern_lam", L.Arena.internLamL),
   ("intern_forall", L.Arena.internForallL), ("lp_rb_let", L.Arena.lpRbLet),
   ("intern_proj", L.Arena.internProj), ("limbs_eq", L.Arena.limbsEq),
   ("lam_find", L.Arena.lamFind), ("lam_push", L.Arena.lamPush),
   ("forall_find", L.Arena.forallFind), ("forall_push", L.Arena.forallPush),
   ("mk_let", L.Arena.mkLet), ("proj_find", L.Arena.projFind), ("proj_push", L.Arena.projPush),
   ("intern_letE", L.Arena.internLet), ("letE_find", L.Arena.letFind),
   ("letE_push", L.Arena.letPush)]

def ilpfFns : List FnName := ilpfP.map (·.1)

/-- What it writes: the stack, the level heap, the expression, level, level-list and name-lookup
tables (both tiers), the pool scratch, the three `instLP` memos (52‥54). -/
def ilpfA : List ArrId :=
  [0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 25, 26, 27, 28, 29, 30, 31,
   32, 39, 40, 42, 43, 44, 45, 46, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 144, 192,
   256, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277,
   281, 282, 283, 284, 285, 286, 287, 288, 295, 296, 298, 299, 300, 301, 302, 311, 312, 313,
   314, 315, 316, 317]
/-- The `CTL` words it writes: the stack top (136), the heap top (192), the pool top (0), the
memos' stamps and counts (54‥59), the tables' counts. -/
def ilpfC : List Word :=
  [0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 26, 27, 28, 29, 30, 31, 32,
   33, 40, 41, 54, 55, 56, 57, 58, 59, 136, 192]

theorem ilpfP_closed : closedA ilpfP ilpfA ilpfC ilpfFns = true := by decide +kernel

theorem ilpfP_entry : ILWEntryProg ilpfP := by
  repeat' (first | rfl | constructor)

/-- The program bundle. -/
abbrev IlpfF (p : Prog) : Prop := ProgHas p ilpfP

/-- **The model of `inst_lp_fast`** (program- and fuel-free). -/
noncomputable def ilpfF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF ilpfP "inst_lp_fast" m args

theorem ilpfF_spec (p : Prog) (hp : IlpfF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_lp_fast" args
    ⦃fun r s' => LocEq s' s₀ ∧ ilpfF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec ilpfP_closed (hp.agree ilpfFns) (by decide) n s₀ args

/-- `inst_lp_fast` writes only `ilpfA`, `ilpfC`. -/
theorem ilpfF_frame {m m' : Mem} {args r : List Word} (h : ilpfF m args = some (r, m')) :
    MemFrame ilpfA ilpfC m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame ilpfP_closed (by decide) (run_of_callW hc)).1

/-! ## Under `StageT` -/

section stage
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`StageT` after a run framed away from the pools and the pins**, from `CoreS` after it
(`StageT.of_core` at a write set from the callee's own program text). -/
theorem StageT.of_coreFrame {A : List ArrId} {C : List Word} {m m' : Mem} {a a' : AState}
    {M : ModeMaps} (hfr : MemFrame A C m m') (hIW : IW ∉ A) (hE : EREC ∉ A) (hP : PINS ∉ A)
    (h129 : (129 : Word) ∉ C) (h200 : (200 : Word) ∉ C) (hS : StageT dn vis fe m a)
    (hC : CoreS dn m' a' vis fe M 0) : StageT dn vis fe m' a' ∧ IWGrow m m' := by
  have hI : m'.arr64 IW = m.arr64 IW := hfr.1 _ hIW (by decide)
  have hE' : m'.arr64 EREC = m.arr64 EREC := hfr.1 _ hE (by decide)
  have hP' : m'.arr64 PINS = m.arr64 PINS := hfr.1 _ hP (by decide)
  have h129' : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hfr.2.1 _ h129
  have h200' : rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 := hfr.2.1 _ h200
  obtain ⟨hCR, hT⟩ := hC.checkR
  refine ⟨⟨⟨hCR, IWOK.frame hfr hIW hE h129 h200 hS.stage.2⟩, hT, by simp only [pinW, hP']; exact hS.flag⟩, ?_⟩
  exact ⟨by simp [iwTop, h200'], by simp [erTop, h129'], fun i _ => by rw [hI], fun i _ => by rw [hE']⟩

/-- **`inst_lp_fast` refines `instLPFast` under `StageT`** (the contract
`IndStubs.instLPFast_spec` with `StageT` for `StageR`: `CoreS` needs the twin's invariants). -/
theorem ilpfF_okT (f o l us e : Word) (hu : H us) (he : H e) (ks : List NIdx) :
    RelW ilpfF [f, o, l, us, e]
      (fun m a => StageT dn vis fe m a ∧ decHL m o.toNat l.toNat = some ks)
      (instLPFast f.toNat ks (decI us) (decI e)) (KeepPostT dn vis fe decW0E) := by
  intro m m' a r h ⟨hT, hdec⟩
  obtain ⟨n, hc⟩ := callF_run h
  have hfr := ilpfF_frame h
  obtain ⟨M, hC⟩ := hT.core
  obtain ⟨hok, ⟨M', hC', -, -⟩, hres, hrh⟩ := CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
    (instLPFastI_refines ilpfP ilpfP_entry rfl rfl rfl n _ a dn vis fe M 0 f o l us e ks hC he hu hdec
      hT.stage.2.2.2.1) hc
  obtain ⟨hT', hg⟩ := StageT.of_coreFrame hfr (by decide) (by decide) (by decide) (by decide) (by decide)
    hT hC'
  exact ⟨_, _, AM.run_of_ok _ a hok, hT', hg, hrh, hres.symm⟩

/-- **The same, the walk memos `AbsOK` kept** (`I1Memo`, `CrMemo` framed; the rest from `TwinOK`
after the call). -/
theorem ilpfF_okTA (f o l us e : Word) (hu : H us) (he : H e) (ks : List NIdx) :
    RelW ilpfF [f, o, l, us, e]
      (fun m a => StageT dn vis fe m a ∧ AbsOK m ∧ decHL m o.toNat l.toNat = some ks)
      (instLPFast f.toNat ks (decI us) (decI e))
      (fun m m' a r x => KeepPostT dn vis fe decW0E m m' a r x ∧ AbsOK m') := by
  rintro m m' a r h ⟨hT, ⟨-, hI1, hCr, -, -⟩, hdec⟩
  have hfr := ilpfF_frame h
  obtain ⟨x, a', hrun, hK⟩ := ilpfF_okT f o l us e hu he ks m m' a r h ⟨hT, hdec⟩
  exact ⟨x, a', hrun, hK, hK.1.absOK (hI1.frame hfr (by decide) (by decide))
    (hCr.frame hfr (by decide) (by decide))⟩

end stage

end L.Ind
