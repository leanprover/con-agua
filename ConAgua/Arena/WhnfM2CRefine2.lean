module

public import ConAgua.Arena.WhnfM2CRefine
public import ConAgua.Arena.WhnfIotaRefine4
import ConRon.Bridge.Grind
public import ConAgua.Verdict.WhnfModels6E
public import ConAgua.Arena.DefEqStuck
import ConAgua.Arena.DerRel
import ConAgua.Arena.RefWalk
import ConAgua.Arena.StoreDenIntern
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.WhnfIotaRefine3

@[expose] public section

/-!
# `major_to_ctor`: refinements of `m2c_pre`, `m2c_check` and the K arm

One refinement per piece for both outcomes (`RefE`, `Arena/Verdict.lean`): each piece's unified
model (`Verdict/WhnfModels6E.lean`) is taken apart call by call, each callee's own spec or
refinement applied to its run, the relation threaded (`CorePost`, `GrowPost` once a slice is left
on the stack). An error claims the twin's failure under `M2CCtxE` (the knot's slots' claims,
`proof_irrel`'s); `m2c_pre`, a prefix of the arms, has its own shape (`PreRef`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Helpers

Copies of `WhnfDeltaRefine*.lean`'s (`LsStore.viewLen_eq_map`, `callW_internConst`, `callW_mkAppN`,
`CoreS.of_const`, …): that module cannot be imported next to `WhnfIotaRefine.lean` (both declare
`L.Arena.frW`), so they are restated here under primed names. -/

theorem LsStore.viewLen_eq_map' (st : LsStore) (i : LsIdx) :
    st.viewLen i = (st.view i).map List.length := by
  simp only [LsStore.viewLen, LsStore.view, LsStore.persGetLen, LsTables.getLen, LsTables.get]
  split
  · split <;> simp [Option.map_map, Function.comp_def]
  · split
    · split <;> simp [Option.map_map, Function.comp_def]
    · rfl

theorem viewLs_run' {a : AState} {h : LsIdx} {l : LsNodeView} (hv : a.store.lss.view h = some l) :
    (viewLs h).run a = .ok (l, a) := by
  simp [viewLs, StateT.run_bind, StateT.run_get, hv]; rfl

theorem viewLs_of_len {a : AState} {h : LsIdx} {k : Nat} (hv : a.store.lss.viewLen h = some k) :
    ∃ l, (viewLs h).run a = .ok (l, a) ∧ l.length = k := by
  rw [LsStore.viewLen_eq_map'] at hv
  cases e : a.store.lss.view h with
  | none => rw [e] at hv; cases hv
  | some l => rw [e] at hv; exact ⟨l, viewLs_run' e, Option.some.inj hv⟩

theorem rdW_off' {b : Array Word} {q c : Word} {i : Nat} {w : Word} (hb : b[i]? = some w)
    (hi : q.toNat + c.toNat = i) (hsz : b.size < 2 ^ 63) : rdW b (q + c) = w := by
  have hlt : i < b.size := (Array.getElem?_eq_some_iff.mp hb).1
  have : (q + c).toNat = i := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
  simp only [rdW, this, hb]; rfl

theorem keeps_cpl_internConst' (n : NIdx) (us : LsIdx) : Keeps cpl (internE (.const n us)) := by
  simp only [internE]; exact keeps_cpl_internNodeE _

theorem CoreS.of_const' {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    (hD : ArenaD m' a') (hcpl : cpl a' = cpl a) (hf : MemFrame [CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP] [18, 19] m m')
    {n : NIdx} {us : LsIdx} {r : EIdx} (hrun : (internE (.const n us)).run a = .ok (r, a'))
    (hus : ∃ ls, denoteLs a.store.lss us = some ls) :
    CoreS dn m' a' vis fe M eb :=
  hS.arena_frameD hD hcpl hf
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by decide)
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
    (hS.den.of_internConst hus hrun (hf.arr EREC (by simp [tier1, CREC, CSLOT, CLP, EREC]) (by decide)))
    (hmode := hS.mode.frame hf (by decide) (by decide))

theorem StackKept.of_constF {m m' : Mem} (hf : MemFrame [CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP] [18, 19] m m') :
    StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.arr SPN (by simp [tier1, CREC, CSLOT, CLP, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.ctl 136 (by simp)
  exact StackKept.of_frame hf

theorem ceinternW_hw' (m : Mem) (a : AState) (hR : ConstR m a) (f x : Word) (_hf : f.toNat < 2 ^ 32)
    (_hx : x.toNat < 2 ^ 32) (w : Word) (m' : Mem) (hI : ceinternW m f x = some (w, m')) :
    w.toNat < 2 ^ 32 := by
  exact consInternM_lt constCS_wf hR hI

section progs
variable (p : Prog)

/-- **`intern_const` as a run.** -/
theorem callW_internConst' (hpf : p.lookup "const_find" = some constFind)
    (hpp : p.lookup "const_push" = some constPush) (hp : p.lookup "intern_const" = some internConst)
    (n : Nat) (m : Mem) (a₀ : AState) (hD : ArenaD m a₀) (f x : Word) (hf : HW f) (hx : HW x)
    (r : List Word) (m' : Mem) (h : callW p n "intern_const" [f, x] m = some (r, m')) :
    AM.ok (internE (.const (decI f) (decI x))) a₀ ∧
    ArenaD m' (AM.st (internE (.const (decI f) (decI x))) a₀) ∧
    AM.res (internE (.const (decI f) (decI x))) a₀ = decI (r.headD 0) ∧
    MemFrame [CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP] [18, 19] m m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internConst_spec p hpf hpp hp n _ f x) h
  obtain ⟨-, hm⟩ := hm
  obtain ⟨h1, h2, h3⟩ := internConst_D m a₀ hD f x _ hf hx _ hm
  refine ⟨h1, h2, h3, ?_, ceinternW_hw' m a₀ ?_ f x hf hx _ _ hm⟩
  · exact ceinternW_frame (hI := hm)
  · exact hD.base.const

/-- **`mk_app_n` as a run**, with the result a handle word. -/
theorem callW_mkAppN' (hp : SpineProg p) (n : Nat) (m : Mem) (a₀ : AState) (hD : ArenaD m a₀)
    (f o k : Word) (xs : Array EIdx) (hf : HW f) (hx : SpineR m o k xs) (r : List Word)
    (m' : Mem) (h : callW p n "mk_app_n" [f, o, k] m = some (r, m')) :
    AM.ok (mkAppN (decE f) xs.toList) a₀ ∧ ArenaD m' (AM.st (mkAppN (decE f) xs.toList) a₀) ∧
    AM.res (mkAppN (decE f) xs.toList) a₀ = decE (r.headD 0) ∧
    MemFrame [AREC, ASLOT, ADER, tier1 AREC, tier1 ASLOT, tier1 ADER] [4, 5] m m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, -, hok, hD', hres, hfr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (Q := fun r s' =>
      LocEq s' ⟨m, Locals.init []⟩ ∧ AM.ok (mkAppN (decE f) xs.toList) a₀ ∧
        ArenaD s'.mem (AM.st (mkAppN (decE f) xs.toList) a₀) ∧
        AM.res (mkAppN (decE f) xs.toList) a₀ = decE (r.headD 0) ∧
        MemFrame [AREC, ASLOT, ADER, tier1 AREC, tier1 ASLOT, tier1 ADER] [4, 5] m s'.mem)
    (mkAppN_refines p hp n _ a₀ hD f o k xs hf hx) h
  obtain ⟨s'', hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (mkAppNL_spec p hp.derb hp.appf hp.appp hp.appi hp.mkapp hp.mkn n _ f o k) h
  exact ⟨hok, hD', hres, hfr, mkAppNFromW_hw k.toNat m a₀ f o k 0 (by simp) hD hf _ _ hm.2.2⟩

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`env_find` as a run** (`IotaProg'`'s lookups). -/
theorem callW_envFindI (hp : IotaProg' p) (n : Nat) (m : Mem) {dn : NIdx → Option ConLeche.Name}
    {fe : IFEnv} (vis w : Word) (hE : EnvR m vis fe) (hw : HW w) (r : List Word) (m' : Mem)
    (h : callW p n "env_find" [w, vis] m = some (r, m')) :
    m' = m ∧ fe.find? (decI w) = decFound dn m (r.headD 0) (r.tail.headD 0) ∧
    (r.headD 0 ≠ 0 → ∃ ci, decCI (erecP m) (r.tail.headD 0).toNat = some ci) := by
  obtain ⟨t₁, ht₁, hm₁, -, hfind⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_refines p hp.envix hp.envrow hp.envfind n _ vis w hE hw) h
  obtain ⟨t₁', ht₁', hm₁', -, hfound⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_found p hp.envix hp.envrow hp.envfind n _ vis w hw) h
  refine ⟨ht₁.symm.trans hm₁, hfind, fun h0 => ?_⟩
  obtain ⟨htag, hrow, hq⟩ := hfound h0
  obtain ⟨ci, hci⟩ := hE.found_some w hw htag hrow
  rw [← hq] at hci
  exact ⟨ci, hci⟩
-/

end progs

/-- **The program hypotheses of the `major_to_ctor` proofs**: part 4's, the pieces, the `const`
interning. -/
structure M2CProg' (p : Prog) : Prop extends IotaProg4 p, M2CProg p where
  constFind' : p.lookup "const_find" = some constFind
  constPush' : p.lookup "const_push" = some constPush
  internConst' : p.lookup "intern_const" = some internConst

/-! ## Results -/

theorem GrowRef.of_run {T : AM EIdx} {a a' : AState} {v : EIdx} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
    (hrun : T.run a = .ok (v, a')) (hA : CoreAfterG dn m m' a' vis fe M eb) (hv : v = decH r)
    (hr : ResH r) : GrowRef T a decH dn m vis fe M eb r m' := by
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hok, hst ▸ hA, hres.trans hv, hr⟩

/-! ## `m2c_pre` -/

/-- The twin's run of the common prefix (`m2cPreT`'s calls), as the L run `L` answers it. -/
def PreRun (R : CoreFnsA) (d : Nat) (major : EIdx) (a : AState) (L : List Word) (a' : AState) :
    Prop :=
  ∃ (ta tmaj hh : EIdx) (a₁ : AState),
    (R.inferIO d major).run a = .ok (ta, a₁) ∧ (R.whnf d ta).run a₁ = .ok (tmaj, a') ∧
    (getAppFn coreWalkFuel tmaj).run a' = .ok (hh, a') ∧
    (L.headD 0 = 0 → hh.tag ≠ ETag.const) ∧
    (L.headD 0 ≠ 0 → hh.tag = ETag.const ∧ tmaj = decE (L.tail.headD 0) ∧
      a'.store.view hh =
        some (.const (decI (L.tail.tail.headD 0)) (decI (L.tail.tail.tail.headD 0))) ∧
      a'.store.lss.viewLen (decI (L.tail.tail.tail.headD 0)) =
        some (L.tail.tail.tail.tail.headD 0).toNat)

theorem m2cPreT_none {R : CoreFnsA} {d : Nat} {major : EIdx} {a a' : AState} {L : List Word}
    (h : PreRun R d major a L a') (h0 : L.headD 0 = 0) (k : EIdx → NIdx → LsIdx → AM EIdx) :
    (m2cPreT R d major k).run a = .ok (major, a') := by
  obtain ⟨ta, tmaj, hh, a₁, h1, h2, h3, hn, -⟩ := h
  have ht : (hh.tag == ETag.const) = false := by simpa using hn h0
  simp only [m2cPreT, StateT.run_bind, h1, except_ok_bind, h2, h3, ht]; rfl

theorem m2cPreT_some {R : CoreFnsA} {d : Nat} {major : EIdx} {a a' : AState} {L : List Word}
    (h : PreRun R d major a L a') (h0 : L.headD 0 ≠ 0) (k : EIdx → NIdx → LsIdx → AM EIdx) :
    (m2cPreT R d major k).run a =
      (k (decE (L.tail.headD 0)) (decI (L.tail.tail.headD 0)) (decI (L.tail.tail.tail.headD 0))).run a' := by
  obtain ⟨ta, tmaj, hh, a₁, h1, h2, h3, -, hs⟩ := h
  obtain ⟨ht, rfl, hv, -⟩ := hs h0
  have ht' : (hh.tag == ETag.const) = true := by simpa using ht
  simp only [m2cPreT, StateT.run_bind, h1, except_ok_bind, h2, h3, ht', ↓reduceIte,
    view_run _ _ _ hv]

/-- What a successful `m2c_pre` gives from `m`: the twin's prefix (`PreRun`), the relation after
it, the record pool kept, the result words' range. -/
structure PreOk (R : CoreFnsA) (d : Nat) (major : EIdx) (a : AState)
    (dn : NIdx → Option ConLeche.Name) (m : Mem) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word)
    (L : List Word) (m' : Mem) (a' : AState) : Prop where
  run : PreRun R d major a L a'
  after : CoreAfter dn m m' a' vis fe M eb
  erec : m'.arr64 EREC = m.arr64 EREC
  hw : L.headD 0 ≠ 0 → HW (L.tail.headD 0) ∧ HW (L.tail.tail.headD 0) ∧
    HW (L.tail.tail.tail.headD 0)

/-- **`m2c_pre`'s refinement for both outcomes** (`RefC`, a prefix): an ok value is the twin's
prefix (`PreOk`); an error claims the failure of the twin's arm whatever its continuation. -/
def PreRef (G : Prop) (x : Except Err (List Word × Mem)) (R : CoreFnsA) (d : Nat) (major : EIdx)
    (a : AState) (dn : NIdx → Option ConLeche.Name) (m : Mem) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word) : Prop :=
  RefC G x (fun v => ∃ a', PreOk R d major a dn m vis fe M eb v.1 v.2 a')
    (fun e => ∀ k, ErrClaim (m2cPreT R d major k) a e)

theorem pre_err_io {R : CoreFnsA} {d : Nat} {major : EIdx} {a : AState} {ce : CheckError}
    (h : (R.inferIO d major).run a = .error ce) (k : EIdx → NIdx → LsIdx → AM EIdx) :
    (m2cPreT R d major k).run a = .error ce := by
  simp only [m2cPreT, StateT.run_bind, h]; rfl

theorem pre_err_whnf {R : CoreFnsA} {d : Nat} {major ta : EIdx} {a a₁ : AState} {ce : CheckError}
    (h1 : (R.inferIO d major).run a = .ok (ta, a₁)) (h : (R.whnf d ta).run a₁ = .error ce)
    (k : EIdx → NIdx → LsIdx → AM EIdx) :
    (m2cPreT R d major k).run a = .error ce := by
  simp only [m2cPreT, StateT.run_bind, h1, except_ok_bind, h]; rfl

section pre
variable (p : Prog) (hp : M2CProg' p) (hE : ErecKeptKnot p)
include hp hE

/-- **`m2c_pre` refines the twin's prefix, both outcomes** (`PreRef`): the errors are the
`infer_io` and `whnf` slots' (before any continuation). -/
theorem m2cPre_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode d major : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hmaj : HW major) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) :
    PreRef (M2CCtxE p N) (m2cPreE p (N + 1) m mode vis d major) (coreKnot (decMode mode) (decEager mode) fe id F)
      d.toNat (decE major) a dn m vis fe M eb := by
  rw [m2cPreE.arm1]
  rcases c1 : callE p N "infer_io" [mode, vis, d, major] m with e1 | ⟨r1, m1⟩
  · rw [m2cPreE.k_infer_io.none]
    exact fun hG k => ErrClaim.of_run_err (fun ce h' => pre_err_io h' k)
      (CoreSpecE.of_callE ((hG.knot N (Nat.le_refl _)).inferIO F ⟨m, Locals.init []⟩ a dn vis fe M eb
        mode d major hnF hn62 ⟨hS, hm4, hebm⟩ hmaj) c1)
  rw [m2cPreE.k_infer_io.arm1]
  obtain ⟨ok1, ⟨M1, hS1, hK1, hSt1⟩, res1, hr1⟩ := CoreSpec.of_callW
    ((hk N (Nat.le_refl _)).inferIO F ⟨m, Locals.init []⟩ a dn vis fe M eb mode d major hnF hn62
      ⟨hS, hm4, hebm⟩ hmaj) (callW_of_callE c1)
  have e1 : m1.arr64 EREC = m.arr64 EREC := hE _ _ _ _ _ _ (by simp) (callW_of_callE c1)
  have hrun1 := AM.run_of_ok _ _ ok1
  rw [res1] at hrun1
  rcases c2 : callE p N "whnf" [mode, vis, d, r1.headD 0] m1 with e2 | ⟨r2, m2⟩
  · rw [m2cPreE.k_whnf.none]
    exact fun hG k => ErrClaim.of_run_err (fun ce h' => pre_err_whnf hrun1 h' k)
      (CoreSpecE.of_callE ((hG.knot N (Nat.le_refl _)).whnf F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb
        mode d _ hnF hn62 ⟨hS1, hm4, hebm⟩ hr1) c2)
  rw [m2cPreE.k_whnf.arm1]
  obtain ⟨ok2, ⟨M2, hS2, hK2, hSt2⟩, res2, hr2⟩ := CoreSpec.of_callW
    ((hk N (Nat.le_refl _)).whnf F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d _ hnF hn62
      ⟨hS1, hm4, hebm⟩ hr1) (callW_of_callE c2)
  have e2 : m2.arr64 EREC = m1.arr64 EREC := hE _ _ _ _ _ _ (by simp) (callW_of_callE c2)
  have hrun2 := AM.run_of_ok _ _ ok2
  rw [res2] at hrun2
  rcases c3 : callW p N "get_app_fn" [r2.headD 0] m2 with _ | ⟨r3, m3⟩
  · rw [liftE_none, m2cPreE.k_get_app_fn.none]; exact fun _ _ => ErrClaim.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨t3, ht3, hm3, -, hh3, hga⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (getAppFn_refines' p hp.spine.fn N _ _ hS2.arena.base (r2.headD 0) hr2) c3
  have hm3' : m3 = m2 := ht3.symm.trans hm3
  subst hm3'
  have hKA : KeptAll M M2 eb := hK1.trans hK2
  have hStA : StackKept m m3 := hSt1.trans hSt2
  by_cases g3 : tagW (r3.headD 0) ≠ 3
  · rw [m2cPreE.k_get_app_fn.arm1 _ _ _ _ _ g3]
    refine ⟨_, ⟨⟨_, _, _, _, hrun1, hrun2, hga, fun _ => ?_, fun h => absurd rfl h⟩,
      ⟨M2, hS2, hKA, hStA⟩, e2.trans e1, fun h => absurd rfl h⟩⟩
    exact fun ht => g3 ((decE_tag_eq _ hh3 3 (by decide)).mp ht)
  have g3' : tagW (r3.headD 0) = 3 := by simpa using g3
  rw [m2cPreE.k_get_app_fn.arm2 _ _ _ _ _ g3']
  rcases c4 : callW p N "m2c_const_view" [r3.headD 0] m3 with _ | ⟨r4, m4⟩
  · rw [liftE_none, m2cPreE.k_m2c_const_view.none]; exact fun _ _ => ErrClaim.of_cls0 (by simp)
  rw [liftE_some, m2cPreE.k_m2c_const_view.arm1]
  obtain ⟨t4, ht4, -, hm4', hcv⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (m2cConstView_spec p hp.constView N _ (r3.headD 0)) c4
  have hm4e : m4 = m3 := ht4.symm.trans hm4'
  subst hm4e
  simp only [cvwW] at hcv
  obtain ⟨v1, hcv⟩ := of_ite_none hcv
  obtain ⟨v2, hcv⟩ := of_ite_none hcv
  have hr4 := (Option.some.inj hcv).symm
  obtain ⟨hvw, hn32, hu32⟩ := view_const_f m4 _ hS2.arena.base (r3.headD 0) hh3
    ⟨v1, UInt64.not_le.mp v2⟩ g3'
  rcases c5 : callW p N "ls_node" [r4.tail.headD 0] m4 with _ | ⟨r5, m5⟩
  · rw [liftE_none, m2cPreE.k_ls_node.none]; exact fun _ _ => ErrClaim.of_cls0 (by simp)
  rw [liftE_some, m2cPreE.k_ls_node.arm1]
  obtain ⟨t5, ht5, ht5s, hne5, hr5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
    (lsNode_spec p hp.lvl.lsnode N _ (r4.tail.headD 0)) c5
  have hm5 : m5 = m4 := by rw [← ht5, ht5s]
  subst hm5
  obtain ⟨o5, l5, hl5⟩ : ∃ o l, lsNodeW m5 (r4.tail.headD 0) = [o, l] := by
    rcases lsNodeW_cases m5 (r4.tail.headD 0) with h' | h'
    · rw [h'] at hr5; exact absurd hr5 hne5
    · exact h'
  have hus : HW (r4.tail.headD 0) := by rw [hr4]; exact hu32
  have hvl := lsNodeW_viewLen hS2.arena.base hus hl5
  have hr5' : r5.tail.headD 0 = l5 := by rw [hr5, hl5]; rfl
  refine ⟨_, ⟨⟨_, _, _, _, hrun1, hrun2, hga, fun h => absurd h (by simp),
    fun _ => ⟨?_, rfl, ?_, ?_⟩⟩, ⟨M2, hS2, hKA, hStA⟩, e2.trans e1, fun _ => ⟨hr2, ?_, hus⟩⟩⟩
  · exact (decE_tag_eq _ hh3 3 (by decide)).mpr g3'
  · simp only [List.tail_cons, List.headD_cons]
    rw [hr4]; exact hvw
  · simp only [List.tail_cons, List.headD_cons]
    rw [hvl, hr5']
  · simp only [List.tail_cons, List.headD_cons]
    rw [hr4]; exact hn32

end pre

theorem ret_eq {w : Word} {m₁ m' : Mem} {r : List Word}
    (h : some (w, m₁) = some (r.headD 0, m')) : w = r.headD 0 ∧ m₁ = m' := by
  simpa using h

/-! ## `m2c_check` -/

/-- `proof_irrel`'s refinement (`WhnfIotaRefine4.lean`'s `proofIrrel_refines`), a hypothesis here:
that proof rests on the `CoreS.lvl_den` stub, which the census-tagged statements supply. -/
def ProofIrrelOKM (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d a b : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 →
    eb = (mode >>> 1) &&& 1 → HW a → HW b →
    CoreSpec p (n + 1) "proof_irrel" [mode, vis, d, a, b]
      (proofIrrel (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) decBool s₀ a₀ dn
      vis fe MM eb

section check
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hpi : ProofIrrelOKM p)
include hp hc hpi

/-- **`m2c_check` refines `m2cCheckT`, both outcomes**: the errors are the slots' and
`proof_irrel`'s. -/
theorem m2cCheck_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode d tmaj fab major : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (htm : HW tmaj) (hfab : HW fab)
    (hmaj : HW major) (m : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) :
    RefE (M2CCtxE p N) (m2cCheckE p (N + 1) m mode vis d tmaj fab major)
      (m2cCheckT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE tmaj)
        (decE fab) (decE major)) a (CorePost decH dn m vis fe M eb ResH) := by
  rw [m2cCheckE.arm1]
  cases N with
  | zero => rw [callW_zero, liftE_none, m2cCheckE.k_fab_scope_ok.none]; exact RefE.of_cls0 (by simp)
  | succ N' =>
  unfold m2cCheckT
  refine RefE.bind_callW (s₀ := ⟨m, Locals.init []⟩) (fun _ => m2cCheckE.k_fab_scope_ok.none ..)
    (fabScopeOk_refines' p hp.toIotaProg' hc (N' + 1) _ a dn vis fe M eb d fab major hS hfab hmaj)
    fun r1 m1 _ h1 => RefE.after_core (w := id) h1 fun M1 hS1 _ => ?_
  by_cases g1 : r1.headD 0 = 0
  · rw [m2cCheckE.k_fab_scope_ok.arm1 _ _ _ _ _ _ _ _ _ _ g1, decBool_f_m2c g1]
    exact RefE.ret rfl (CorePost.ret hS1 rfl hmaj)
  rw [m2cCheckE.k_fab_scope_ok.arm2 _ _ _ _ _ _ _ _ _ _ g1, decBool_t_m2c g1]
  have hs1 : SlotPre ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode := ⟨hS1, hm4, hebm⟩
  refine RefE.bind_callE (s₀ := ⟨m1, Locals.init []⟩) (fun _ => m2cCheckE.k_infer_io.none ..)
    ((hk _ (Nat.le_refl _)).inferIO F _ _ dn vis fe M1 eb mode d fab hnF hn62 hs1 hfab)
    (fun (hG : M2CCtxE p (N' + 1)) => (hG.knot _ (Nat.le_refl _)).inferIO F _ _ dn vis fe M1 eb mode d
      fab hnF hn62 hs1 hfab) fun r2 m2 _ h2 => RefE.after_core (w := id) h2 fun M2 hS2 _ => ?_
  rw [m2cCheckE.k_infer_io.arm1]
  have hs2 : SlotPre ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode := ⟨hS2, hm4, hebm⟩
  refine RefE.bind_callE (s₀ := ⟨m2, Locals.init []⟩) (fun _ => m2cCheckE.k_defeq.none ..)
    ((hk _ (Nat.le_refl _)).defeq F _ _ dn vis fe M2 eb mode d tmaj _ hnF hn62 hs2 htm h2.resOk)
    (fun (hG : M2CCtxE p (N' + 1)) => (hG.knot _ (Nat.le_refl _)).defeq F _ _ dn vis fe M2 eb mode d
      tmaj _ hnF hn62 hs2 htm h2.resOk) fun r3 m3 _ h3 => RefE.after_core (w := id) h3 fun M3 hS3 _ => ?_
  by_cases g3 : r3.headD 0 = 0
  · rw [m2cCheckE.k_defeq.arm1 _ _ _ _ _ _ _ _ _ g3, decBool_f_m2c g3]
    exact RefE.ret rfl (CorePost.ret hS3 rfl hmaj)
  rw [decBool_t_m2c g3]
  have hv := decMode_verified mode hm4
  by_cases g4 : mode &&& 1 = 0
  · rw [m2cCheckE.k_defeq.arm2 _ _ _ _ _ _ _ _ _ g3 g4]
    have hv' : (decMode mode).verifiedChecks = true := by rw [hv]; simpa using g4
    simp only [hv', ↓reduceIte]
    refine RefE.bind_callE (s₀ := ⟨m3, Locals.init []⟩) (fun _ => m2cCheckE.k_proof_irrel.none ..)
      (hpi N' (hk.mono (Nat.le_succ _)) F (by omega) (by omega) _ _ dn vis fe M3 eb mode d fab major hS3
        hm4 hebm hfab hmaj)
      (fun (hG : M2CCtxE p (N' + 1)) => hG.pirr N' (hk.mono (Nat.le_succ _)) (hG.knot.mono (Nat.le_succ _))
        F (by omega) (by omega) _ _ dn vis fe M3 eb mode d fab major hS3 hm4 hebm hfab hmaj)
      fun r4 m4 _ h4 => RefE.after_core (w := id) h4 fun M4 hS4 _ => ?_
    rw [m2cCheckE.k_proof_irrel.arm1]
    by_cases g5 : r4.headD 0 = 0
    · rw [m2cCheckE.j1.arm2 _ _ _ _ _ g5, decBool_f_m2c g5]
      exact RefE.ret rfl (CorePost.ret hS4 rfl hmaj)
    · rw [m2cCheckE.j1.arm1 _ _ _ _ _ g5, decBool_t_m2c g5]
      exact RefE.ret rfl (CorePost.ret hS4 rfl hfab)
  · rw [m2cCheckE.k_defeq.arm3 _ _ _ _ _ _ _ _ _ g3 g4, m2cCheckE.j1.arm1 _ _ _ _ _ (by decide)]
    have hv' : (decMode mode).verifiedChecks = false := by rw [hv]; simpa using g4
    simp only [hv', Bool.false_eq_true, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS3 rfl hfab)

end check

/-! ## The K arm -/

theorem keeps_cpl_mkAppN' (f : EIdx) (xs : List EIdx) : Keeps cpl (mkAppN f xs) := by
  have := keeps_cpl_mkAppNFrom f xs.toArray 0
  rwa [mkAppNFrom_eq_mkAppN, List.toList_toArray] at this

theorem SpineR.take' {m : Mem} {o n k : Word} {xs : List EIdx} (h : SpineR m o n xs.toArray)
    (hk : k.toNat ≤ n.toNat) : SpineR m o k (xs.take k.toNat).toArray := by
  have hs : xs.length = n.toNat := by simpa using h.size
  refine ⟨by simp [hs, hk], by have := h.bound; omega, fun i hi => h.lt i (by omega), fun i hi => ?_⟩
  have hi' : i < xs.length := by simp at hi; omega
  have := h.get i (by simpa using hi')
  simpa using this

/-- The stack grew by a writer of the stack alone (`get_app_args`). -/
theorem CoreAfterG.of_stk {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    (hf : MemFrame [SPN] [136] m m') (hg : StackGrew m m') : CoreAfterG dn m m' a vis fe M eb :=
  ⟨M, hS.frame_stk hf (by simp) (by simp), KeptAll.refl _ _, hg⟩

/-- A successful prefix's universe arguments are a stored `const` node's list (the scrutinee's
type's head). -/
theorem PreRun.cview {R : CoreFnsA} {d : Nat} {major : EIdx} {a a' : AState} {L : List Word}
    (h : PreRun R d major a L a') (h0 : L.headD 0 ≠ 0) :
    ∃ (hh : EIdx) (c : NIdx), a'.store.view hh = some (.const c (decI (L.tail.tail.tail.headD 0))) := by
  obtain ⟨ta, tmaj, hh, a₁, -, -, -, -, hs⟩ := h
  obtain ⟨-, -, hv, -⟩ := hs h0
  exact ⟨hh, _, hv⟩

/-- The facts a successful prefix hands the arms. -/
theorem PreRun.view {R : CoreFnsA} {d : Nat} {major : EIdx} {a a' : AState} {L : List Word}
    (h : PreRun R d major a L a') (h0 : L.headD 0 ≠ 0) :
    ∃ l, (viewLs (decI (L.tail.tail.tail.headD 0))).run a' = .ok (l, a') ∧
      l.length = (L.tail.tail.tail.tail.headD 0).toNat ∧
      a'.store.lss.viewLen (decI (L.tail.tail.tail.headD 0)) =
        some (L.tail.tail.tail.tail.headD 0).toNat := by
  obtain ⟨ta, tmaj, hh, a₁, -, -, -, -, hs⟩ := h
  obtain ⟨-, -, -, hvl⟩ := hs h0
  obtain ⟨l, h1, h2⟩ := viewLs_of_len hvl
  exact ⟨l, h1, h2, hvl⟩

section karm
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hpi : ProofIrrelOKM p)
  (hE : ErecKeptKnot p)
include hp hc hpi

/-- **`m2c_k2` refines `m2cK2T`, both outcomes** (the arguments are left on the stack; the errors
are `m2c_check`'s). -/
theorem m2cK2_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ctor cnP tmaj ust major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hctor : HW ctor) (htm : HW tmaj) (hus : HW ust) (hmaj : HW major) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb)
    (hdus : ∃ ls, denoteLs a.store.lss (decI ust) = some ls) :
    RefE (M2CCtxE p N) (m2cK2E p (N + 1) m mode vis d ctor cnP tmaj ust major)
      (m2cK2T (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI ctor)
        cnP.toNat (decE tmaj) (decI ust) (decE major)) a (GrowPost decH dn m vis fe M eb ResH) := by
  rw [m2cK2E.arm1]
  cases N with
  | zero => rw [callW_zero, liftE_none, m2cK2E.k_get_app_args.none]; exact RefE.of_cls0 (by simp)
  | succ N' =>
  refine RefE.onlySim (fun _ => m2cK2E.k_get_app_args.none ..) (fun _ _ h => h) fun r1 m1 c1 => ?_
  obtain ⟨t1, ht1, -, hfr1, hg1, htop1, -, xs, hargs, hsp1⟩ := triple_of_callW
    (s₀ := ⟨m, Locals.init []⟩) (getAppArgs_refines p hp.spine (N' + 1) _ a hS.arena.base tmaj htm hS.spn) c1
  rw [ht1] at hfr1 hg1 hsp1
  have hA1 := CoreAfterG.of_stk hS hfr1 hg1
  have hS1 := hS.frame_stk hfr1 (by simp) (by simp)
  have hlen : xs.length = (r1.tail.headD 0).toNat := by simpa using hsp1.size
  unfold m2cK2T
  refine RefE.bind_right hargs ?_
  by_cases g1 : r1.tail.headD 0 < cnP
  · rw [m2cK2E.k_get_app_args.arm1 _ _ _ _ _ _ _ _ _ _ _ _ g1]
    have : ¬ cnP.toNat ≤ xs.length := by rw [hlen]; exact Nat.not_le.mpr g1
    exact RefE.ret (by rw [ite_eq_right this]; rfl) ⟨hA1, rfl, hmaj⟩
  rw [m2cK2E.k_get_app_args.arm2 _ _ _ _ _ _ _ _ _ _ _ _ g1]
  have hle : cnP.toNat ≤ xs.length := by rw [hlen]; exact UInt64.not_lt.mp g1
  rw [ite_eq_left hle]
  refine RefE.onlySim (fun _ => m2cK2E.k_intern_const.none ..) (fun _ _ h => h) fun r2 m2 c2 => ?_
  rw [m2cK2E.k_intern_const.arm1]
  obtain ⟨ok2, hD2, res2, hfr2, hh2⟩ := callW_internConst' p hp.constFind' hp.constPush'
    hp.internConst' (N' + 1) m1 a hS1.arena ctor ust hctor hus r2 m2 c2
  have hrun2 := AM.run_of_ok _ _ ok2
  rw [res2] at hrun2
  refine RefE.bind_right hrun2 ?_
  have hS2 := hS1.of_const' hD2 (Keeps.run (keeps_cpl_internConst' _ _) hrun2) hfr2 hrun2 hdus
  have hsp2 : SpineR m2 (r1.headD 0) cnP (xs.take cnP.toNat).toArray :=
    (hsp1.take' (by rw [← hlen]; exact hle)).of_spn_core
      (hfr2.1 SPN (by simp [tier1, CREC, CSLOT, CLP, SPN]) (by decide))
  refine RefE.onlySim (fun _ => m2cK2E.k_mk_app_n.none ..) (fun _ _ h => h) fun r3 m3 c3 => ?_
  rw [m2cK2E.k_mk_app_n.arm1]
  obtain ⟨ok3, hD3, res3, hfr3, hh3⟩ := callW_mkAppN' p hp.spine (N' + 1) m2 _ hS2.arena
    (r2.headD 0) (r1.headD 0) cnP _ hh2 hsp2 r3 m3 c3
  have hrun3 := AM.run_of_ok _ _ ok3
  rw [res3, show ((xs.take cnP.toNat).toArray).toList = xs.take cnP.toNat from rfl,
    show decE (r2.headD 0) = decI (r2.headD 0) from rfl] at hrun3
  refine RefE.bind_right hrun3 ?_
  have hS3 := hS2.of_app hD3 (Keeps.run (keeps_cpl_mkAppN' _ _) hrun3) hfr3
  have hSt : StackGrew m m3 :=
    hg1.trans ((StackKept.of_constF hfr2).trans (StackKept.of_app_frame hfr3)).toGrew
  exact RefE.lastE (m2cK2E.k_m2c_check.none p) (fun v => m2cK2E.k_m2c_check.arm1 p v.1 v.2)
    (fun h => h.mono (Nat.le_succ _))
    (m2cCheck_ref p hp hc hpi N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
      mode d tmaj (r3.headD 0) major hm4 hebm htm hh3 hmaj m3 _ M hS3)
    fun _ _ _ _ hv => ⟨CoreAfterG.compK (KeptAll.refl _ _) hSt hv.after.toG, hv.res, hv.valid⟩

include hE in
/-- **`m2c_k` refines `m2cKT`, both outcomes** (the errors are `m2c_pre`'s and `m2c_k2`'s). -/
theorem m2cK_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d T major ctor lpl cnP : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hT : HW T) (hmaj : HW major) (hctor : HW ctor) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) :
    RefE (M2CCtxE p N) (m2cKE p (N + 1) m mode vis d T major ctor lpl cnP)
      (m2cKT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI ctor)
        lpl.toNat cnP.toNat (decI T) (decE major)) a (GrowPost decH dn m vis fe M eb ResH) := by
  rw [m2cKE.arm1]
  cases N with
  | zero => rw [m2cPreE.eq_1, m2cKE.k_m2c_pre.none]; exact RefE.of_cls0 (by simp)
  | succ N' =>
  have hpre := m2cPre_ref p hp hE N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode
    d major hm4 hebm hmaj m a M hS
  rcases c1 : m2cPreE p (N' + 1) m mode vis d major with e1 | ⟨L, m1⟩
  · rw [m2cKE.k_m2c_pre.none]
    rw [c1] at hpre
    unfold m2cKT
    exact fun hG => hpre (hG.mono (Nat.le_succ _)) _
  rw [c1] at hpre
  obtain ⟨a1, hpre, ⟨M1, hS1, hK1, hSt1⟩, -, hhw⟩ := hpre
  have hA1 : GrowPost decH dn m vis fe M eb ResH ([major], m1) (decE major) a1 :=
    ⟨CoreAfter.toG ⟨M1, hS1, hK1, hSt1⟩, rfl, hmaj⟩
  by_cases g0 : L.headD 0 = 0
  · rw [m2cKE.k_m2c_pre.arm1 _ _ _ _ _ _ _ _ _ _ _ _ g0]
    exact RefE.ret (by unfold m2cKT; exact m2cPreT_none hpre g0 _) hA1
  obtain ⟨htm, hT2, hus⟩ := hhw g0
  obtain ⟨l, hvls, hll, -⟩ := hpre.view g0
  have hpre' := m2cPreT_some hpre g0
  by_cases g2 : L.tail.tail.headD 0 ≠ T
  · rw [m2cKE.k_m2c_pre.arm2 _ _ _ _ _ _ _ _ _ _ _ _ g0 g2]
    have hcd : ¬ ((decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ lpl.toNat = l.length) :=
      fun e => g2 ((decI_inj_iff hT2 hT).mp e.1)
    refine RefE.ret ?_ hA1
    unfold m2cKT; rw [hpre']
    simp only [StateT.run_bind, hvls, except_ok_bind]
    rw [ite_eq_right hcd]; rfl
  have g2' : L.tail.tail.headD 0 = T := by simpa using g2
  by_cases g3 : lpl ≠ L.tail.tail.tail.tail.headD 0
  · rw [m2cKE.k_m2c_pre.arm3 _ _ _ _ _ _ _ _ _ _ _ _ g0 g2' g3]
    have hcd : ¬ ((decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ lpl.toNat = l.length) :=
      fun e => g3 (UInt64.toNat_inj.mp (e.2.trans hll))
    refine RefE.ret ?_ hA1
    unfold m2cKT; rw [hpre']
    simp only [StateT.run_bind, hvls, except_ok_bind]
    rw [ite_eq_right hcd]; rfl
  have g3' : lpl = L.tail.tail.tail.tail.headD 0 := by simpa using g3
  rw [m2cKE.k_m2c_pre.arm4 _ _ _ _ _ _ _ _ _ _ _ _ g0 g2' g3']
  have hcd : ((decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ lpl.toNat = l.length) :=
    ⟨by rw [g2'], by rw [hll, g3']⟩
  have hrun : (m2cKT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI ctor)
      lpl.toNat cnP.toNat (decI T) (decE major)).run a =
      (m2cK2T (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI ctor) cnP.toNat
        (decE (L.tail.headD 0)) (decI (L.tail.tail.tail.headD 0)) (decE major)).run a1 := by
    unfold m2cKT; rw [hpre']
    simp only [StateT.run_bind, hvls, except_ok_bind]
    rw [ite_eq_left hcd]
  exact RefE.tail_eq (m2cKE.k_m2c_k2.none p) (fun v => m2cKE.k_m2c_k2.arm1 p v.1 v.2)
    (fun h => h.mono (Nat.le_succ _)) hrun (GrowPost.of_tail hK1 hSt1.toGrew)
    (m2cK2_ref p hp hc hpi N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode d ctor
      cnP _ _ major hm4 hebm hctor htm hus hmaj m1 a1 M1 hS1
      (by obtain ⟨_, _, _, _, _, _, _, _, hp5⟩ := hpre
          exact hS1.den.constLs _ _ _ (hp5 g0).2.2.1))

end karm

end L.Arena
