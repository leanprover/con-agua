import ConAgua.Arena.WhnfM2CRefine

/-!
# `major_to_ctor`: refinements of `m2c_pre`, `m2c_check` and the K arm

The callW pattern (`WhnfBase.lean`): each piece's model (`WhnfM2CRefine.lean`) is taken apart call
by call, each callee's own spec applied to its run, the relation threaded (`CoreAfter`,
`CoreAfterG` once a slice is left on the stack).
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
    (hD : ArenaD m' a') (hcpl : cpl a' = cpl a) (hf : MemFrame [CREC, CREC + 256, CSLOT, CSLOT + 256, CLP, CLP + 256] [18, 19] m m')
    {n : NIdx} {us : LsIdx} {r : EIdx} (hrun : (internE (.const n us)).run a = .ok (r, a'))
    (hus : ∃ ls, denoteLs a.store.lss us = some ls) :
    CoreS dn m' a' vis fe M eb :=
  hS.arena_frameD hD hcpl hf
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp [CREC, CSLOT, CLP])
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
    (hS.den.of_internConst hus hrun (hf.1 EREC (by simp [CREC, CSLOT, CLP, EREC]) (by decide)))
    (hmode := hS.mode.frame hf (by decide) (by decide))

theorem StackKept.of_constF {m m' : Mem} (hf : MemFrame [CREC, CREC + 256, CSLOT, CSLOT + 256, CLP, CLP + 256] [18, 19] m m') :
    StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (by simp [CREC, CSLOT, CLP, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
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
    MemFrame [CREC, CREC + 256, CSLOT, CSLOT + 256, CLP, CLP + 256] [18, 19] m m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internConst_spec p hpf hpp hp n _ f x) h
  obtain ⟨-, hm⟩ := hm
  obtain ⟨h1, h2, h3⟩ := internConst_D m a₀ hD f x _ hf hx _ hm
  refine ⟨h1, h2, h3, ?_, ceinternW_hw' m a₀ ?_ f x hf hx _ _ hm⟩
  · exact ceinternW_frame (hI := hm)
  · exact hD.1.const

/-- **`mk_app_n` as a run**, with the result a handle word. -/
theorem callW_mkAppN' (hp : SpineProg p) (n : Nat) (m : Mem) (a₀ : AState) (hD : ArenaD m a₀)
    (f o k : Word) (xs : Array EIdx) (hf : HW f) (hx : SpineR m o k xs) (r : List Word)
    (m' : Mem) (h : callW p n "mk_app_n" [f, o, k] m = some (r, m')) :
    AM.ok (mkAppN (decE f) xs.toList) a₀ ∧ ArenaD m' (AM.st (mkAppN (decE f) xs.toList) a₀) ∧
    AM.res (mkAppN (decE f) xs.toList) a₀ = decE (r.headD 0) ∧
    MemFrame [AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [4, 5] m m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, -, hok, hD', hres, hfr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (Q := fun r s' =>
      LocEq s' ⟨m, Locals.init []⟩ ∧ AM.ok (mkAppN (decE f) xs.toList) a₀ ∧
        ArenaD s'.mem (AM.st (mkAppN (decE f) xs.toList) a₀) ∧
        AM.res (mkAppN (decE f) xs.toList) a₀ = decE (r.headD 0) ∧
        MemFrame [AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [4, 5] m s'.mem)
    (mkAppN_refines p hp n _ a₀ hD f o k xs hf hx) h
  obtain ⟨s'', hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (mkAppNL_spec p hp.derb hp.appf hp.appp hp.appi hp.mkapp hp.mkn n _ f o k) h
  exact ⟨hok, hD', hres, hfr, mkAppNFromW_hw k.toNat m a₀ f o k 0 (by simp) hD hf _ _ hm.2.2⟩

/-- **`env_find` as a run** (`IotaProg'`'s lookups). -/
theorem callW_envFindI (hp : IotaProg' p) (n : Nat) (m : Mem) {dn : NIdx → Option ConLeche.Name}
    {fe : IFEnv} (vis w : Word) (hE : EnvR dn m vis fe) (hw : HW w) (r : List Word) (m' : Mem)
    (h : callW p n "env_find" [w, vis] m = some (r, m')) :
    m' = m ∧ fe.find? (decI w) = decFound dn m (r.headD 0) (r.tail.headD 0) ∧
    (r.headD 0 ≠ 0 → ∃ ci, decCI (erecP m) dn (r.tail.headD 0).toNat = some ci) := by
  obtain ⟨t₁, ht₁, hm₁, -, hfind⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_refines p hp.envix hp.envrow hp.envfind n _ vis w hE hw) h
  obtain ⟨t₁', ht₁', hm₁', -, hfound⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_found p hp.envix hp.envrow hp.envfind n _ vis w hw) h
  refine ⟨ht₁.symm.trans hm₁, hfind, fun h0 => ?_⟩
  obtain ⟨htag, hrow, hq⟩ := hfound h0
  obtain ⟨ci, hci⟩ := hE.found_some w hw htag hrow
  rw [← hq] at hci
  exact ⟨ci, hci⟩

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

/-- A run that ends with a pure answer `w`: its result list. -/
theorem CoreAfterG.compK {dn : NIdx → Option ConLeche.Name} {m₀ m₁ m₂ : Mem} {a₂ : AState}
    {vis : Word} {fe : IFEnv} {M M' : ModeMaps} {eb : Word}
    (hK : KeptAll M M' eb) (hSt : StackGrew m₀ m₁)
    (h₂ : CoreAfterG dn m₁ m₂ a₂ vis fe M' eb) : CoreAfterG dn m₀ m₂ a₂ vis fe M eb := by
  obtain ⟨M'', hS', hK', hSt'⟩ := h₂
  exact ⟨M'', hS', hK.trans hK', hSt.trans hSt'⟩

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

section pre
variable (p : Prog) (hp : M2CProg' p) (hE : ErecKeptKnot p)
include hp hE

/-- **`m2c_pre` refines the twin's prefix** (`PreRun`), keeping the record pool. -/
theorem m2cPre_ok (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode d major : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hmaj : HW major) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (L : List Word) (m' : Mem)
    (h : callW p (N + 1) "m2c_pre" [mode, vis, d, major] m = some (L, m')) :
    ∃ a', PreRun (coreKnot (decMode mode) fe id F) d.toNat (decE major) a L a' ∧
      CoreAfter dn m m' a' vis fe M eb ∧ m'.arr64 EREC = m.arr64 EREC ∧
      (L.headD 0 ≠ 0 → HW (L.tail.headD 0) ∧ HW (L.tail.tail.headD 0) ∧
        HW (L.tail.tail.tail.headD 0)) := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (m2cPre_spec p hp.pre N _ mode vis d major) h
  dsimp only at hW
  rw [hs'] at hW
  simp only [m2cPreW] at hW
  rcases c1 : callW p N "infer_io" [mode, vis, d, major] m with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨ok1, ⟨M1, hS1, hK1, hSt1⟩, res1, hr1⟩ := CoreSpec.of_callW
    ((hk N (Nat.le_refl _)).inferIO F ⟨m, Locals.init []⟩ a dn vis fe M eb mode d major hnF hn62
      ⟨hS, hm4, hebm⟩ hmaj) c1
  have e1 : m1.arr64 EREC = m.arr64 EREC := hE _ _ _ _ _ _ (by simp) c1
  rcases c2 : callW p N "whnf" [mode, vis, d, r1.headD 0] m1 with _ | ⟨r2, m2⟩ <;>
    simp only [c2, reduceCtorEq] at hW
  obtain ⟨ok2, ⟨M2, hS2, hK2, hSt2⟩, res2, hr2⟩ := CoreSpec.of_callW
    ((hk N (Nat.le_refl _)).whnf F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d _ hnF hn62
      ⟨hS1, hm4, hebm⟩ hr1) c2
  have e2 : m2.arr64 EREC = m1.arr64 EREC := hE _ _ _ _ _ _ (by simp) c2
  have hrun1 := AM.run_of_ok _ _ ok1
  have hrun2 := AM.run_of_ok _ _ ok2
  rw [res1] at hrun1
  rw [res2] at hrun2
  rcases c3 : callW p N "get_app_fn" [r2.headD 0] m2 with _ | ⟨r3, m3⟩ <;>
    simp only [c3, reduceCtorEq] at hW
  obtain ⟨t3, ht3, hm3, -, hh3, hga⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (getAppFn_refines' p hp.spine.fn N _ _ hS2.arena.1 (r2.headD 0) hr2) c3
  have hm3' : m3 = m2 := ht3.symm.trans hm3
  subst hm3'
  have hKA : KeptAll M M2 eb := hK1.trans hK2
  have hStA : StackKept m m3 := hSt1.trans hSt2
  by_cases g3 : r3.headD 0 >>> 28 ≠ 3
  · rw [ite_eq_left g3] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨_, ⟨_, _, _, _, hrun1, hrun2, hga, fun _ => ?_, fun h => absurd rfl h⟩,
      ⟨M2, hS2, hKA, hStA⟩, e2.trans e1, fun h => absurd rfl h⟩
    exact fun ht => g3 ((decE_tag_eq _ hh3 3 (by decide)).mp ht)
  rw [ite_eq_right g3] at hW
  have g3' : r3.headD 0 >>> 28 = 3 := by simpa using g3
  rcases c4 : callW p N "m2c_const_view" [r3.headD 0] m3 with _ | ⟨r4, m4⟩ <;>
    simp only [c4, reduceCtorEq] at hW
  obtain ⟨t4, ht4, -, hm4', hcv⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (m2cConstView_spec p hp.constView N _ (r3.headD 0)) c4
  have hm4e : m4 = m3 := ht4.symm.trans hm4'
  subst hm4e
  simp only [cvwW] at hcv
  obtain ⟨v1, hcv⟩ := of_ite_none hcv
  obtain ⟨v2, hcv⟩ := of_ite_none hcv
  have hr4 := (Option.some.inj hcv).symm
  obtain ⟨hvw, hn32, hu32⟩ := view_const_f m4 _ hS2.arena.1 (r3.headD 0) hh3
    ⟨v1, UInt64.not_le.mp v2⟩ g3'
  rcases c5 : callW p N "ls_node" [r4.tail.headD 0] m4 with _ | ⟨r5, m5⟩ <;>
    simp only [c5, reduceCtorEq] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨t5, ht5, ht5s, hne5, hr5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
    (lsNode_spec p hp.lvl.lsnode N _ (r4.tail.headD 0)) c5
  have hm5 : m5 = m4 := by rw [← ht5, ht5s]
  subst hm5
  obtain ⟨o5, l5, hl5⟩ : ∃ o l, lsNodeW m5 (r4.tail.headD 0) = [o, l] := by
    rcases lsNodeW_cases m5 (r4.tail.headD 0) with h' | h'
    · rw [h'] at hr5; exact absurd hr5 hne5
    · exact h'
  have hus : HW (r4.tail.headD 0) := by rw [hr4]; exact hu32
  have hvl := lsNodeW_viewLen hS2.arena.1 hus hl5
  have hr5' : r5.tail.headD 0 = l5 := by rw [hr5, hl5]; rfl
  refine ⟨_, ⟨_, _, _, _, hrun1, hrun2, hga, fun h => absurd h (by simp), fun _ => ⟨?_, rfl, ?_, ?_⟩⟩,
    ⟨M2, hS2, hKA, hStA⟩, e2.trans e1, fun _ => ⟨hr2, ?_, hus⟩⟩
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
      (proofIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool s₀ a₀ dn
      vis fe MM eb

section check
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hpi : ProofIrrelOKM p)
include hp hc hpi

/-- **`m2c_check` refines `m2cCheckT`.** -/
theorem m2cCheck_ok (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode d tmaj fab major : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (htm : HW tmaj) (hfab : HW fab)
    (hmaj : HW major) (m : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m a vis fe M eb)
    (r : List Word) (m' : Mem)
    (h : callW p (N + 1) "m2c_check" [mode, vis, d, tmaj, fab, major] m = some (r, m')) :
    CoreRef (m2cCheckT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE tmaj)
      (decE fab) (decE major)) a decH dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (m2cCheck_spec p hp.check N _ mode vis d tmaj fab major) h
  dsimp only at hW
  rw [hs'] at hW
  simp only [m2cCheckW] at hW
  cases N with
  | zero => simp [callW_zero] at hW
  | succ N' =>
  rcases c1 : callW p (N' + 1) "fab_scope_ok" [d, fab, major] m with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, -⟩ := CoreSpec.run
    (fabScopeOk_refines' p hp.toIotaProg' hc (N' + 1) ⟨m, Locals.init []⟩ a dn vis fe M eb d fab major
      hS hfab hmaj) c1
  by_cases g1 : r1.headD 0 = 0
  · rw [ite_eq_left g1] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    rw [decBool_f_m2c g1] at hrun1
    refine CoreRef.of_run ?_ ⟨M1, hS1, hK1, hSt1⟩ (decH_of _ _ hr) (resH_of_m2c _ _ hr hmaj)
    simp only [m2cCheckT, StateT.run_bind, hrun1, except_ok_bind, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [ite_eq_right g1] at hW
  rw [decBool_t_m2c g1] at hrun1
  rcases c2 : callW p (N' + 1) "infer_io" [mode, vis, d, fab] m1 with _ | ⟨r2, m2⟩ <;>
    simp only [c2, reduceCtorEq] at hW
  obtain ⟨hrun2, ⟨M2, hS2, hK2, hSt2⟩, hr2⟩ := CoreSpec.run
    ((hk _ (Nat.le_refl _)).inferIO F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d fab hnF hn62
      ⟨hS1, hm4, hebm⟩ hfab) c2
  rw [show decH r2 = decE (r2.headD 0) from rfl] at hrun2
  rcases c3 : callW p (N' + 1) "defeq" [mode, vis, d, tmaj, r2.headD 0] m2 with _ | ⟨r3, m3⟩ <;>
    simp only [c3, reduceCtorEq] at hW
  obtain ⟨hrun3, ⟨M3, hS3, hK3, hSt3⟩, -⟩ := CoreSpec.run
    ((hk _ (Nat.le_refl _)).defeq F ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d tmaj _ hnF hn62
      ⟨hS2, hm4, hebm⟩ htm hr2) c3
  have hKA : KeptAll M M3 eb := hK1.trans (hK2.trans hK3)
  have hStA : StackKept m m3 := hSt1.trans (hSt2.trans hSt3)
  by_cases g3 : r3.headD 0 = 0
  · rw [ite_eq_left g3] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    rw [decBool_f_m2c g3] at hrun3
    refine CoreRef.of_run ?_ ⟨M3, hS3, hKA, hStA⟩ (decH_of _ _ hr) (resH_of_m2c _ _ hr hmaj)
    simp only [m2cCheckT, StateT.run_bind, hrun1, except_ok_bind, ↓reduceIte, hrun2, hrun3,
      Bool.false_eq_true]
    rfl
  rw [ite_eq_right g3] at hW
  rw [decBool_t_m2c g3] at hrun3
  have hv := decMode_verified mode hm4
  by_cases g4 : mode &&& 1 = 0
  · rw [ite_eq_left g4] at hW
    have hv' : (decMode mode).verifiedChecks = true := by rw [hv]; simpa using g4
    rcases c4 : callW p (N' + 1) "proof_irrel" [mode, vis, d, fab, major] m3 with _ | ⟨r4, m4⟩ <;>
      simp only [c4, reduceCtorEq] at hW
    obtain ⟨hrun4, ⟨M4, hS4, hK4, hSt4⟩, -⟩ := CoreSpec.run
      (hpi N' (hk.mono (Nat.le_succ _)) F (by omega) (by omega)
        ⟨m3, Locals.init []⟩ _ dn vis fe M3 eb mode d fab major hS3 hm4 hebm hfab hmaj) c4
    by_cases g5 : r4.headD 0 = 0
    · rw [ite_eq_right (by simpa using g5)] at hW
      obtain ⟨hr, rfl⟩ := ret_eq hW
      rw [decBool_f_m2c g5] at hrun4
      refine CoreRef.of_run ?_ ⟨M4, hS4, hKA.trans hK4, hStA.trans hSt4⟩ (decH_of _ _ hr)
        (resH_of_m2c _ _ hr hmaj)
      simp only [m2cCheckT, StateT.run_bind, hrun1, except_ok_bind, ↓reduceIte, hrun2, hrun3, hv',
        hrun4, Bool.false_eq_true]
      rfl
    · rw [ite_eq_left (by simpa using g5)] at hW
      obtain ⟨hr, rfl⟩ := ret_eq hW
      rw [decBool_t_m2c g5] at hrun4
      refine CoreRef.of_run ?_ ⟨M4, hS4, hKA.trans hK4, hStA.trans hSt4⟩ (decH_of _ _ hr)
        (resH_of_m2c _ _ hr hfab)
      simp only [m2cCheckT, StateT.run_bind, hrun1, except_ok_bind, ↓reduceIte, hrun2, hrun3, hv',
        hrun4]
      rfl
  · rw [ite_eq_right g4] at hW
    have hv' : (decMode mode).verifiedChecks = false := by rw [hv]; simpa using g4
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine CoreRef.of_run ?_ ⟨M3, hS3, hKA, hStA⟩ (decH_of _ _ hr) (resH_of_m2c _ _ hr hfab)
    simp only [m2cCheckT, StateT.run_bind, hrun1, except_ok_bind, ↓reduceIte, hrun2, hrun3, hv',
      Bool.false_eq_true]
    rfl

end check

/-! ## The K arm -/

theorem keeps_cpl_mkAppN' (f : EIdx) (xs : List EIdx) : Keeps cpl (mkAppN f xs) := by
  have := keeps_cpl_mkAppNFrom f xs.toArray 0
  rwa [mkAppNFrom_eq_mkAppN, List.toList_toArray] at this

theorem decI_inj_m2c {k : IdxKind} {x y : Word} (hx : HW x) (hy : HW y) :
    (decI x : Idx k) = decI y ↔ x = y := by
  rw [decI_eq_iff x hx, decI_word_self y hy]

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

/-- **`m2c_k2` refines `m2cK2T`** (the arguments are left on the stack). -/
theorem m2cK2_ok (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ctor cnP tmaj ust major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hctor : HW ctor) (htm : HW tmaj) (hus : HW ust) (hmaj : HW major) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (r : List Word) (m' : Mem)
    (hdus : ∃ ls, denoteLs a.store.lss (decI ust) = some ls)
    (h : callW p (N + 1) "m2c_k2" [mode, vis, d, ctor, cnP, tmaj, ust, major] m = some (r, m')) :
    GrowRef (m2cK2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI ctor)
      cnP.toNat (decE tmaj) (decI ust) (decE major)) a decH dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (m2cK2_spec p hp.k2 N _ mode vis d ctor cnP tmaj ust major) h
  dsimp only at hW
  rw [hs'] at hW
  simp only [m2cK2W] at hW
  cases N with
  | zero => simp [callW_zero] at hW
  | succ N' =>
  rcases c1 : callW p (N' + 1) "get_app_args" [tmaj] m with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨t1, ht1, -, hfr1, hg1, htop1, -, xs, hargs, hsp1⟩ := triple_of_callW
    (s₀ := ⟨m, Locals.init []⟩) (getAppArgs_refines p hp.spine (N' + 1) _ a hS.arena.1 tmaj htm hS.spn) c1
  rw [ht1] at hfr1 hg1 hsp1
  have hA1 := CoreAfterG.of_stk hS hfr1 hg1
  have hS1 := hS.frame_stk hfr1 (by simp) (by simp)
  have hlen : xs.length = (r1.tail.headD 0).toNat := by simpa using hsp1.size
  by_cases g1 : r1.tail.headD 0 < cnP
  · rw [ite_eq_left g1] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA1 (decH_of _ _ hr) (resH_of_m2c _ _ hr hmaj)
    have : ¬ cnP.toNat ≤ xs.length := by rw [hlen]; exact Nat.not_le.mpr g1
    simp only [m2cK2T, StateT.run_bind, hargs, except_ok_bind, this, ↓reduceIte]
    rfl
  rw [ite_eq_right g1] at hW
  have hle : cnP.toNat ≤ xs.length := by rw [hlen]; exact UInt64.not_lt.mp g1
  rcases c2 : callW p (N' + 1) "intern_const" [ctor, ust] m1 with _ | ⟨r2, m2⟩ <;>
    simp only [c2, reduceCtorEq] at hW
  obtain ⟨ok2, hD2, res2, hfr2, hh2⟩ := callW_internConst' p hp.constFind' hp.constPush'
    hp.internConst' (N' + 1) m1 a hS1.arena ctor ust hctor hus r2 m2 c2
  have hrun2 := AM.run_of_ok _ _ ok2
  rw [res2] at hrun2
  have hS2 := hS1.of_const' hD2 (Keeps.run (keeps_cpl_internConst' _ _) hrun2) hfr2 hrun2 hdus
  have hsp2 : SpineR m2 (r1.headD 0) cnP (xs.take cnP.toNat).toArray :=
    (hsp1.take' (by rw [← hlen]; exact hle)).of_spn_core
      (hfr2.1 SPN (by simp [CREC, CSLOT, CLP, SPN]) (by decide))
  rcases c3 : callW p (N' + 1) "mk_app_n" [r2.headD 0, r1.headD 0, cnP] m2 with _ | ⟨r3, m3⟩ <;>
    simp only [c3, reduceCtorEq] at hW
  obtain ⟨ok3, hD3, res3, hfr3, hh3⟩ := callW_mkAppN' p hp.spine (N' + 1) m2 _ hS2.arena
    (r2.headD 0) (r1.headD 0) cnP _ hh2 hsp2 r3 m3 c3
  have hrun3 := AM.run_of_ok _ _ ok3
  rw [res3, show ((xs.take cnP.toNat).toArray).toList = xs.take cnP.toNat from rfl,
    show decE (r2.headD 0) = decI (r2.headD 0) from rfl] at hrun3
  have hS3 := hS2.of_app hD3 (Keeps.run (keeps_cpl_mkAppN' _ _) hrun3) hfr3
  rcases c4 : callW p (N' + 1) "m2c_check" [mode, vis, d, tmaj, r3.headD 0, major] m3 with _ | ⟨r4, m4⟩ <;>
    simp only [c4, reduceCtorEq] at hW
  obtain ⟨hr, rfl⟩ := ret_eq hW
  have hck := m2cCheck_ok p hp hc hpi N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
    mode d tmaj (r3.headD 0) major hm4 hebm htm hh3 hmaj m3 _ M hS3 r4 m4 c4
  obtain ⟨ok4, ⟨M4, hS4, hK4, hSt4⟩, res4, hr4⟩ := hck
  have hrun4 := AM.run_of_ok _ _ ok4
  rw [res4] at hrun4
  refine GrowRef.of_run (v := decH r4) ?_ ⟨M4, hS4, hK4, hg1.trans ((StackKept.of_constF hfr2).trans
    ((StackKept.of_app_frame hfr3).trans hSt4)).toGrew⟩ (by unfold decH; rw [hr])
    (by unfold ResH at hr4 ⊢; rw [← hr]; exact hr4)
  simp only [m2cK2T, StateT.run_bind, hargs, except_ok_bind, hle, ↓reduceIte, hrun2, hrun3]
  exact hrun4

include hE in
/-- **`m2c_k` refines `m2cKT`.** -/
theorem m2cK_ok (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d T major ctor lpl cnP : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hT : HW T) (hmaj : HW major) (hctor : HW ctor) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (r : List Word) (m' : Mem)
    (h : callW p (N + 1) "m2c_k" [mode, vis, d, T, major, ctor, lpl, cnP] m = some (r, m')) :
    GrowRef (m2cKT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI ctor)
      lpl.toNat cnP.toNat (decI T) (decE major)) a decH dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (m2cK_spec p hp.k N _ mode vis d T major ctor lpl cnP) h
  dsimp only at hW
  rw [hs'] at hW
  simp only [m2cKW] at hW
  cases N with
  | zero => simp [callW_zero] at hW
  | succ N' =>
  rcases c1 : callW p (N' + 1) "m2c_pre" [mode, vis, d, major] m with _ | ⟨L, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨a1, hpre, ⟨M1, hS1, hK1, hSt1⟩, -, hhw⟩ := m2cPre_ok p hp hE N' F
    (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode d major hm4 hebm hmaj m a M hS
    L m1 c1
  by_cases g0 : L.headD 0 = 0
  · rw [ite_eq_left g0] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ (CoreAfter.toG ⟨M1, hS1, hK1, hSt1⟩) (decH_of _ _ hr)
      (resH_of_m2c _ _ hr hmaj)
    unfold m2cKT; exact m2cPreT_none hpre g0 _
  rw [ite_eq_right g0] at hW
  obtain ⟨htm, hT2, hus⟩ := hhw g0
  obtain ⟨l, hvls, hll, -⟩ := hpre.view g0
  have hpre' := m2cPreT_some hpre g0
  by_cases g2 : L.tail.tail.headD 0 ≠ T
  · rw [ite_eq_left g2] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ (CoreAfter.toG ⟨M1, hS1, hK1, hSt1⟩) (decH_of _ _ hr)
      (resH_of_m2c _ _ hr hmaj)
    have hc : ¬ ((decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ lpl.toNat = l.length) :=
      fun e => g2 ((decI_inj_m2c hT2 hT).mp e.1)
    unfold m2cKT; rw [hpre']
    simp only [StateT.run_bind, hvls, except_ok_bind]
    rw [ite_eq_right hc]; rfl
  rw [ite_eq_right g2] at hW
  have g2' : L.tail.tail.headD 0 = T := by simpa using g2
  by_cases g3 : lpl ≠ L.tail.tail.tail.tail.headD 0
  · rw [ite_eq_left g3] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ (CoreAfter.toG ⟨M1, hS1, hK1, hSt1⟩) (decH_of _ _ hr)
      (resH_of_m2c _ _ hr hmaj)
    have hc : ¬ ((decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ lpl.toNat = l.length) :=
      fun e => g3 (UInt64.toNat_inj.mp (e.2.trans hll))
    unfold m2cKT; rw [hpre']
    simp only [StateT.run_bind, hvls, except_ok_bind]
    rw [ite_eq_right hc]; rfl
  rw [ite_eq_right g3] at hW
  have g3' : lpl = L.tail.tail.tail.tail.headD 0 := by simpa using g3
  rcases c2 : callW p (N' + 1) "m2c_k2" [mode, vis, d, ctor, cnP, L.tail.headD 0,
      L.tail.tail.tail.headD 0, major] m1 with _ | ⟨r2, m2⟩ <;> simp only [c2, reduceCtorEq] at hW
  obtain ⟨hr, rfl⟩ := ret_eq hW
  obtain ⟨ok2, hA2, res2, hr2⟩ := m2cK2_ok p hp hc hpi N' F (hk.mono (Nat.le_succ _)) (by omega)
    (by omega) dn vis fe eb mode d ctor cnP _ _ major hm4 hebm hctor htm hus hmaj m1 a1 M1 hS1 r2 m2
    (by obtain ⟨_, _, _, _, _, _, _, _, hp5⟩ := hpre
        exact hS1.den.constLs _ _ _ (hp5 g0).2.2.1) c2
  have hrun2 := AM.run_of_ok _ _ ok2
  rw [res2] at hrun2
  have hc : ((decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ lpl.toNat = l.length) :=
    ⟨by rw [g2'], by rw [hll, g3']⟩
  refine GrowRef.of_run (v := decH r2) ?_ (CoreAfterG.compK hK1 hSt1.toGrew hA2)
    (by unfold decH; rw [hr]) (by unfold ResH at hr2 ⊢; rw [← hr]; exact hr2)
  unfold m2cKT; rw [hpre']
  simp only [StateT.run_bind, hvls, except_ok_bind]
  rw [ite_eq_left hc]; exact hrun2

end karm

end L.Arena
