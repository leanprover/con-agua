module

public import ConAgua.Arena.WhnfDeltaRefine
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.StoreDenIntern
import all ConAgua.Arena.WhnfDelta
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.NatAdd
import all ConAgua.Arena.Refine
import all ConAgua.Arena.Store

@[expose] public section

/-!
# δ and `Nat` literals: proofs of `WhnfDelta.lean`'s specs, part 2 (`raw_nat_lit` … `unfold_definition`)

Split from `WhnfDeltaRefine.lean`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `raw_nat_lit` -/

/-- The model of `raw_nat_lit`: `(flag, off, cnt, memory)`. -/
l_model rawNatLit_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.rawNatLit ↦ rawNatLitW tuple]
  specs [callW_spec p n "pin_at", callW_spec p n "pin_word"]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] gen 30


theorem rdW_ctl_top' (m : Mem) : rdW (m.arr64 CTL) 0 = m.top := by
  simp [rdW, Mem.top]

/-- **A `lit` node past the view checks**: the kind word `0` says `natVal`, with the record's
slice; any other kind says `strVal`. -/
theorem view_lit_nat (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h LIT) (hg : tagW h = 8) :
    (tfld m LIT (tierW h) (idxW h) 0 = 0 →
      ∃ N, a.store.view (decE h) = some (.lit (.natVal N)) ∧ NatRec m (tierW h) (idxW h) N) ∧
    (tfld m LIT (tierW h) (idxW h) 0 ≠ 0 →
      ∃ s, a.store.view (decE h) = some (.lit (.strVal s))) := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h litCS RecRel (·.lits) _ hR.lit.2 hv.2
  have hview : ∀ l, k = ⟨l⟩ → a.store.view (decE h) = some (.lit l) := by
    intro l hl
    rw [view_tier m a hR h hh hv.1, get_lit _ h hh hg, Tbl.node?, hk, hl]
    rfl
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k
  · simp only [RecRel_natVal] at hkr
    exact ⟨fun _ => ⟨N, hview _ rfl, hkr⟩, fun hne => absurd hkr.1 hne⟩
  · simp only [RecRel_strVal, StrRec] at hkr
    exact ⟨fun h0 => absurd (hkr.1.symm.trans h0) (by decide), fun _ => ⟨s, hview _ rfl⟩⟩

/-- The result of a `raw_nat_lit` word triple, as the twin's option. -/
def rawDec (m : Mem) (r : List Word) : Option Nat :=
  if r.headD 0 = 0 then none
  else some (pv (vpool m) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat)

/-- The postcondition of a `raw_nat_lit` run. -/
def RawOut (m : Mem) (a₀ : AState) (h : Word) (r : List Word) : Prop :=
  (rawNatLit? (decE h)).run a₀ = .ok (rawDec m r, a₀) ∧ ResH r ∧
  (r.headD 0 ≠ 0 → SliceOK m (r.tail.headD 0) (r.tail.tail.headD 0) ∧
    Norm (vpool m) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat)

theorem RawOut.none {m : Mem} {a₀ : AState} {h : Word} {r : List Word}
    (hrun : (rawNatLit? (decE h)).run a₀ = .ok (none, a₀)) (hr0 : r.headD 0 = 0) :
    RawOut m a₀ h r :=
  ⟨by unfold rawDec; rw [ite_eq_left hr0]; exact hrun, by unfold ResH HW; rw [hr0]; decide,
         fun hne => absurd hr0 hne⟩

theorem rawNatLit_run_other {a : AState} {h : EIdx} {v : ENodeView} (hv : a.store.view h = some v)
    (hl : ∀ N, v ≠ .lit (.natVal N)) (hc : ∀ c us, v ≠ .const c us) :
    (rawNatLit? h).run a = .ok (none, a) := by
  simp only [rawNatLit?, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  cases v with
  | lit l =>
    cases l with
    | natVal N => exact absurd rfl (hl N)
    | strVal s => rfl
  | const c us => exact absurd rfl (hc c us)
  | _ => rfl

theorem rawNatLit_run_lit {a : AState} {h : EIdx} {N : Nat}
    (hv : a.store.view h = some (.lit (.natVal N))) :
    (rawNatLit? h).run a = .ok (some N, a) := by
  simp only [rawNatLit?, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; rfl

theorem rawNatLit_run_const {m : Mem} {a : AState} {h : EIdx} {c : NIdx} {us : LsIdx}
    (hP : PinsFull m a.pins) (hv : a.store.view h = some (.const c us)) :
    (rawNatLit? h).run a = .ok (if c == decI (pinW m 3) && us == decI (pinW m 52) then some 0
      else none, a) := by
  simp only [rawNatLit?, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, emptyLevels,
    pinEmptyLevels_run hP, pinNatZero_run hP]; rfl


theorem view_other (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (c : TRec) (hv : viewOK m h c)
    (hcg : (tagW h = 0 ∧ c = BVAR) ∨ (tagW h = 1 ∧ c = FVAR) ∨ (tagW h = 2 ∧ c = SORT) ∨
      (tagW h = 5 ∧ c = LAM) ∨ (tagW h = 6 ∧ c = FORALL) ∨
      (tagW h = 7 ∧ c = LET) ∨ (tagW h = 9 ∧ c = PROJ)) :
    ∃ v, a.store.view (decE h) = some v ∧ (∀ N, v ≠ .lit (.natVal N)) ∧
      (∀ c us, v ≠ .const c us) := by
  rcases hcg with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact ⟨_, view_bvar m a hR h hh hv g, fun N => nofun, fun c us => nofun⟩
  · obtain ⟨i, ty, hw⟩ := view_fvar m a hR h hh hv g
    exact ⟨_, hw, fun N => nofun, fun c us => nofun⟩
  · obtain ⟨u, hw⟩ := view_sort m a hR h hh hv g
    exact ⟨_, hw, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_lam m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_forall m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_let m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_proj m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩

theorem rawSimple {dn : NIdx → Option ConLeche.Name} {m : Mem} {a₀ : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a₀ vis fe M eb) {h : Word} (hh : HW h)
    (c : TRec) (hsc : ¬(tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hb : ¬ tcnt m c (tierW h) ≤ idxW h)
    (hcg : (tagW h = 0 ∧ c = BVAR) ∨ (tagW h = 1 ∧ c = FVAR) ∨ (tagW h = 2 ∧ c = SORT) ∨
      (tagW h = 5 ∧ c = LAM) ∨ (tagW h = 6 ∧ c = FORALL) ∨
      (tagW h = 7 ∧ c = LET) ∨ (tagW h = 9 ∧ c = PROJ))
    (r : List Word) (hr : r.headD 0 = 0) : RawOut m a₀ h r := by
  obtain ⟨v, hv, hl, hc⟩ := view_other m a₀ hS.arena.base h hh c ⟨hsc, by simpa using hb⟩ hcg
  exact RawOut.none (rawNatLit_run_other hv hl hc) hr

/-- `rawSimple` at an `app` handle (its index is the wide one). -/
theorem rawSimpleA {dn : NIdx → Option ConLeche.Name} {m : Mem} {a₀ : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a₀ vis fe M eb) {h : Word} (hh : HW h)
    (hsc : ¬(tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hb : ¬ tcnt m APP (tierW h) ≤ idxA h) (g : tagW h = 4)
    (r : List Word) (hr : r.headD 0 = 0) : RawOut m a₀ h r :=
  RawOut.none (rawNatLit_run_other
    (view_app m a₀ hS.arena.base h hh ⟨hsc, by simpa using hb⟩ g).1 (fun N => nofun)
    (fun c us => nofun)) hr

section refs9
variable (p : Prog)

theorem callW_rawNatLit (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb h : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hh : HW h) (r : List Word) (m' : Mem)
    (hcall : callW p n "raw_nat_lit" [h] s₀.mem = some (r, m')) :
    m' = s₀.mem ∧ RawOut s₀.mem a₀ h r := by
  sorry

/-- **`raw_nat_lit` refines `rawNatLit?`**: the result is a flag and the literal's POOL slice
(`pv`), read-only. -/
@[refines ConRon.Arena.rawNatLit?]
theorem rawNatLit_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb h : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hh : HW h) :
    CoreSpec p n "raw_nat_lit" [h] (rawNatLit? (decE h))
      (fun r => if r.headD 0 = 0 then none
        else some (pv (vpool s₀.mem) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat))
      s₀ a₀ dn vis fe MM eb := by
  apply CoreSpec.of_call
  intro r m' hcall
  obtain ⟨rfl, hrun, hres, -⟩ := callW_rawNatLit p hp n s₀ a₀ dn vis fe MM eb h hC hh r m' hcall
  exact CRef.core (m' := s₀.mem) (CRef.pure hC _ hrun rfl hres)

end refs9


/-! ## `nat_lit_to_ctor` -/


/-- The model of `nat_lit_to_ctor`. -/
l_model natLitToCtor_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.natLitToCtor ↦ natLitToCtorW ]
  specs [callW_spec p n "pin_at", callW_spec p n "const_e", callW_spec p n "nat_pred_lit", callW_spec p n "mk_app"]
  grind [arena_grind] fold [tierW, idxW]
  finish [tierW, idxW] gen 30


/-! ## Frames of the `Nat` functions -/

theorem CoreS.of_nat {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    (hD : ArenaD m' a') (hcpl : cpl a' = cpl a) (hf : MemFrame natA natC m m')
    (hv : ∀ x w, IsSC w → a'.store.view x = some w → a.store.view x = some w) (hP : PoolGrew m m') :
    CoreS dn m' a' vis fe M eb :=
  have hk : a'.caches = a.caches ∧ a'.pins = a.pins ∧ a'.store.lss = a.store.lss := by
    simpa only [cpl, Prod.mk.injEq] using hcpl
  hS.arena_frameD hD hcpl hf
    (fun b hb => by
      simp only [natA, List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by decide)
    (fun b hb => by
      simp only [natA, List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [natC, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [natC, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
    (hS.den.of_views hk.1 hk.2.1 hk.2.2 (hf.arr EREC (by simp [tier1, natA, POOL, POOL1, REC, SLOT, CREC, CSLOT, CLP, EREC]) (by decide))
      hv) (hmode := hS.mode.poolGrew hP)

theorem StackKept.of_nat_frame {m m' : Mem} (hf : MemFrame natA natC m m') (hP : PoolGrew m m') :
    StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.arr SPN (by simp [tier1, natA, POOL, POOL1, REC, SLOT, CREC, CSLOT, CLP, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.ctl 136 (by simp [natC])
  exact ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn],
    BKept.of_frame hf (by decide) (by decide), hP⟩

theorem keeps_cpl_natPredArm (a : Nat) : Keeps cpl (natPredArm a) := by
  unfold natPredArm
  exact Keeps.bind (keeps_cpl_internLit _) (fun _ => Keeps.pure _)

section refs10
variable (p : Prog)

theorem callW_natFrame (hc : closedA p natA natC natFns = true) (f : FnName) (hf : f ∈ natFns)
    (n : Nat) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem)
    (h : callW p n f vs m = some (r, m')) : MemFrame natA natC m m' := by
  obtain ⟨s', rfl, hfr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (invoke_memFrame hc n hf vs ⟨m, Locals.init []⟩) h
  exact hfr.1

theorem natPredLit_inst (hp : WhnfDeltaProg' p) : InternSpec p ArenaD := by
  sorry

/-- The functions of `intern_lit`: they write the `lit` table only, never the pool. -/
def litFns : List FnName := ["intern_lit", "lit_hash", "limbs_eq", "lit_match", "lit_find", "lit_push"]

theorem litFns_closed : closedA storeProg [REC, tier1 REC, SLOT, tier1 SLOT] [2, 3] litFns = true := by decide +kernel

theorem WhnfDeltaProg'.litClosed (hp : WhnfDeltaProg' p) : closedA p [REC, tier1 REC, SLOT, tier1 SLOT] [2, 3] litFns = true :=
  closedW_of_agree litFns_closed (by
    intro f hf
    simp only [litFns, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp.internLit]; rfl
    · rw [hp.litHash']; rfl
    · rw [hp.limbsEq']; rfl
    · rw [hp.litMatch']; rfl
    · rw [hp.litFind']; rfl
    · rw [hp.litPush']; rfl)

/-- `intern_lit` under `ArenaD` and "the pool only grew since `m₀`". -/
theorem natPredLit_instP (hp : WhnfDeltaProg' p) (m₀ : Mem) :
    InternSpec p (fun m a => ArenaD m a ∧ PoolGrew m₀ m) := by
  intro a₀ n s₀ o l ⟨hA, hP⟩ hq hn hq0
  apply L.M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hD, hres⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun (natPredLit_inst p hp a₀ n s₀ o l hA hq hn hq0)
  obtain ⟨hfr, -⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun
    (invoke_memFrame hp.litClosed n (f := "intern_lit") (by decide) [o, l] s₀)
  subst hs
  exact ⟨hloc, hok, ⟨hD, hP.trans (PoolGrew.of_frame hfr (by decide) (by decide))⟩, hres⟩

theorem callW_natPredLit (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb o cnt : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hs : SliceOK s₀.mem o cnt) (r : List Word) (m' : Mem)
    (h : callW p n "nat_pred_lit" [o, cnt] s₀.mem = some (r, m')) :
    AM.ok (natPredArm (pv (vpool s₀.mem) o.toNat cnt.toNat)) a₀ ∧
    CoreS dn m' (AM.st (natPredArm (pv (vpool s₀.mem) o.toNat cnt.toNat)) a₀) vis fe MM eb ∧
    AM.res (natPredArm (pv (vpool s₀.mem) o.toNat cnt.toNat)) a₀ = some (decE (r.headD 0)) ∧
    MemFrame natA natC s₀.mem m' ∧ PoolGrew s₀.mem m' := by
  sorry

end refs10


theorem natLitToConstructor_zero_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    (natLitToConstructor 0).run a = (constE (decI (pinW m 3))).run a := by
  simp only [natLitToConstructor, StateT.run_bind, pinNatZero_run h, except_ok_bind]

theorem natLitToConstructor_succ_run {m : Mem} {a a₁ a₂ a₃ : AState} (h : PinsFull m a.pins)
    (k : Nat) (sc l f : EIdx)
    (h1 : (constE (decI (pinW m 4))).run a = .ok (sc, a₁))
    (h2 : (internE (.lit (.natVal k))).run a₁ = .ok (l, a₂))
    (h3 : (internE (.app sc l)).run a₂ = .ok (f, a₃)) :
    (natLitToConstructor (k + 1)).run a = .ok (f, a₃) := by
  simp only [natLitToConstructor, StateT.run_bind, pinNatSucc_run h, except_ok_bind, h1, h2, h3]

theorem natPredArm_succ_run {a₁ a₂ : AState} {k : Nat} {x : EIdx}
    (h : (natPredArm (k + 1)).run a₁ = .ok (some x, a₂)) :
    (internE (.lit (.natVal k))).run a₁ = .ok (x, a₂) := by
  have e : (natPredArm (k + 1)).run a₁ =
      Except.map (fun q => (some q.1, q.2)) ((internE (.lit (.natVal k))).run a₁) := by
    simp only [natPredArm, Nat.add_sub_cancel, StateT.run_bind]
    cases (internE (.lit (.natVal k))).run a₁ <;> rfl
  rw [e] at h
  cases hh : (internE (.lit (.natVal k))).run a₁ with
  | error e => rw [hh] at h; cases h
  | ok q =>
    rw [hh] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨x', a'⟩ := q
    simp only at h1 h2
    rw [h1, h2]

section refs11
variable (p : Prog)

@[refines ConRon.Arena.natLitToConstructor]
theorem natLitToCtor_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb o cnt : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hs : SliceOK s₀.mem o cnt)
    (hnorm : Norm (vpool s₀.mem) o.toNat cnt.toNat) :
    CoreSpec p n "nat_lit_to_ctor" [o, cnt]
      (natLitToConstructor (pv (vpool s₀.mem) o.toNat cnt.toNat)) decH s₀ a₀ dn vis fe MM eb := by
  sorry

end refs11


/-! ## `lit_to_ctor_if_nat` -/


/-- The model of `lit_to_ctor_if_nat`. -/
l_model litToCtorIfNat_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.litToCtorIfNat ↦ litToCtorIfNatW ]
  specs [callW_spec p n "nat_lit_supported", callW_spec p n "nat_lit_to_ctor"]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] gen 30


theorem litToCtor_run_notlit (fe : IFEnv) (a : AState) (h : Word) (hh : HW h) (hg : tagW h ≠ 8) :
    (litToCtorIfNat fe (decE h)).run a = .ok (decE h, a) := by
  sorry

theorem litToCtor_run_str (fe : IFEnv) (a : AState) (h : Word) (hh : HW h) (hg : tagW h = 8)
    (s : String) (hv : a.store.view (decE h) = some (.lit (.strVal s))) :
    (litToCtorIfNat fe (decE h)).run a = .ok (decE h, a) := by
  sorry

theorem litToCtor_run_unsup (fe : IFEnv) (a a₁ : AState) (h : Word) (hh : HW h)
    (hg : tagW h = 8) (N : Nat) (hv : a.store.view (decE h) = some (.lit (.natVal N)))
    (hs : (natLitSupported fe).run a = .ok (false, a₁)) :
    (litToCtorIfNat fe (decE h)).run a = .ok (decE h, a₁) := by
  sorry

theorem litToCtor_run_sup (fe : IFEnv) (a a₁ a₂ : AState) (h : Word) (hh : HW h)
    (hg : tagW h = 8) (N : Nat) (hv : a.store.view (decE h) = some (.lit (.natVal N)))
    (hs : (natLitSupported fe).run a = .ok (true, a₁)) (x : EIdx)
    (hc : (natLitToConstructor N).run a₁ = .ok (x, a₂)) :
    (litToCtorIfNat fe (decE h)).run a = .ok (x, a₂) := by
  sorry

section refs12
variable (p : Prog)

@[refines ConRon.Arena.litToCtorIfNat]
theorem litToCtorIfNat_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb h : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hh : HW h) :
    CoreSpec p n "lit_to_ctor_if_nat" [vis, h] (litToCtorIfNat fe (decE h)) decH s₀ a₀ dn vis fe MM
      eb := by
  sorry

end refs12


/-! ## `const_val_at` -/

/-- `constValC` gains an entry (copy of `CoreS.set_wh`, at `cvSch`: array 103, `CTL` 110/111). -/
theorem CoreS.set_cv {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (nm us x : Word)
    (hn : HW nm) (hu : HW us) (hx : HW x) (hs : msetG cvSch m nm us x = some m') :
    CoreS dn m' { a with caches := { a.caches with
        constValC := a.caches.constValC.insert (decI nm, decI us) (decE x) } } vis fe M eb ∧
      StackKept m m' := by
  sorry

/-- The model of `const_val_at`. -/
l_model constValAt_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.constValAt ↦ constValAtW]
  specs [memoFindG_spec cvSch p _ hp.cvFind n, memoPutG_spec cvSch p _ hp.cvPut n,
    callW_spec p n "inst_lp"]
  grind [arena_grind]


theorem constValAt_run_hit (a : AState) (n : NIdx) (lps : List NIdx) (value : EIdx) (us : LsIdx)
    (r : EIdx) (hm : a.caches.constValC[(n, us)]? = some r) :
    (constValAt n lps value us).run a = .ok (r, a) := by
  simp only [constValAt, StateT.run_bind, StateT.run_get, pure_bind, hm]; rfl

theorem constValAt_run_miss (a a₁ : AState) (n : NIdx) (lps : List NIdx) (value : EIdx) (us : LsIdx)
    (r : EIdx) (hm : a.caches.constValC[(n, us)]? = none)
    (hI : (instLPFast coreWalkFuel lps us value).run a = .ok (r, a₁)) :
    (constValAt n lps value us).run a = .ok (r, { a₁ with caches := { a₁.caches with
      constValC := a₁.caches.constValC.insert (n, us) r } }) := by
  simp only [constValAt, StateT.run_bind, StateT.run_get, pure_bind, hm, hI, except_ok_bind]; rfl

section refs13
variable (p : Prog)

theorem callW_constValAt (hp : WhnfDeltaProg p) (hlp : InstLPOK p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb nm po pl value us : Word) (lps : List NIdx) (hC : CoreS dn s₀.mem a₀ vis fe MM eb)
    (hnm : HW nm) (hv : HW value) (hu : HW us)
    (hlps : hslice? (erecP s₀.mem) po.toNat pl.toNat = some lps) (r : List Word) (m' : Mem)
    (h : callW p n "const_val_at" [nm, po, pl, value, us] s₀.mem = some (r, m')) :
    CoreRef (constValAt (decI nm) lps (decE value) (decI us)) a₀ decH dn s₀.mem vis fe MM eb r m'
      ResH := by
  sorry

theorem constValAt_refines' (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb nm po pl value us : Word) (lps : List NIdx)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hnm : HW nm) (hv : HW value) (hu : HW us)
    (hlp : InstLPOK p) (hlps : hslice? (erecP s₀.mem) po.toNat pl.toNat = some lps) :
    CoreSpec p n "const_val_at" [nm, po, pl, value, us]
      (constValAt (decI nm) lps (decE value) (decI us)) decH s₀ a₀ dn vis fe MM eb :=
  CoreSpec.of_call fun r m' h => callW_constValAt p hp hlp n s₀ a₀ dn vis fe MM eb nm po pl value us lps
    hC hnm hv hu hlps r m' h

end refs13


/-! ## `unfold_definition` -/

/-- The model of `unfold_defn_at`: `(flag, result, memory)`. -/
def unfoldDefnAtW (p : Prog) (n : Nat) (m : Mem) (e nw usw q : Word) : Option (Word × Word × Mem) :=
  if tagW usw ≠ 0 then none
  else if tierW usw ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m LVLS (tierW usw) ≤ idxW usw then none
  else if tfld m LVLS (tierW usw) (idxW usw) 1 ≠ rdW (m.arr64 EREC) (q + 3) then
    some (0, 0, m)
  else
  match callW p n "const_val_at" [nw, rdW (m.arr64 EREC) (q + 2), rdW (m.arr64 EREC) (q + 3),
      rdW (m.arr64 EREC) (q + 5), usw] m with
  | none => none
  | some (r₃, m₃) =>
  match callW p n "get_app_args" [e] m₃ with
  | none => none
  | some (r₄, m₄) =>
  match callW p n "mk_app_n" [r₃.headD 0, r₄.headD 0, r₄.tail.headD 0] m₄ with
  | none => none
  | some (r₅, m₅) => some (1, r₅.headD 0, m₅.set64 CTL 136 (rdW (m₃.arr64 CTL) 136))

theorem unfoldDefnAt_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (e nw usw q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "unfold_defn_at" [e, nw, usw, q]
    ⦃fun r s' => LocEq s' s₀ ∧
      unfoldDefnAtW p n s₀.mem e nw usw q = some (r.headD 0, r.tail.headD 0, s'.mem) ∧
      ((r.headD 0 ≠ 0) → (136 : Word).toNat < (s'.mem.arr64 CTL).size); ⊤⦄ := by
  sorry

/-- The model of `unfold_definition`: `(flag, result, memory)`. -/
l_model unfoldDefinition_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.unfoldDefinition ↦ unfoldDefinitionW tuple]
  specs [callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "unfold_defn_at"]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] gen 30


/-- The twin's tail of `unfoldDefinition`, once the head is a `defnInfo` constant. -/
def unfoldTailT (n : NIdx) (us : LsIdx) (cv : IConstantVal) (value e : EIdx) : AM (Option EIdx) := do
  let usl ← viewLs us
  if usl.length = cv.levelParams.length then do
    let v ← constValAt n cv.levelParams value us
    let args ← getAppArgs coreWalkFuel e
    let r ← mkAppN v args
    pure (some r)
  else pure none

theorem LsStore.viewLen_eq_map (st : LsStore) (i : LsIdx) :
    st.viewLen i = (st.view i).map List.length := by
  simp only [LsStore.viewLen, LsStore.view, LsStore.persGetLen, LsTables.getLen, LsTables.get]
  split
  · split <;> simp [Option.map_map, Function.comp_def]
  · split
    · split <;> simp [Option.map_map, Function.comp_def]
    · rfl

theorem whnf_viewLs_run {a : AState} {h : LsIdx} {l : LsNodeView} (hv : a.store.lss.view h = some l) :
    (viewLs h).run a = .ok (l, a) := by
  simp [viewLs, StateT.run_bind, StateT.run_get, hv]; rfl

theorem unfoldTail_run_ne {a : AState} {n : NIdx} {us : LsIdx} {cv : IConstantVal} {value e : EIdx}
    {l : LsNodeView} (hv : a.store.lss.view us = some l) (hne : l.length ≠ cv.levelParams.length) :
    (unfoldTailT n us cv value e).run a = .ok (none, a) := by
  simp only [unfoldTailT, StateT.run_bind, whnf_viewLs_run hv, except_ok_bind, hne, ↓reduceIte]; rfl

theorem unfoldTail_run_ok {a a₁ a₂ : AState} {n : NIdx} {us : LsIdx} {cv : IConstantVal}
    {value e v r : EIdx} {args : List EIdx} {l : LsNodeView} (hv : a.store.lss.view us = some l)
    (heq : l.length = cv.levelParams.length)
    (hc : (constValAt n cv.levelParams value us).run a = .ok (v, a₁))
    (hargs : (getAppArgs coreWalkFuel e).run a₁ = .ok (args, a₁))
    (hmk : (mkAppN v args).run a₁ = .ok (r, a₂)) :
    (unfoldTailT n us cv value e).run a = .ok (some r, a₂) := by
  simp only [unfoldTailT, StateT.run_bind, whnf_viewLs_run hv, except_ok_bind, heq, ↓reduceIte, hc,
    hargs, hmk]; rfl

section refs14
variable (p : Prog)

/-- **`mk_app_n` as a run**: the twin's `mkAppN`, `ArenaD` after it, only the `app` tables written,
and the result a handle word. -/
theorem callW_mkAppN (hp : SpineProg p) (n : Nat) (s₀ : St) (a₀ : AState) (hD : ArenaD s₀.mem a₀)
    (f o k : Word) (xs : Array EIdx) (hf : HW f) (hx : SpineR s₀.mem o k xs) (r : List Word)
    (m' : Mem) (h : callW p n "mk_app_n" [f, o, k] s₀.mem = some (r, m')) :
    AM.ok (mkAppN (decE f) xs.toList) a₀ ∧ ArenaD m' (AM.st (mkAppN (decE f) xs.toList) a₀) ∧
    AM.res (mkAppN (decE f) xs.toList) a₀ = decE (r.headD 0) ∧
    MemFrame [AREC, ASLOT, ADER, tier1 AREC, tier1 ASLOT, tier1 ADER] [4, 5] s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, -, hok, hD', hres, hfr⟩ := triple_of_callW (Q := fun r s' =>
      LocEq s' s₀ ∧ AM.ok (mkAppN (decE f) xs.toList) a₀ ∧
        ArenaD s'.mem (AM.st (mkAppN (decE f) xs.toList) a₀) ∧
        AM.res (mkAppN (decE f) xs.toList) a₀ = decE (r.headD 0) ∧
        MemFrame [AREC, ASLOT, ADER, tier1 AREC, tier1 ASLOT, tier1 ADER] [4, 5] s₀.mem s'.mem)
    (mkAppN_refines p hp n s₀ a₀ hD f o k xs hf hx) h
  obtain ⟨s'', hm⟩ := triple_of_callW (mkAppNL_spec p hp.derb hp.appf hp.appp hp.appi hp.mkapp hp.mkn
    n s₀ f o k) h
  exact ⟨hok, hD', hres, hfr, mkAppNFromW_hw k.toNat s₀.mem a₀ f o k 0 (by simp) hD hf _ _ hm.2.2⟩

end refs14


section refs15
variable (p : Prog)

theorem callW_unfoldDefnAt (hp : WhnfDeltaProg' p) (hlp : InstLPOK p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb e nw usw q : Word) (cv : IConstantVal) (value : EIdx) (hint : ConLeche.ReducibilityHint)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) (hnw : HW nw) (hus : HW usw)
    (hci : decCI (erecP s₀.mem) q.toNat = some (.defnInfo cv value hint))
    (hk1 : rdW (s₀.mem.arr64 EREC) q = 1) (r : List Word) (m' : Mem)
    (h : callW p n "unfold_defn_at" [e, nw, usw, q] s₀.mem = some (r, m')) :
    CoreRef (unfoldTailT (decI nw) (decI usw) cv value (decE e)) a₀ decOptR dn s₀.mem vis fe MM eb r
      m' ResW := by
  sorry

end refs15


theorem unfoldDef_run_notconst (fe : IFEnv) (e hh : EIdx) (a : AState)
    (hgf : (getAppFn coreWalkFuel e).run a = .ok (hh, a)) (ht : (hh.tag == ETag.const) = false) :
    (unfoldDefinition fe e).run a = .ok (none, a) := by
  simp only [unfoldDefinition, StateT.run_bind, hgf, except_ok_bind, ht]; rfl

theorem unfoldDef_run_nodefn (fe : IFEnv) (e hh : EIdx) (a : AState) (n : NIdx) (us : LsIdx)
    (hgf : (getAppFn coreWalkFuel e).run a = .ok (hh, a)) (ht : (hh.tag == ETag.const) = true)
    (hv : a.store.view hh = some (.const n us))
    (hfind : ∀ cv v hint, fe.find? n ≠ some (.defnInfo cv v hint)) :
    (unfoldDefinition fe e).run a = .ok (none, a) := by
  simp only [unfoldDefinition, StateT.run_bind, hgf, except_ok_bind, ht, ↓reduceIte,
    view_run _ _ _ hv]
  cases hf : fe.find? n with
  | none => rfl
  | some ci =>
    cases ci with
    | defnInfo cv v hint => exact absurd hf (hfind cv v hint)
    | _ => rfl

theorem unfoldDef_run_tail (fe : IFEnv) (e hh : EIdx) (a : AState) (n : NIdx) (us : LsIdx)
    (cv : IConstantVal) (value : EIdx) (hint : ConLeche.ReducibilityHint)
    (hgf : (getAppFn coreWalkFuel e).run a = .ok (hh, a)) (ht : (hh.tag == ETag.const) = true)
    (hv : a.store.view hh = some (.const n us)) (hfind : fe.find? n = some (.defnInfo cv value hint)) :
    (unfoldDefinition fe e).run a = (unfoldTailT n us cv value e).run a := by
  simp only [unfoldDefinition, StateT.run_bind, hgf, except_ok_bind, ht, ↓reduceIte,
    view_run _ _ _ hv, hfind, unfoldTailT]

section refs16
variable (p : Prog)

theorem callW_unfoldDefinition (hp : WhnfDeltaProg' p) (hlp : InstLPOK p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb e : Word) (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) (r : List Word) (m' : Mem)
    (h : callW p n "unfold_definition" [vis, e] s₀.mem = some (r, m')) :
    CoreRef (unfoldDefinition fe (decE e)) a₀ decOptR dn s₀.mem vis fe MM eb r m' ResW := by
  sorry

/-- **`unfold_definition` refines `unfoldDefinition`**, given the stub `inst_lp`'s spec. -/
theorem unfoldDefinition_refines' (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb e : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) (hlp : InstLPOK p) :
    CoreSpec p n "unfold_definition" [vis, e] (unfoldDefinition fe (decE e)) decOptR s₀ a₀ dn vis fe
      MM eb ResW :=
  CoreSpec.of_call fun r m' h => callW_unfoldDefinition p hp hlp n s₀ a₀ dn vis fe MM eb e hC he r m' h

end refs16

end L.Arena
