module

import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.StoreDenIntern
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.DerRel
import ConAgua.Arena.PinsNatOp
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.L.ModelGen
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.WhnfCoreApp
public import ConAgua.Arena.WhnfDelta
import all ConAgua.Arena.Pins
import all ConAgua.Arena.WhnfDelta
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.ConstStore
import all ConAgua.Arena.NatAdd
import all ConAgua.Arena.NatArms
import all ConAgua.Arena.NatBits
import all ConAgua.Arena.NatCmp
import all ConAgua.Arena.NatDiv
import all ConAgua.Arena.NatGcd
import all ConAgua.Arena.NatMul
import all ConAgua.Arena.NatPow
import all ConAgua.Arena.NatShl
import all ConAgua.Arena.NatShr
import all ConAgua.Arena.NatSub
import all ConAgua.Arena.Refine
import all ConAgua.Arena.Store

@[expose] public section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

theorem decCV_words {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV (aread a) q = some cv) :
    (∃ w, a[q]? = some w ∧ w.toNat < 2 ^ 32 ∧ cv.name = decI w) ∧
    (∃ w, a[q + 2]? = some w ∧ cv.levelParams.length = w.toNat) ∧
    (∃ w, a[q + 3]? = some w ∧ w.toNat < 2 ^ 32 ∧ cv.type = decI w) := by
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨n, hn, l, hl, t, ht, hc⟩ := h
  cases Option.some.inj hc
  refine ⟨hd?_eq hn, ?_, hd?_eq ht⟩
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hl
  obtain ⟨o, ho, c, hc', hs⟩ := hl
  simp only [nat?, Option.map_eq_some_iff] at hc'
  obtain ⟨w, hw, rfl⟩ := hc'
  exact ⟨w, hw, hslice?_length hs⟩

/-! ## Environment records: the shape lemmas the nat-literal and delta functions read -/

theorem rdW_off {b : Array Word} {q c : Word} {i : Nat} {w : Word} (hb : b[i]? = some w)
    (hi : q.toNat + c.toNat = i) (hsz : b.size < 2 ^ 63) : rdW b (q + c) = w := by
  have hlt : i < b.size := (Array.getElem?_eq_some_iff.mp hb).1
  have : (q + c).toNat = i := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
  simp only [rdW, this, hb]; rfl

/-- Shape of a record whose `decCV` succeeds at `q + 1`, read at the words `q + 2`, `q + 3`, `q + 4`. -/
theorem decCV_rd {a b : Array Word} {q : Word} {cv : IConstantVal} (hab : ArrExt (aread a) (aread b))
    (hsz : b.size < 2 ^ 63) (h : decCV (aread a) (q.toNat + 1) = some cv) :
    hslice? (aread b) (rdW b (q + 2)).toNat (rdW b (q + 3)).toNat = some cv.levelParams ∧
    cv.levelParams.length = (rdW b (q + 3)).toNat ∧
    cv.type = decI (rdW b (q + 4)) ∧ (rdW b (q + 4)).toNat < 2 ^ 32 := by
  obtain ⟨-, ⟨w3, hw3, hlen⟩, ⟨w4, hw4, hl4, hty⟩⟩ := decCV_words h
  have e3 : rdW b (q + 3) = w3 := rdW_off (hab _ _ hw3) (by simp <;> omega) hsz
  have e4 : rdW b (q + 4) = w4 := rdW_off (hab _ _ hw4) (by simp <;> omega) hsz
  refine ⟨?_, by rw [e3]; exact hlen, by rw [e4]; exact hty, by rw [e4]; exact hl4⟩
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨n, hn, l, hl, t, ht, hc⟩ := h
  cases Option.some.inj hc
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hl
  obtain ⟨o, ho, c, hc', hs⟩ := hl
  simp only [nat?, Option.map_eq_some_iff] at ho hc'
  obtain ⟨w2, hw2, rfl⟩ := ho
  obtain ⟨w3', hw3', rfl⟩ := hc'
  have e2 : rdW b (q + 2) = w2 := rdW_off (hab _ _ hw2) (by simp <;> omega) hsz
  have e3' : w3' = w3 := by
    have := hw3'.symm.trans hw3; exact Option.some.inj this
  subst e3'
  rw [e2, e3]
  exact hab.hslice? hs

/-- The kind word of a decoded record, and what each kind decodes to. -/
theorem decCI_split {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {ci : IConstantInfo} (h : decCI (aread a) q.toNat = some ci) (hab : ArrExt (aread a) (aread b))
    (hsz : b.size < 2 ^ 63) :
    (rdW b q = 1 → ∃ cv v hint, ci = .defnInfo cv v hint ∧ decCV (aread a) (q.toNat + 1) = some cv ∧
      v = decI (rdW b (q + 5)) ∧ (rdW b (q + 5)).toNat < 2 ^ 32) ∧
    (rdW b q ≠ 1 → ∀ cv v hint, ci ≠ .defnInfo cv v hint) ∧
    (rdW b q = 3 → ∃ cv caps, ci = .indInfo cv caps ∧ decCV (aread a) (q.toNat + 1) = some cv) ∧
    (rdW b q ≠ 3 → ∀ cv caps, ci ≠ .indInfo cv caps) ∧
    (rdW b q = 4 → ∃ cv np nf, ci = .ctorInfo cv np nf ∧ decCV (aread a) (q.toNat + 1) = some cv) ∧
    (rdW b q ≠ 4 → ∀ cv np nf, ci ≠ .ctorInfo cv np nf) := by
  sorry

/-! ## Calls of the leaf readers, as facts about their runs -/

theorem pinAt_word_spec (p : Prog) (hp : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St)
    (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_at" [i]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ pinW s₀.mem 0 ≠ 0 ∧ i.toNat < 51 ∧
      r.headD 0 = pinW s₀.mem (1 + i.toNat); ⊤⦄ := by
  sorry

theorem pinWord_word_spec (p : Prog) (hp : p.lookup "pin_word" = some pinWordL) (n : Nat) (s₀ : St)
    (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_word" [k]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ pinW s₀.mem 0 ≠ 0 ∧
      r.headD 0 = pinW s₀.mem k.toNat; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, pinWordL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;> finish [pinW_eq]

theorem callW_pinAt (p : Prog) (hp : p.lookup "pin_at" = some pinAtL) (n : Nat) (m : Mem)
    (i : Word) (r : List Word) (m' : Mem) (h : callW p n "pin_at" [i] m = some (r, m')) :
    m' = m ∧ pinW m 0 ≠ 0 ∧ i.toNat < 51 ∧ r.headD 0 = pinW m (1 + i.toNat) := by
  obtain ⟨s', hs', hmem, -, h0, h1, h2⟩ :=
    triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (pinAt_word_spec p hp n _ i) h
  exact ⟨hs'.symm.trans hmem, h0, h1, h2⟩

theorem callW_pinWord (p : Prog) (hp : p.lookup "pin_word" = some pinWordL) (n : Nat) (m : Mem)
    (k : Word) (r : List Word) (m' : Mem) (h : callW p n "pin_word" [k] m = some (r, m')) :
    m' = m ∧ pinW m 0 ≠ 0 ∧ r.headD 0 = pinW m k.toNat := by
  obtain ⟨s', hs', hmem, -, h0, h2⟩ :=
    triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (pinWord_word_spec p hp n _ k) h
  exact ⟨hs'.symm.trans hmem, h0, h2⟩

/-! ## `CoreS` across a `const` interning -/

theorem keeps_cpl_internConst (n : NIdx) (us : LsIdx) : Keeps cpl (internE (.const n us)) := by
  simp only [internE]; exact keeps_cpl_internNodeE _

theorem keeps_cpl_internLit (l : ConLeche.Literal) : Keeps cpl (internE (.lit l)) := by
  simp only [internE]; exact keeps_cpl_internNodeE _

theorem CoreS.of_const {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
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

theorem StackKept.of_const_frame {m m' : Mem} (hf : MemFrame [CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP] [18, 19] m m') :
    StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.arr SPN (by simp [tier1, CREC, CSLOT, CLP, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.ctl 136 (by simp)
  exact StackKept.of_frame hf

/-- **An interned `const` handle word is below `2^32`.** -/
theorem ceinternW_hw (m : Mem) (a : AState) (hR : ConstR m a) (f x : Word) (_hf : f.toNat < 2 ^ 32)
    (_hx : x.toNat < 2 ^ 32) (w : Word) (m' : Mem) (hI : ceinternW m f x = some (w, m')) :
    w.toNat < 2 ^ 32 := by
  exact consInternM_lt constCS_wf hR hI

section progs
variable (p : Prog)

/-- **`intern_const` as a run.** -/
theorem callW_internConst (hpf : p.lookup "const_find" = some constFind)
    (hpp : p.lookup "const_push" = some constPush) (hp : p.lookup "intern_const" = some internConst)
    (n : Nat) (s₀ : St) (a₀ : AState) (hD : ArenaD s₀.mem a₀) (f x : Word) (hf : HW f) (hx : HW x)
    (r : List Word) (m' : Mem) (h : callW p n "intern_const" [f, x] s₀.mem = some (r, m')) :
    AM.ok (internE (.const (decI f) (decI x))) a₀ ∧
    ArenaD m' (AM.st (internE (.const (decI f) (decI x))) a₀) ∧
    AM.res (internE (.const (decI f) (decI x))) a₀ = decI (r.headD 0) ∧
    MemFrame [CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP] [18, 19] s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, hm⟩ := triple_of_callW (internConst_spec p hpf hpp hp n s₀ f x) h
  obtain ⟨-, hm⟩ := hm
  obtain ⟨h1, h2, h3⟩ := internConst_D s₀.mem a₀ hD f x _ hf hx _ hm
  refine ⟨h1, h2, h3, ?_, ceinternW_hw s₀.mem a₀ ?_ f x hf hx _ _ hm⟩
  · exact ceinternW_frame (hI := hm)
  · exact hD.base.const

end progs

/-! ## The `Nat` functions' write set -/

/-- The `Nat` arms' program, with `nat_succ_lit`. -/
def natArmProg' : Prog := natArmProg ++ [("nat_succ_lit", natSuccLitL)]
def natFns : List FnName := natArmProg'.map (·.1)
/-- What they write: the pool, the `lit` table (2, 3), the `const` table (18, 19 = `CREC`, `CSLOT`,
and its `lp` column `CLP`), and the counts. -/
def natA : List TieredArray := [POOL, POOL1, REC, tier1 REC, SLOT, tier1 SLOT, CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP]
def natC : List Word := [0, 2, 3, 18, 19]
theorem natArmProg'_closed : closedA natArmProg' natA natC natFns = true := by decide +kernel

theorem WhnfDeltaProg'.natClosed_of_agree {p : Prog}
    (h : ∀ f ∈ natFns, p.lookup f = natArmProg'.lookup f) : closedA p natA natC natFns = true :=
  closedW_of_agree natArmProg'_closed h

/-! ## The program hypotheses -/

/-- `WhnfDeltaProg` plus the functions the callees' own specs need (the `mk_app`/`get_app_*` family
of `SpineProg`, the `const` and `lit` interning, the memo and pool functions). -/
structure WhnfDeltaProg' (p : Prog) : Prop extends WhnfDeltaProg p where
  spine : SpineProg p
  constFind' : p.lookup "const_find" = some constFind
  constPush' : p.lookup "const_push" = some constPush
  envRow' : p.lookup "env_row_get" = some envRowGetL
  predLit : p.lookup "nat_pred_lit" = some natPredLit
  natLimb' : p.lookup "nat_limb" = some natLimb
  subBorrow' : p.lookup "sub_borrow" = some subBorrow
  natTrim' : p.lookup "nat_trim" = some natTrim
  addCarry' : p.lookup "add_carry" = some addCarry
  natAdd' : p.lookup "nat_add" = some natAdd
  litHash' : p.lookup "lit_hash" = some litHash
  limbsEq' : p.lookup "limbs_eq" = some limbsEq
  litMatch' : p.lookup "lit_match" = some litMatch
  litFind' : p.lookup "lit_find" = some litFind
  litPush' : p.lookup "lit_push" = some litPush
  /-- `p` agrees with `natArmProg'` on the `Nat` functions (`natFns`): their write set
  (`natClosed`) and `nat_op_result`'s refinement (`CoreNatOp.lean`) carry over. -/
  natAgree : ∀ f ∈ natFns, p.lookup f = natArmProg'.lookup f

/-- The write set of the `Nat` functions (`natFns`): the pool, the `lit` and `const` tables. -/
theorem WhnfDeltaProg'.natClosed {p : Prog} (hp : WhnfDeltaProg' p) :
    closedA p natA natC natFns = true :=
  WhnfDeltaProg'.natClosed_of_agree hp.natAgree

theorem CoreSpec.zero {α : Type} [Inhabited α] {p : Prog} {f : FnName} {fd : FunDecl}
    (hf : p.lookup f = some fd) (args : List Word) (T : AM α) (dec : List Word → α) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb : Word) (ok : List Word → Prop) :
    CoreSpec p 0 f args T dec s₀ a₀ dn vis fe MM eb ok := by
  unfold CoreSpec
  rw [invoke_eq _ hf]
  simp only [callFn]
  vcgen [exec] <;> grind

/-! ## `const_e` -/

/-- The model of `const_e`. -/
l_model constE_spec (p : Prog) (hp : p.lookup "const_e" = some constEL)
  fns [hp ↦ constEW]
  specs [callW_spec p n "pin_word", callW_spec p n "intern_const"]
  grind [arena_grind]
  gen 30

theorem constE_run {m : Mem} {a : AState} (h : PinsFull m a.pins) (n : NIdx) :
    (constE n).run a = (internE (.const n (decI (pinW m 52)))).run a := by
  simp only [constE, emptyLevels, StateT.run_bind, pinEmptyLevels_run h]; rfl

/-- **A refinement spec from the calls' runs**: the callee's run (`callW`) and the post. -/
theorem CoreSpec.of_call {α : Type} [Inhabited α] {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {T : AM α} {dec : List Word → α} {s₀ : St} {a₀ : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {ok : List Word → Prop}
    (h : ∀ (r : List Word) (m' : Mem), callW p n f args s₀.mem = some (r, m') →
      CoreRef T a₀ dec dn s₀.mem vis fe M eb r m' ok) :
    CoreSpec p n f args T dec s₀ a₀ dn vis fe M eb ok := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hc⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (callW_spec p n f args s₀)
  subst hs0
  exact ⟨hloc, h r s'.mem hc⟩

section refs
variable (p : Prog)

/-- **`const_e` as a run**: the twin's interning, the relation after it (same maps), only the
`const` tables written, and the result a handle word. -/
theorem callW_constE (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb nm : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hnm : HW nm) (r : List Word) (m' : Mem)
    (h : callW p n "const_e" [nm] s₀.mem = some (r, m')) :
    AM.ok (constE (decI nm)) a₀ ∧ CoreS dn m' (AM.st (constE (decI nm)) a₀) vis fe MM eb ∧
    AM.res (constE (decI nm)) a₀ = decH r ∧ MemFrame [CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP] [18, 19] s₀.mem m' ∧
    HW (r.headD 0) := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (constE_spec p hp.constE (n + 1) s₀ nm) h
  cases h1 : callW p n "pin_word" [52] s₀.mem with
  | none => simp only [constEW, constEW.k_pin_word, h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  obtain ⟨rfl, -, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₁ m₁ h1
  simp only [show (52 : Word).toNat = 52 from rfl] at hr₁
  cases h2 : callW p n "intern_const" [nm, r₁.headD 0] s₀.mem with
  | none => simp only [constEW, constEW.k_pin_word, constEW.k_intern_const, h1, h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  simp only [constEW, constEW.k_pin_word, constEW.k_intern_const, h1, h2, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  have hpw : HW (r₁.headD 0) := by rw [hr₁]; exact hC.pins.lv_lt.1
  obtain ⟨hok, hD', hres, hfr, hhw⟩ := callW_internConst p hp.constFind' hp.constPush' hp.internConst n
    s₀ a₀ hC.arena nm _ hnm hpw r₂ m₂ h2
  have hrun := constE_run hC.pins (decI nm)
  rw [← hr₁] at hrun
  obtain ⟨hok', hst', hres'⟩ := AM.congr_run hrun
  rw [← hm]
  refine ⟨by rw [hok']; exact hok, ?_, ?_, hfr, by rw [← hr]; exact hhw⟩
  · rw [hst']
    exact hC.of_const hD' (Keeps.run (keeps_cpl_internConst _ _) (AM.run_of_ok _ _ hok)) hfr
      (AM.run_of_ok _ _ hok) (by rw [hr₁, ← hC.pins.emptyLevels]; exact hC.den.emptyLs)
  · rw [hres', hres, decH, ← hr]; rfl

/-- **`const_e` refines `constE`.** `WhnfDeltaProg'` for the extra function lookups. -/
@[refines ConRon.Arena.constE]
theorem constE_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb nm : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hnm : HW nm) :
    CoreSpec p n "const_e" [nm] (constE (decI nm)) decH s₀ a₀ dn vis fe MM eb := by
  apply CoreSpec.of_call
  intro r m' h
  obtain ⟨hok, hS, hres, hfr, hhw⟩ := callW_constE p hp n s₀ a₀ dn vis fe MM eb nm hC hnm r m' h
  exact ⟨hok, ⟨MM, hS, KeptAll.refl _ _, StackKept.of_const_frame hfr⟩, hres, hhw⟩

end refs

/-! ## `nat_ind_ok`, `nat_zero_ok`, `nat_succ_ok` -/

/-- The model of `nat_ind_ok`. -/
l_model natIndOk_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.natIndOk ↦ natIndOkW]
  specs [callW_spec p n "pin_word"]
  grind [arena_grind]
  gen 30

/-- **A call that may only intern `const` nodes**: the twin's run succeeds, the relation holds
after it at the same maps, the result words decode to the twin's result, and the memory moved only in
the `const` tables. -/
def CRef {α : Type} [Inhabited α] (T : AM α) (a₀ : AState) (dec : List Word → α)
    (dn : NIdx → Option ConLeche.Name) (m₀ : Mem) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb : Word) (r : List Word) (m' : Mem) (ok : List Word → Prop) : Prop :=
  AM.ok T a₀ ∧ CoreS dn m' (AM.st T a₀) vis fe M eb ∧ AM.res T a₀ = dec r ∧
    MemFrame [CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP] [18, 19] m₀ m' ∧ ok r

theorem CRef.pure {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop}
    (hC : CoreS dn m a₀ vis fe M eb) (b : α) (hrun : T.run a₀ = .ok (b, a₀)) (hres : dec r = b)
    (hok : ok r) : CRef T a₀ dec dn m vis fe M eb r m ok := by
  obtain ⟨h1, h2, h3⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨h1, by rw [h2]; exact hC, by rw [h3, hres], MemFrame.refl _ _ _, hok⟩

theorem CRef.core {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m' : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop}
    (h : CRef T a₀ dec dn m₀ vis fe M eb r m' ok) : CoreRef T a₀ dec dn m₀ vis fe M eb r m' ok :=
  ⟨h.1, ⟨M, h.2.1, KeptAll.refl _ _, StackKept.of_const_frame h.2.2.2.1⟩, h.2.2.1, h.2.2.2.2⟩

theorem CoreSpec.of_callC {α : Type} [Inhabited α] {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {T : AM α} {dec : List Word → α} {s₀ : St} {a₀ : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {ok : List Word → Prop}
    (h : ∀ (r : List Word) (m' : Mem), callW p n f args s₀.mem = some (r, m') →
      CRef T a₀ dec dn s₀.mem vis fe M eb r m' ok) :
    CoreSpec p n f args T dec s₀ a₀ dn vis fe M eb ok :=
  CoreSpec.of_call fun r m' hc => (h r m' hc).core

theorem ResH_ite (P : Prop) [Decidable P] : ResH [if P then 1 else 0] := by
  unfold ResH HW; by_cases h : P <;> simp [h]

theorem decBool_ite' (P : Prop) [Decidable P] : decBool [if P then 1 else 0] = decide P := by
  by_cases h : P <;> simp [h, decBool]

theorem natIndOk_run_none (a : AState) : (natIndOk none).run a = .ok (false, a) := rfl

theorem natIndOk_run_other {ci : IConstantInfo} (h : ∀ cv caps, ci ≠ .indInfo cv caps) (a : AState) :
    (natIndOk (some ci)).run a = .ok (false, a) := by
  cases ci with
  | indInfo cv caps => exact absurd rfl (h cv caps)
  | _ => rfl

theorem natIndOk_run_ind {m : Mem} {a : AState} (hP : PinsFull m a.pins) (cv : IConstantVal)
    (caps : IIndCaps) :
    (natIndOk (some (.indInfo cv caps))).run a =
      .ok (cv.levelParams.isEmpty && cv.type == decI (pinW m 54), a) := by
  simp only [natIndOk, sortOne, StateT.run_bind, pinSortOne_run hP]; rfl

section refs2
variable (p : Prog)

/-- `find?`'s result `(found, q)` decoded (`none` at `found = 0`). -/
def decFound (_dn : NIdx → Option ConLeche.Name) (m : Mem) (f q : Word) : Option IConstantInfo :=
  if f = 0 then none else decCI (erecP m) q.toNat

theorem callW_natIndOk (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb found q : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb)
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP s₀.mem) q.toNat = some ci)
    (r : List Word) (m' : Mem) (h : callW p n "nat_ind_ok" [found, q] s₀.mem = some (r, m')) :
    CRef (natIndOk (decFound dn s₀.mem found q)) a₀ decBool dn s₀.mem vis fe MM eb r m' ResH := by
  sorry

@[refines ConRon.Arena.natIndOk]
theorem natIndOk_refines (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb found q : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (_hq : HW q)
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP s₀.mem) q.toNat = some ci) :
    CoreSpec p n "nat_ind_ok" [found, q] (natIndOk (decFound dn s₀.mem found q)) decBool s₀ a₀ dn
      vis fe MM eb :=
  CoreSpec.of_callC fun r m' h => callW_natIndOk p hp n s₀ a₀ dn vis fe MM eb found q hC hdec r m' h

end refs2

/-! ## `nat_zero_ok` -/

/-- The model of `nat_zero_ok`. -/
l_model natZeroOk_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.natZeroOk ↦ natZeroOkW]
  specs [callW_spec p n "pin_at", callW_spec p n "const_e"]
  grind [arena_grind]
  gen 30

theorem pinNat_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    pinNat.run a = .ok (decI (pinW m 2), a) := pinAt_run h 1 (by decide)

theorem natZeroOk_run_none (a : AState) : (natZeroOk none).run a = .ok (false, a) := rfl

theorem natZeroOk_run_other {ci : IConstantInfo} (h : ∀ cv np nf, ci ≠ .ctorInfo cv np nf)
    (a : AState) : (natZeroOk (some ci)).run a = .ok (false, a) := by
  cases ci with
  | ctorInfo cv np nf => exact absurd rfl (h cv np nf)
  | _ => rfl

theorem natZeroOk_run_ctor {m : Mem} {a a₁ : AState} (hP : PinsFull m a.pins) (cv : IConstantVal)
    (np nf : Nat) (nc : EIdx) (h : (constE (decI (pinW m 2))).run a = .ok (nc, a₁)) :
    (natZeroOk (some (.ctorInfo cv np nf))).run a =
      .ok (cv.levelParams.isEmpty && cv.type == nc, a₁) := by
  simp only [natZeroOk, StateT.run_bind, pinNat_run hP, except_ok_bind, h]; rfl

theorem MemFrame.arr_eq {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (b : TieredArray) (hb : b ∉ A) (hc : b ≠ CTL) : m'.arr64 b = m.arr64 b := hf.arr b hb hc

section refs3
variable (p : Prog)

theorem callW_natZeroOk (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb found q : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb)
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP s₀.mem) q.toNat = some ci)
    (r : List Word) (m' : Mem) (h : callW p n "nat_zero_ok" [found, q] s₀.mem = some (r, m')) :
    CRef (natZeroOk (decFound dn s₀.mem found q)) a₀ decBool dn s₀.mem vis fe MM eb r m' ResH := by
  sorry

@[refines ConRon.Arena.natZeroOk]
theorem natZeroOk_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb found q : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (_hq : HW q)
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP s₀.mem) q.toNat = some ci) :
    CoreSpec p n "nat_zero_ok" [found, q] (natZeroOk (decFound dn s₀.mem found q)) decBool s₀ a₀ dn
      vis fe MM eb :=
  CoreSpec.of_callC fun r m' h => callW_natZeroOk p hp n s₀ a₀ dn vis fe MM eb found q hC hdec r m' h

end refs3

/-! ## `nat_succ_ok` -/

/-- The model of `nat_succ_ok`. -/
l_model natSuccOk_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.natSuccOk ↦ natSuccOkW]
  specs [callW_spec p n "pin_at", callW_spec p n "const_e"]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] gen 30

theorem natSuccOk_run_none (a : AState) : (natSuccOk none).run a = .ok (false, a) := rfl

theorem natSuccOk_run_other {ci : IConstantInfo} (h : ∀ cv np nf, ci ≠ .ctorInfo cv np nf)
    (a : AState) : (natSuccOk (some ci)).run a = .ok (false, a) := by
  cases ci with
  | ctorInfo cv np nf => exact absurd rfl (h cv np nf)
  | _ => rfl

theorem natSuccOk_run_lps (a : AState) (cv : IConstantVal) (np nf : Nat)
    (h : cv.levelParams.isEmpty = false) :
    (natSuccOk (some (.ctorInfo cv np nf))).run a = .ok (false, a) := by
  simp only [natSuccOk, h]; rfl

theorem natSuccOk_run_nonforall {m : Mem} {a a₁ : AState} (hP : PinsFull m a.pins)
    (cv : IConstantVal) (np nf : Nat) (nc : EIdx) (hl : cv.levelParams.isEmpty = true)
    (h : (constE (decI (pinW m 2))).run a = .ok (nc, a₁))
    (ht : (cv.type.tag == ETag.forallE) = false) :
    (natSuccOk (some (.ctorInfo cv np nf))).run a = .ok (false, a₁) := by
  simp only [natSuccOk, hl, StateT.run_bind, pinNat_run hP, except_ok_bind, h, ht, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]; rfl

theorem natSuccOk_run_forall {m : Mem} {a a₁ : AState} (hP : PinsFull m a.pins)
    (cv : IConstantVal) (np nf : Nat) (nc dom body : EIdx) (hl : cv.levelParams.isEmpty = true)
    (h : (constE (decI (pinW m 2))).run a = .ok (nc, a₁))
    (ht : (cv.type.tag == ETag.forallE) = true) (hv : a₁.store.view cv.type = some (.forallE dom body)) :
    (natSuccOk (some (.ctorInfo cv np nf))).run a = .ok (dom == nc && body == nc, a₁) := by
  simp only [natSuccOk, hl, StateT.run_bind, pinNat_run hP, except_ok_bind, h, ht,
    view_run _ _ _ hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rfl

section refs4
variable (p : Prog)

/-- The generated models branch outside the result tuple. -/
theorem ite_some_pair {α β : Type} (c : Prop) [Decidable c] (a b : α) (m : β) :
    (if c then some (a, m) else some (b, m)) = some (if c then a else b, m) := by
  split <;> rfl

theorem callW_natSuccOk (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb found q : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb)
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP s₀.mem) q.toNat = some ci)
    (r : List Word) (m' : Mem) (h : callW p n "nat_succ_ok" [found, q] s₀.mem = some (r, m')) :
    CRef (natSuccOk (decFound dn s₀.mem found q)) a₀ decBool dn s₀.mem vis fe MM eb r m' ResH := by
  sorry

@[refines ConRon.Arena.natSuccOk]
theorem natSuccOk_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb found q : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (_hq : HW q)
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP s₀.mem) q.toNat = some ci) :
    CoreSpec p n "nat_succ_ok" [found, q] (natSuccOk (decFound dn s₀.mem found q)) decBool s₀ a₀ dn
      vis fe MM eb :=
  CoreSpec.of_callC fun r m' h => callW_natSuccOk p hp n s₀ a₀ dn vis fe MM eb found q hC hdec r m' h

end refs4

/-! ## `env_find` as a run -/

section refs5
variable (p : Prog)

/-- **`env_find` as a run**: memory unchanged, the result is the twin's lookup, and a found row
decodes. -/
theorem callW_envFind (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) {dn : NIdx → Option ConLeche.Name}
    {fe : IFEnv} (vis w : Word) (hE : EnvR s₀.mem vis fe) (hw : HW w) (r : List Word) (m' : Mem)
    (h : callW p n "env_find" [w, vis] s₀.mem = some (r, m')) :
    m' = s₀.mem ∧ fe.find? (decI w) = decFound dn s₀.mem (r.headD 0) (r.tail.headD 0) ∧
    (r.headD 0 ≠ 0 → ∃ ci, decCI (erecP s₀.mem) (r.tail.headD 0).toNat = some ci) := by
  sorry

end refs5

/-! ## `nat_op_stored` -/

section refs6
variable (p : Prog)

end refs6

/-! ## `nat_lit_supported` -/

/-- The model of `nat_lit_supported`. -/
l_model natLitSupported_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.natLitSupported ↦ natLitSupportedW]
  specs [callW_spec p n "pin_at", callW_spec p n "env_find", callW_spec p n "nat_ind_ok", callW_spec p n "nat_zero_ok", callW_spec p n "nat_succ_ok"]
  grind [arena_grind]
  gen 30

theorem pinNatZero_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    pinNatZero.run a = .ok (decI (pinW m 3), a) := pinAt_run h 2 (by decide)

theorem pinNatSucc_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    pinNatSucc.run a = .ok (decI (pinW m 4), a) := pinAt_run h 3 (by decide)

section nlsRun
variable {m m' m'' : Mem} {a a₁ a₂ a₃ : AState} (fe : IFEnv)

theorem natLitSupported_run_1 (hP : PinsFull m a.pins)
    (hI : (natIndOk (fe.find? (decI (pinW m 2)))).run a = .ok (false, a₁)) :
    (natLitSupported fe).run a = .ok (false, a₁) := by
  simp only [natLitSupported, StateT.run_bind, pinNat_run hP, except_ok_bind, hI, Bool.not_false, ↓reduceIte]; rfl

theorem natLitSupported_run_2 (hP : PinsFull m a.pins) (hP' : PinsFull m' a₁.pins)
    (hI : (natIndOk (fe.find? (decI (pinW m 2)))).run a = .ok (true, a₁))
    (hZ : (natZeroOk (fe.find? (decI (pinW m' 3)))).run a₁ = .ok (false, a₂)) :
    (natLitSupported fe).run a = .ok (false, a₂) := by
  simp only [natLitSupported, StateT.run_bind, pinNat_run hP, except_ok_bind, hI,
    pinNatZero_run hP', hZ, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]; rfl

theorem natLitSupported_run_3 (hP : PinsFull m a.pins) (hP' : PinsFull m' a₁.pins)
    (hP'' : PinsFull m'' a₂.pins) (b : Bool)
    (hI : (natIndOk (fe.find? (decI (pinW m 2)))).run a = .ok (true, a₁))
    (hZ : (natZeroOk (fe.find? (decI (pinW m' 3)))).run a₁ = .ok (true, a₂))
    (hS : (natSuccOk (fe.find? (decI (pinW m'' 4)))).run a₂ = .ok (b, a₃)) :
    (natLitSupported fe).run a = .ok (b, a₃) := by
  simp only [natLitSupported, StateT.run_bind, pinNat_run hP, except_ok_bind, hI,
    pinNatZero_run hP', hZ, pinNatSucc_run hP'', hS, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

end nlsRun

section refs7
variable (p : Prog)

/-- **`pin_at(k); env_find(·, vis)` as runs**: the pinned name's lookup. -/
theorem callW_pinFind (hp : WhnfDeltaProg' p) (k : Word) (hk : k.toNat < 51) (n : Nat) (m : Mem)
    {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} (vis : Word) {a : AState}
    (hC : ∃ M eb, CoreS dn m a vis fe M eb) (r₁ : List Word) (m₁ : Mem) (r₂ : List Word) (m₂ : Mem)
    (h1 : callW p n "pin_at" [k] m = some (r₁, m₁))
    (h2 : callW p n "env_find" [r₁.headD 0, vis] m₁ = some (r₂, m₂)) :
    m₁ = m ∧ m₂ = m ∧ fe.find? (decI (pinW m (1 + k.toNat))) =
        decFound dn m (r₂.headD 0) (r₂.tail.headD 0) ∧
      (r₂.headD 0 ≠ 0 → ∃ ci, decCI (erecP m) (r₂.tail.headD 0).toNat = some ci) := by
  obtain ⟨M, eb, hC⟩ := hC
  obtain ⟨hm1, -, -, hr₁⟩ := callW_pinAt p hp.pinAt n m k r₁ m₁ h1
  subst m₁
  have hnt : HW (r₁.headD 0) := by
    rw [hr₁]; exact hC.pins.names_lt _ (by omega)
  obtain ⟨hm2, hfind, hdec⟩ := callW_envFind p hp n ⟨m, Locals.init []⟩ vis _ hC.env hnt r₂ m₂ h2
  subst m₂
  refine ⟨rfl, rfl, ?_, hdec⟩
  rw [← hr₁]
  exact hfind

end refs7

section refs8
variable (p : Prog)

theorem callW_natLitSupported (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (r : List Word) (m' : Mem)
    (h : callW p n "nat_lit_supported" [vis] s₀.mem = some (r, m')) :
    CRef (natLitSupported fe) a₀ decBool dn s₀.mem vis fe MM eb r m' ResH := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (natLitSupported_spec p hp.toWhnfDeltaProg (n + 1) s₀ vis) h
  rw [natLitSupportedW.eq_2] at hW
  -- stage 1
  rcases h1 : callW p n "pin_at" [1] s₀.mem with _ | ⟨a₁, m₁⟩ <;> simp only [h1, natLitSupportedW.k_pin_at, reduceCtorEq] at hW
  rcases h2 : callW p n "env_find" [a₁.headD 0, vis] m₁ with _ | ⟨b₁, m₂⟩
    <;> simp only [h2, natLitSupportedW.k_env_find, reduceCtorEq] at hW
  obtain ⟨hm1, hm2, hfind1, hdec1⟩ := callW_pinFind p hp 1 (by decide) n s₀.mem vis ⟨MM, eb, hC⟩
    a₁ m₁ b₁ m₂ h1 h2
  subst hm1 hm2
  rcases h3 : callW p n "nat_ind_ok" [b₁.headD 0, b₁.tail.headD 0] s₀.mem with _ | ⟨c₁, m₃⟩
    <;> simp only [h3, natLitSupportedW.k_nat_ind_ok, reduceCtorEq] at hW
  obtain ⟨hok1, hS1, hres1, hfr1, hrh1⟩ := callW_natIndOk p hp.toWhnfDeltaProg n s₀ a₀ dn vis fe MM eb
    _ _ hC hdec1 c₁ m₃ h3
  have hI : (natIndOk (fe.find? (decI (pinW s₀.mem 2)))).run a₀ =
      .ok (decBool c₁, AM.st (natIndOk (decFound dn s₀.mem (b₁.headD 0) (b₁.tail.headD 0))) a₀) := by
    have := AM.run_of_ok _ _ hok1
    rw [hres1] at this
    rw [show pinW s₀.mem 2 = pinW s₀.mem (1 + (1 : Word).toNat) from rfl, hfind1]
    exact this
  by_cases hc1 : c₁.headD 0 = 0
  · rw [ite_eq_left hc1] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    have hb : decBool c₁ = false := by simp only [decBool, hc1]; rfl
    rw [hb] at hI
    have hz := natLitSupported_run_1 fe hC.pins hI
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', by rw [hst']; exact hS1, ?_, hfr1, ?_⟩
    · rw [hres']; simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [ite_eq_right hc1] at hW
  have hb : decBool c₁ = true := by simp only [decBool, bne_iff_ne, ne_eq]; exact hc1
  rw [hb] at hI
  -- stage 2
  rcases h4 : callW p n "pin_at" [2] m₃ with _ | ⟨a₂, m₄⟩ <;> simp only [h4, natLitSupportedW.k_pin_at_2, reduceCtorEq] at hW
  rcases h5 : callW p n "env_find" [a₂.headD 0, vis] m₄ with _ | ⟨b₂, m₅⟩
    <;> simp only [h5, natLitSupportedW.k_env_find_2, reduceCtorEq] at hW
  obtain ⟨hm4, hm5, hfind2, hdec2⟩ := callW_pinFind p hp 2 (by decide) n m₃ vis ⟨_, _, hS1⟩
    a₂ m₄ b₂ m₅ h4 h5
  subst m₄ m₅
  rcases h6 : callW p n "nat_zero_ok" [b₂.headD 0, b₂.tail.headD 0] m₃ with _ | ⟨c₂, m₆⟩
    <;> simp only [h6, natLitSupportedW.k_nat_zero_ok, reduceCtorEq] at hW
  obtain ⟨hok2, hS2, hres2, hfr2, hrh2⟩ : CRef
      (natZeroOk (decFound dn m₃ (b₂.headD 0) (b₂.tail.headD 0)))
      (AM.st (natIndOk (decFound dn s₀.mem (b₁.headD 0) (b₁.tail.headD 0))) a₀) decBool dn m₃ vis fe
      MM eb c₂ m₆ ResH :=
    callW_natZeroOk p hp n ⟨m₃, Locals.init []⟩ _ dn vis fe MM eb _ _ hS1 hdec2 c₂ m₆ h6
  have hZ : (natZeroOk (fe.find? (decI (pinW m₃ 3)))).run
      (AM.st (natIndOk (decFound dn s₀.mem (b₁.headD 0) (b₁.tail.headD 0))) a₀) =
      .ok (decBool c₂, AM.st (natZeroOk (decFound dn m₃ (b₂.headD 0) (b₂.tail.headD 0)))
        (AM.st (natIndOk (decFound dn s₀.mem (b₁.headD 0) (b₁.tail.headD 0))) a₀)) := by
    have := AM.run_of_ok _ _ hok2
    rw [hres2] at this
    rw [show pinW m₃ 3 = pinW m₃ (1 + (2 : Word).toNat) from rfl, hfind2]
    exact this
  by_cases hc2 : c₂.headD 0 = 0
  · rw [ite_eq_left hc2] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    have hb2 : decBool c₂ = false := by simp only [decBool, hc2]; rfl
    rw [hb2] at hZ
    have hz := natLitSupported_run_2 fe hC.pins hS1.pins hI hZ
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', by rw [hst']; exact hS2, ?_, hfr1.trans hfr2, ?_⟩
    · rw [hres']; simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [ite_eq_right hc2] at hW
  have hb2 : decBool c₂ = true := by simp only [decBool, bne_iff_ne, ne_eq]; exact hc2
  rw [hb2] at hZ
  -- stage 3
  rcases h7 : callW p n "pin_at" [3] m₆ with _ | ⟨a₃, m₇⟩ <;> simp only [h7, natLitSupportedW.k_pin_at_3, reduceCtorEq] at hW
  rcases h8 : callW p n "env_find" [a₃.headD 0, vis] m₇ with _ | ⟨b₃, m₈⟩
    <;> simp only [h8, natLitSupportedW.k_env_find_3, reduceCtorEq] at hW
  obtain ⟨hm7, hm8, hfind3, hdec3⟩ := callW_pinFind p hp 3 (by decide) n m₆ vis ⟨_, _, hS2⟩
    a₃ m₇ b₃ m₈ h7 h8
  subst m₇ m₈
  rcases h9 : callW p n "nat_succ_ok" [b₃.headD 0, b₃.tail.headD 0] m₆ with _ | ⟨c₃, m₉⟩
    <;> simp only [h9, natLitSupportedW.k_nat_succ_ok, reduceCtorEq] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  rw [← hm]
  obtain ⟨hok3, hS3, hres3, hfr3, hrh3⟩ : CRef
      (natSuccOk (decFound dn m₆ (b₃.headD 0) (b₃.tail.headD 0)))
      (AM.st (natZeroOk (decFound dn m₃ (b₂.headD 0) (b₂.tail.headD 0)))
        (AM.st (natIndOk (decFound dn s₀.mem (b₁.headD 0) (b₁.tail.headD 0))) a₀)) decBool dn m₆ vis fe
      MM eb c₃ m₉ ResH :=
    callW_natSuccOk p hp n ⟨m₆, Locals.init []⟩ _ dn vis fe MM eb _ _ hS2 hdec3 c₃ m₉ h9
  have hS : (natSuccOk (fe.find? (decI (pinW m₆ 4)))).run
      (AM.st (natZeroOk (decFound dn m₃ (b₂.headD 0) (b₂.tail.headD 0)))
        (AM.st (natIndOk (decFound dn s₀.mem (b₁.headD 0) (b₁.tail.headD 0))) a₀)) =
      .ok (decBool c₃, AM.st (natSuccOk (decFound dn m₆ (b₃.headD 0) (b₃.tail.headD 0)))
        (AM.st (natZeroOk (decFound dn m₃ (b₂.headD 0) (b₂.tail.headD 0)))
          (AM.st (natIndOk (decFound dn s₀.mem (b₁.headD 0) (b₁.tail.headD 0))) a₀))) := by
    have := AM.run_of_ok _ _ hok3
    rw [hres3] at this
    rw [show pinW m₆ 4 = pinW m₆ (1 + (3 : Word).toNat) from rfl, hfind3]
    exact this
  have hz := natLitSupported_run_3 fe hC.pins hS1.pins hS2.pins (decBool c₃) hI hZ hS
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  refine ⟨hok', by rw [hst']; exact hS3, ?_, (hfr1.trans hfr2).trans hfr3, ?_⟩
  · rw [hres']; simp only [decBool, ← hr]
  · show ResH [r.headD 0]
    rw [← hr]; exact hrh3

@[refines ConRon.Arena.natLitSupported]
theorem natLitSupported_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) :
    CoreSpec p n "nat_lit_supported" [vis] (natLitSupported fe) decBool s₀ a₀ dn vis fe MM eb :=
  CoreSpec.of_callC fun r m' h => callW_natLitSupported p hp n s₀ a₀ dn vis fe MM eb hC r m' h

end refs8

end L.Arena
