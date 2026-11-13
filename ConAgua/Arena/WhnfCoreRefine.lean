module

public import ConAgua.Arena.WhnfCore
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.DerRel
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.Env
import all ConAgua.Arena.WhnfCore

@[expose] public section

/-!
# Refinements of `WhnfCore.lean`'s functions (other than the slot and the loop)

The callW pattern of `WhnfCoreSlot.lean`, one function at a time.

* Environment reads: `env_find`'s flag `≠ 0` means the name has a record that decodes
  (`envFind_refines`): the L code may read the record's words where the twin matches
  on the decoded constant (`decCI_ctor`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `env_find`: a found row is a row -/

/-- The kind word of a decoded constant record says whether it is a constructor, and a
constructor's type is the handle at `q + 4`. -/
theorem decCI_ctor {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {ci : IConstantInfo} (h : decCI R q.toNat = some ci) :
    (rd q = 4 → ∃ cv np nf fam, ci = .ctorInfo cv np nf fam ∧ cv.type = decI (rd (q + 4)) ∧
      (rd (q + 4)).toNat < 2 ^ 32) ∧
    (rd q ≠ 4 → ∀ cv np nf fam, ci ≠ .ctorInfo cv np nf fam) := by
  have hs := decCI_split hR h
  refine ⟨fun h4 => ?_, hs.2.2.2.2.2⟩
  obtain ⟨cv, np, nf, rfl, hcv⟩ := hs.2.2.2.2.1 h4
  obtain ⟨-, -, hty, hlt⟩ := decCV_rd hR hcv
  exact ⟨cv, np, nf, rfl, hty, hlt⟩

/-! ## Runs of plain triples -/

/-! ## `proj_cert` -/

/-- The model of `proj_cert`, its callees through their runs. -/
def projCertW (p : Prog) (n : Nat) (m : Mem) (vis k _ao an : Word) : Option (Word × Mem) :=
  match callW p n "env_find" [k, vis] m with
  | none => none
  | some (r₁, m₁) =>
    if r₁.headD 0 = 0 then some (0, m₁)
    else if erRd m₁ (r₁.tail.headD 0) ≠ 4 then some (0, m₁)
    else match callW p n "peel_pis" [an, erRd m₁ (r₁.tail.headD 0 + 4)] m₁ with
      | none => none
      | some (r₂, m₂) => some (if r₂.headD 0 ≠ 0 then 1 else 0, m₂)

section pc
variable (p : Prog) (n : Nat) (m m₁ m₂ : Mem) (vis k ao an : Word) (r₁ r₂ : List Word)

theorem projCertW_none (h : callW p n "env_find" [k, vis] m = some (r₁, m₁)) (h0 : r₁.headD 0 = 0) :
    projCertW p n m vis k ao an = some (0, m₁) := by
  simp only [projCertW, h, h0, ↓reduceIte]

theorem projCertW_kind (h : callW p n "env_find" [k, vis] m = some (r₁, m₁)) (h0 : ¬ r₁.headD 0 = 0)
    (h4 : erRd m₁ (r₁.tail.headD 0) ≠ 4) :
    projCertW p n m vis k ao an = some (0, m₁) := by
  simp only [projCertW, h, h0, h4, ↓reduceIte, ne_eq, not_false_eq_true]

theorem projCertW_peel (h : callW p n "env_find" [k, vis] m = some (r₁, m₁)) (h0 : ¬ r₁.headD 0 = 0)
    (h4 : ¬ erRd m₁ (r₁.tail.headD 0) ≠ 4)
    (h2 : callW p n "peel_pis" [an, erRd m₁ (r₁.tail.headD 0 + 4)] m₁ = some (r₂, m₂)) :
    projCertW p n m vis k ao an = some (if r₂.headD 0 ≠ 0 then 1 else 0, m₂) := by
  simp only [projCertW, h, h0, h4, h2, ↓reduceIte]

end pc

theorem projCert_spec (p : Prog) (hp : WhnfCoreProg p) (n : Nat) (s₀ : St) (vis k ao an : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "proj_cert" [vis, k, ao, an]
    ⦃fun r s' => LocEq s' s₀ ∧ projCertW p n s₀.mem vis k ao an = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.cert]
  simp only [callFn, projCertL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "env_find", callW_spec p n "peel_pis"] <;>
    finish [projCertW_none, projCertW_kind, projCertW_peel]

theorem projCert_run_none (fe : IFEnv) (c : NIdx) (args : List EIdx) (a : AState)
    (h : ∀ cv np nf fam, fe.find? c ≠ some (.ctorInfo cv np nf fam)) :
    (projCert fe c args).run a = .ok (false, a) := by
  unfold projCert
  cases e : fe.find? c with
  | none => rfl
  | some ci =>
    cases ci with
    | ctorInfo cv np nf _ => exact absurd e (h cv np nf)
    | _ => rfl

theorem projCert_run_ctor (fe : IFEnv) (c : NIdx) (args : List EIdx) (a : AState)
    (cv : IConstantVal) (np nf : Nat) {fam : NIdx} (h : fe.find? c = some (.ctorInfo cv np nf fam)) (o : Option EIdx)
    (hp : (peelPis args.length cv.type).run a = .ok (o, a)) :
    (projCert fe c args).run a = .ok (o.isSome, a) := by
  simp only [projCert, h, teleArityOk, StateT.run_bind, hp, except_ok_bind]; rfl

/-- **`proj_cert` refines `projCert`** (the verified mode's `projCertAt`). -/
@[refines ConRon.Arena.projCert]
theorem projCert_refines (p : Prog) (hp : WhnfCoreProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb k ao an : Word)
    (args : Array EIdx) (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (hk : HW k)
    (har : SpineR s₀.mem ao an args) :
    CoreSpec p (n + 1) "proj_cert" [vis, k, ao, an] (projCert fe (decI k) args.toList) decBool s₀ a₀
      dn vis fe MM eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (projCert_spec p hp n s₀ vis k ao an)
  subst hs0
  refine ⟨hloc, ?_⟩
  simp only [projCertW] at hW
  rcases hc : callW p n "env_find" [k, vis] s.mem with _ | ⟨r₁, m₁⟩ <;> simp only [hc, reduceCtorEq] at hW
  obtain ⟨t₁, ht₁, hm₁, -, hfind, hdec⟩ := triple_of_callW
    (envFind_refines p hp.envrow hp.baserow hp.envfind n s vis k hS.env hk) hc
  rw [ht₁] at hm₁
  subst hm₁
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    have hnone : fe.find? (decI k) = none := by rw [hfind]; simp only [envFound, h0, ↓reduceIte]
    have hrun' := projCert_run_none fe (decI k) args.toList a₀ (fun cv np nf h => by
      rw [hnone] at h; cases h)
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
    rw [← hm]
    refine ⟨hok, ?_, ?_, ?_⟩
    · rw [hst]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
    · rw [hres]; simp only [decBool]; rw [← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [ite_eq_right h0] at hW
  obtain ⟨ci, hci⟩ := hdec h0
  have hfind' : fe.find? (decI k) = some ci := by
    rw [hfind]; simp only [envFound, h0, ↓reduceIte]; exact hci
  have hctor := decCI_ctor (erRdOK _) hci
  by_cases h4 : erRd s.mem (r₁.tail.headD 0) ≠ 4
  · rw [ite_eq_left h4] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    have hrun' := projCert_run_none fe (decI k) args.toList a₀ (fun cv np nf h => by
      rw [hfind'] at h; cases h; exact hctor.2 h4 cv np nf rfl)
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
    rw [← hm]
    refine ⟨hok, ?_, ?_, ?_⟩
    · rw [hst]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
    · rw [hres]; simp only [decBool]; rw [← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [ite_eq_right h4] at hW
  obtain ⟨cv, np, nf, rfl, hty, htw⟩ := hctor.1 (by simpa using h4)
  rcases hc2 : callW p n "peel_pis" [an, erRd s.mem (r₁.tail.headD 0 + 4)] s.mem with _ | ⟨r₂, m₂⟩ <;> simp only [hc2, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hW
  obtain ⟨hr, hm⟩ := hW
  obtain ⟨t₂, ht₂, hm₂, -, -, hpeel⟩ := triple_of_callW
    (peelPis_refines p hp.spine n s a₀ hS.arena.base an _ htw) hc2
  rw [ht₂] at hm₂
  have hlen : args.toList.length = an.toNat := by simp [har.size]
  rw [decE_eq, ← hty, ← hlen] at hpeel
  have hrun' := projCert_run_ctor fe (decI k) args.toList a₀ cv np nf hfind' _ hpeel
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  rw [← hm, hm₂]
  refine ⟨hok, ?_, ?_, ?_⟩
  · rw [hst]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
  · rw [hres]; simp only [decBool]; rw [← hr]; simp only [decOpt]; split <;> simp_all
  · unfold ResH HW; rw [← hr]; split <;> decide

/-! ## Stack writers keep the relation; slices below the top survive -/

theorem CoreS.frame_stk {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List TieredArray} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b = SPN)
    (hC : ∀ x ∈ C, x = 136) : CoreS dn m' a vis fe M eb := by
  have aA : ∀ lo hi : Nat, hi ≤ 144 → AvoidA lo hi A := fun lo hi h b hb => by
    rw [hA b hb]; right; simp only [SPN]; omega
  have aC : ∀ lo hi : Nat, hi ≤ 136 → AvoidC lo hi C := fun lo hi h x hx => by
    have := hA; rw [hC x hx]; right; simpa using h
  exact ⟨⟨ArenaR.frame_ext A C (fun b hb => by rw [hA b hb]; decide)
      (fun x hx => by rw [hC x hx]; decide) m m' hf a hS.arena.base,
      DerR.frameM A C m m' hf (fun b hb => by rw [hA b hb]; decide) a hS.arena.der⟩,
    hS.core.frame (aA 96 128 (by decide)) (aC 96 128 (by decide)) hf,
    hS.pins.congr (hf.arr PINS (fun h => by have := hA _ h; simp [PINS, SPN] at this) (by decide)),
    hS.env.frame (fun b hb => by rw [hA b hb]; decide) (fun x hx => by rw [hC x hx]; decide) hf,
    hS.readL, hS.readLs, hS.nwf, hf.size EREC ▸ hS.erec, hf.size SPN ▸ hS.spn,
    hS.memos.frame_hi hf (fun b hb => by rw [hA b hb]; decide) (fun x hx => by rw [hC x hx]; decide)
      (fun b hb => by rw [hA b hb]; decide) (fun x hx => by rw [hC x hx]; decide)
      (fun h => by have := hA _ h; simp [L.Ind.HBM, SPN] at this) (fun h => by have := hC _ h; simp at this),
    hf.size BSTK ▸ hS.bstk,
    hS.den.frameE (hf.arr EREC (fun h => by have := hA _ h; simp [EREC, SPN] at this) (by decide)),
    hS.mode.frame hf (fun h => by have := hC _ h; simp at this) (fun h => by have := hC _ h; simp at this),
    hS.iwF hf (fun h => by have := hA _ h; simp [EREC, SPN] at this)
      (fun h => by have := hA _ h; simp [SPN] at this) (fun h => by have := hC _ h; simp at this)
      (fun h => by have := hC _ h; simp at this) (fun h => by have := hC _ h; simp at this)⟩

theorem SpineR.keep {m m' : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (hsz : (m'.arr64 SPN).size = (m.arr64 SPN).size)
    (hk : ∀ i : Word, i < spTop m → spW m' i = spW m i)
    (htop : off.toNat + cnt.toNat ≤ (spTop m).toNat) (hspn : (m.arr64 SPN).size < 2 ^ 63) :
    SpineR m' off cnt xs := by
  have hb := h.bound
  have hlt : ∀ i : Nat, i < cnt.toNat → off + i.toUInt64 < spTop m := by
    intro i hi
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_ofNat']
    have : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.mod_eq_of_lt (by omega)]; omega
  refine ⟨h.size, hsz ▸ hb, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hk _ (hlt i hi)]; exact h.lt i hi
  · rw [hk _ (hlt i (h.size ▸ hi))]; exact h.get i hi


/-! ## Stack and word helpers (used by the app arm and `whnf_app`) -/

/-- The top restored after a run that kept everything below the old top. -/
theorem StackKept.restore {m m₁ : Mem} (hk : ∀ i : Word, i < spTop m → spW m₁ i = spW m i)
    (hsz : (m₁.arr64 SPN).size = (m.arr64 SPN).size) (hb : BKept m m₁) (hp : PoolGrew m m₁)
    (h136 : (136 : Word).toNat < (m₁.arr64 CTL).size) :
    StackKept m (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) := by
  have hfs : MemFrame [] [136] m₁ (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) :=
    MemFrame.setCtl m₁ 136 _
  have hspn : (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)).arr64 SPN = m₁.arr64 SPN :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨?_, by rw [hspn, hsz], fun i hi => by simp only [spW, hspn]; exact hk i hi,
    hb.trans (BKept.of_frame hfs (by decide) (by decide)),
    hp.trans (PoolGrew.of_frame hfs (by decide) (by decide))⟩
  simp only [spTop, rdW_set64]
  have : (136 : Word).toNat = 136 := rfl
  simp only [this] at h136
  simp; intro h; omega

/-- The top restored after a run that grew the stack. -/
theorem StackKept.restoreG {m m₁ : Mem} (hg : StackGrew m m₁)
    (h136 : (136 : Word).toNat < (m₁.arr64 CTL).size) :
    StackKept m (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) :=
  StackKept.restore hg.below hg.size hg.bstk hg.pool h136

/-- `CTL[136]` (the stack top) is a word of the control array: the walk memos' counters sit above
it (`CoreMemos`). -/
theorem CoreS.ctl136 {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {m : Mem} {a : AState} (hS : CoreS dn m a vis fe M eb) :
    136 < (m.arr64 CTL).size := by
  obtain ⟨mp, h⟩ := hS.memos.walk.lsb
  unfold MemoRG MemoRV at h
  have := h.1
  simp only at this
  have e : (156 : Word).toNat = 156 := rfl
  omega

/-- `StackKept.restoreG` without the bound: out of bounds the top reads `0`, so the old top was
`0` too. -/
theorem StackKept.restoreG' {m m₁ : Mem} (hg : StackGrew m m₁) :
    StackKept m (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) := by
  by_cases h136 : (136 : Word).toNat < (m₁.arr64 CTL).size
  · exact StackKept.restoreG hg h136
  have h0 : spTop m₁ = 0 := by
    simp only [spTop, rdW, Array.getElem?_eq_none (Nat.le_of_not_lt h136)]; rfl
  have hfs := MemFrame.setCtl m₁ 136 (rdW (m.arr64 CTL) 136)
  have hspn : (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)).arr64 SPN = m₁.arr64 SPN :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨?_, by rw [hspn, hg.size], fun i hi => by simp only [spW, hspn]; exact hg.below i hi,
    hg.bstk.trans (BKept.of_frame hfs (by decide) (by decide)),
    hg.pool.trans (PoolGrew.of_frame hfs (by decide) (by decide))⟩
  have hle := hg.top
  rw [h0] at hle
  rw [spTop, rdW_set64, ite_eq_right (fun h => h136 h.2.2)]
  show spTop m₁ = spTop m
  rw [h0]
  rw [UInt64.le_iff_toNat_le] at hle
  exact UInt64.toNat_inj.mp (by simp at hle ⊢; omega)

/-- The twin's second half of the `.app` clause. -/
def whnfCoreApp2T (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (v h : EIdx)
    (args nodes : Array EIdx) : AM WhnfStep := do
  let hv ← headAndArgs v
  whnfApp mode r fe depth v hv.1 hv.2 (v == h) args nodes 0

theorem evalW_eq_ne (v h : Word) (hv : HW v) (hh : HW h) :
    (Cmp.evalW .eq v h != 0) = (decE v == decE h) := by
  rw [decE_eq, decE_eq, decI_beq v h hv hh]
  by_cases e : v = h <;> simp [Cmp.evalW, Cmp.eval, e]

end L.Arena
