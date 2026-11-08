module

public import ConAgua.Arena.IndPosSpec.NestBlockOfKey
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos2

@[expose] public section

/-!
# EntryW

`blk_k3`, `stripW_wrap`, `nestCtorEntryStrip_spec`, `erec_nat`, `erec_hd`, `decCI_kind_cases` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem blk_k3 {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {c : Word} {m : Mem}
    (found q : Word) (hfound : fe.find? (decI c) = decFound dn m found q) (h0 : found ≠ 0)
    (hex : ∃ ci, decCI (erecP m) q.toNat = some ci) (hk : rdW (m.arr64 EREC) q = 3) :
    hslice? (erA m) (rdW (m.arr64 EREC) (q + 15)).toNat (rdW (m.arr64 EREC) (q + 16)).toNat =
      some (nestBlockOf fe (decI c)) := by
  obtain ⟨ci, hci⟩ := hex
  obtain ⟨k, hkn⟩ : ∃ k, nat? (erecP m) q.toNat = some k := by
    simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hci
    obtain ⟨k, hk, -⟩ := hci
    exact ⟨k, hk⟩
  have hkn' : nat? (erA m) q.toNat = some k := by
    simp only [nat?, Option.map_eq_some_iff] at hkn ⊢
    obtain ⟨w, hw, rfl⟩ := hkn
    exact ⟨w, erecP_get hw, rfl⟩
  have hrd := erN_rdW hkn' q.toNat_lt
  rw [UInt64.ofNat_toNat] at hrd
  have hk3 : k = 3 := by
    have h1 : UInt64.ofNat k = 3 := by rw [← hrd]; exact hk
    have h2 := congrArg UInt64.toNat h1
    rw [UInt64.toNat_ofNat_of_lt' (nat?_lt hkn')] at h2
    simpa using h2
  subst hk3
  obtain ⟨cv, caps, hI, -⟩ := decCI_kind3 hci hkn
  subst hI
  have hb := decCI_indInfo_bound hci
  have hsz := erecP_size_lt m
  have := nestBlockOf_key found q hfound (fun _ => ⟨cv, caps, hci⟩) (fun _ => by omega)
  simpa [h0, hk] using this
-/

section arms
variable (m m1 : Mem) (ciq nPc nF : Word) (r : List Word)
theorem stripW_wrap (h : rdW (m.arr64 EREC) ciq = 4)
    (h2 : rdW (m.arr64 EREC) (ciq + 5) + rdW (m.arr64 EREC) (ciq + 6) < rdW (m.arr64 EREC) (ciq + 5)) :
    stripW m ciq = none := by
  simp [stripW, h, h2]
end arms
grind_pattern [ind_grind] stripW_wrap => stripW m ciq
theorem nestCtorEntryStrip_spec (p : Prog) (hp : p.lookup "nest_ctor_entry_strip" = some nestCtorEntryStrip)
    (hst : StripProg p) (n : Nat) (s₀ : St) (ciq : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctor_entry_strip" [ciq]
    ⦃fun r s' => LocEq s' s₀ ∧ stripW s₀.mem ciq = some (r, s'.mem); ⊤⦄ := by
  sorry

theorem erec_nat {m : Mem} {w : Word} {c : Nat} {k : Nat} (h : nat? (erecP m) (w.toNat + c) = some k)
    (hc : c < 2 ^ 64) : rdW (m.arr64 EREC) (w + UInt64.ofNat c) = UInt64.ofNat k ∧ k < 2 ^ 64 := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, rfl⟩ := h
  exact ⟨by rw [erec_rd hv hc]; simp, v.toNat_lt⟩

theorem erec_hd {m : Mem} {w : Word} {c : Nat} {k : IdxKind} {x : Idx k}
    (h : hd? (erecP m) (w.toNat + c) = some x) (hc : c < 2 ^ 64) :
    ∃ v, rdW (m.arr64 EREC) (w + UInt64.ofNat c) = v ∧ v.toNat < 2 ^ 32 ∧ decI v = x := by
  obtain ⟨v, hv, hlt, rfl⟩ := hd?_some h
  exact ⟨v, erec_rd hv hc, hlt, rfl⟩

/-- A record's kind word and, for a constructor, its fields. -/
theorem decCI_kind_cases {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {ci : IConstantInfo} (h : decCI (aread a) p = some ci) :
    ∃ k, nat? (aread a) p = some k ∧
      ((k = 4 ∧ ∃ cv nPc nF, ci = .ctorInfo cv nPc nF ∧ decCV (aread a) (p + 1) = some cv ∧
          nat? (aread a) (p + 5) = some nPc ∧ nat? (aread a) (p + 6) = some nF) ∨
       (k ≠ 4 ∧ ∀ cv nPc nF, ci ≠ .ctorInfo cv nPc nF)) := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  refine ⟨k, hk, ?_⟩
  match k, h with
  | 0, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 1, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 2, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 3, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 4, h =>
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, a1, h1, b1, h2, rfl⟩ := h
    left; exact ⟨rfl, cv, a1, b1, rfl, hcv, h1, h2⟩
  | 5, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 6, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all []
  | (_ + 7), h => simp at h

theorem erecP_ext_grow {m m' : Mem} (hg : IWGrow m m') : ArrExt (erecP m) (erA m') := by
  sorry

/-- What `nest_ctor_entry_strip` returns, against the twin's `stripPis` result. -/
def StripOut (m : Mem) (r : List Word) (ciq : Word) (cv : IConstantVal) (nPc nF : Nat) :
    Option (List EIdx × EIdx) → Prop
  | none => r = [0, 0, 0, 0, 0]
  | some (_, b) => ∃ w, r = [1, ciq + 1, UInt64.ofNat nPc, UInt64.ofNat nF, w] ∧ w.toNat < 2 ^ 32 ∧
      decI w = b ∧ decCV (erecP m) (ciq.toNat + 1) = some cv

theorem stripW_ok {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m' : Mem}
    {a : AState} {ciq : Word} {r : List Word} {ci : IConstantInfo}
    (h : stripW m ciq = some (r, m')) (hS : StageR vis fe m a)
    (hci : decCI (erecP m) ciq.toNat = some ci) :
    (∀ cv nPc nF, ci = .ctorInfo cv nPc nF → nPc + nF < 2 ^ 64 ∧
      ∃ x a', (stripPis (nPc + nF) cv.type).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧
        IWGrow m m' ∧ StripOut m r ciq cv nPc nF x) ∧
    ((∀ cv nPc nF, ci ≠ .ctorInfo cv nPc nF) → r = [0, 0, 0, 0, 0] ∧ m' = m) := by
  sorry

theorem nestCtorEntry_spec (p : Prog) (hs : p.lookup "nest_ctor_entry_strip" = some nestCtorEntryStrip)
    (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "nest_ctor_entry" = some nestCtorEntry) (hst : StripProg p) (had : AdF p) (n : Nat) (s₀ : St)
    (C ciq : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctor_entry" [C, ciq]
    ⦃fun r s' => LocEq s' s₀ ∧ entryW s₀.mem C ciq = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCtorEntry]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestCtorEntryStrip_spec p hs hst n, gafF_spec p had n, eView_spec p hv n] <;>
      finish (gen := 20) [entryW]

def EntryOut (m' : Mem) (r : List Word) (ciq : Word) : Option (IConstantVal × Nat × Nat) → Prop
  | none => r = [0, 0, 0, 0]
  | some (cv, nPc, nF) => r = [1, ciq + 1, UInt64.ofNat nPc, UInt64.ofNat nF] ∧
      decCVp m' (ciq.toNat + 1) = some cv ∧ nPc + nF < 2 ^ 64

theorem entryW_ok {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m' : Mem}
    {a : AState} {C ciq : Word} {r : List Word} {ci : IConstantInfo} (hC : H C)
    (h : entryW m C ciq = some (r, m')) (hS : StageR vis fe m a)
    (hci : decCI (erecP m) ciq.toNat = some ci) :
    ∃ x a', (ConRon.Arena.nestCtorEntry (decI C) ci).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ EntryOut m' r ciq x := by
  sorry

theorem resHeadK_some (r : List Word) (m1 : Mem) :
    resHeadK (some (r, m1)) = some ([if tagW (r.headD 0) = 1 then 1 else 0], m1) := rfl
grind_pattern [ind_grind] resHeadK_some => resHeadK (some (r, m1))

theorem nestResHead_spec (p : Prog) (hg : p.lookup "nest_res_head" = some nestResHeadL) (had : AdF p) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_res_head" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ resHeadW s₀.mem e = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hg, callFn, nestResHeadL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        gafF_spec p had n] <;> finish [resHeadW]

theorem resHeadW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem) (a : AState)
    (e : Word) (r : List Word) (he : H e) (h : resHeadW m e = some (r, m')) (hS : StageR vis fe m a) :
    ∃ a', (ConRon.Arena.nestResHead (decI e)).run a = .ok (r.headD 0 != 0, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' := by
  unfold resHeadW at h
  rcases hs : gafF m [CWF, e] with _ | ⟨r1, m1⟩ <;> rw [hs] at h; · simp [resHeadK] at h
  simp only [resHeadK, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨x, a1, hrun, hS1, hg, hlt, hdec⟩ := gafF_ok dn vis fe CWF e he m m1 a r1 hs hS
  refine ⟨a1, ?_, hS1, hg⟩
  rw [CWF_eq] at hrun
  have htag : (x.tag == ETag.fvar) = decide (tagW (r1.headD 0) = 1) := by
    rw [← hdec]
    have := decE_tag_eq (r1.headD 0) hlt 1 (by decide)
    have e1 : (ETag.fvar : UInt32) = UInt32.ofNat 1 := rfl
    show ((decE (r1.headD 0)).tag == ETag.fvar) = _
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e1, this]
    exact Iff.rfl
  simp only [ConRon.Arena.nestResHead, StateT.run_bind]
  rw [hrun]
  simp only [bind, Except.bind, pure, htag]
  show (StateT.pure (decide (tagW (r1.headD 0) = 1))).run a1 = _
  generalize r1.headD 0 = w
  by_cases hc : tagW w = 1 <;> simp [hc, StateT.pure, StateT.run, pure, Except.pure]

end L.Ind

end
