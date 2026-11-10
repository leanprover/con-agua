module

public import ConAgua.Arena.IndRealAbs
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Arena.IndPos
import ConAgua.L.WordOff

@[expose] public section

/-!
# NestBlockOfKey

`decCI_kind3`, `decCI_indInfo_kind`, `erN_rdW`, `nat?_lt`, `hlist?_some`, `nestBlockOf_key` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `decCI`'s `indInfo` arm, at a known kind word -/

/-- **A decoded record at kind word `3` is `indInfo`**, with its caps: `decCI`'s match only
reaches the `.indInfo` arm from `nat? a p = some 3` (`Env.lean`'s `decCI_name` destructures the
same match generically, for the name field). -/
theorem decCI_kind3 {a : Nat → Option Word} {p : Nat}
    {ci : IConstantInfo} (h : decCI a p = some ci) (hk : nat? a p = some 3) :
    ∃ cv caps, ci = .indInfo cv caps ∧ decCaps a (p + 5) = some caps := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk', h⟩ := h
  have hk3 : k = 3 := Option.some.inj (hk'.symm.trans hk)
  subst hk3
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨cv, hcv, caps, hcaps, rfl⟩ := h
  exact ⟨cv, caps, rfl, hcaps⟩

/-- The contrapositive: an `indInfo` record's kind word is `3`. -/
theorem decCI_indInfo_kind {a : Nat → Option Word} {p : Nat}
    {cv : IConstantVal} {caps : IIndCaps} (h : decCI a p = some (.indInfo cv caps)) :
    nat? a p = some 3 := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  rw [hk]
  congr 1
  match k, h with
  | 0, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 1, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 2, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 3, h => rfl
  | 4, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 5, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 6, h => simp_all []
  | (_ + 7), h => simp_all

/-- A word `EREC⦃q⦄` reads at a `Nat` position, as `nat?` decodes it. -/
theorem erN_rdW {m : Mem} {q : Nat} {k : Nat} (h : nat? (erA m) q = some k) :
    erRd m (UInt64.ofNat q) = UInt64.ofNat k := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  have hqq : (UInt64.ofNat q).toNat = q := by have := erecP_lt64 hw; simp; omega
  rw [L.Arena.erRd_of _ _ (by rw [hqq]; exact hw), UInt64.ofNat_toNat]

/-- A `nat?`-decoded value is below `2 ^ 64` (it is some word's `toNat`). -/
theorem nat?_lt {a : Nat → Option Word} {i k : Nat} (h : nat? a i = some k) : k < 2 ^ 64 := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, -, rfl⟩ := h
  exact w.toNat_lt

/-- `hlist?`'s two-word header, unfolded. -/
theorem hlist?_some {k : IdxKind} {a : Nat → Option Word} {i : Nat} {xs : List (Idx k)}
    (h : hlist? a i = some xs) :
    ∃ o l, nat? a i = some o ∧ nat? a (i + 1) = some l ∧ hslice? a o l = some xs := by
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, l, hl, h⟩ := h
  exact ⟨o, l, ho, hl, h⟩

/-! ## `nest_block_of` refines `nestBlockOf`: the pure fact -/

/-- **What `nest_block_of` computes, as a function of `env_find`'s result** (`envFound`, and a
found record decodes): the key lemma, proved purely over `Mem`/`Word`, outside the L execution. -/
theorem nestBlockOf_key {fe : IFEnv} {c : Word} {m : Mem}
    (found q : Word) (hfound : fe.find? (decI c) = envFound m found q)
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP m) q.toNat = some ci) :
    hslice? (erA m)
        (if found = 0 then (0 : Word) else if erRd m q = 3 then erRd m (q + 15) else 0).toNat
        (if found = 0 then (0 : Word) else if erRd m q = 3 then erRd m (q + 16) else 0).toNat
      = some (nestBlockOf fe (decI c)) := by
  rw [nestBlockOf]
  unfold envFound at hfound
  by_cases h0 : found = 0
  · simp only [h0, hfound, ite_true]
    simp [hslice?]
  · simp only [h0, ite_false] at hfound ⊢
    obtain ⟨ci, hci⟩ := hdec h0
    rw [hci] at hfound
    obtain ⟨k, hk⟩ : ∃ k, nat? (erecP m) q.toNat = some k := by
      simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hci
      obtain ⟨k, hk, -⟩ := hci
      exact ⟨k, hk⟩
    have hrd := erN_rdW (m := m) hk
    rw [UInt64.ofNat_toNat] at hrd
    by_cases hk3 : erRd m q = (3 : Word)
    · have hk3' : k = 3 := by
        have h1 : UInt64.ofNat k = 3 := by rw [← hrd]; exact hk3
        have h2 := congrArg UInt64.toNat h1
        rw [UInt64.toNat_ofNat_of_lt' (nat?_lt hk)] at h2
        simpa using h2
      subst hk3'
      obtain ⟨cv, caps, rfl, hcaps⟩ := decCI_kind3 hci hk
      simp only [hfound, ite_eq_left hk3]
      simp only [decCaps, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hcaps
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, vall, hvall, _, _, _, _, heq⟩ := hcaps
      have hallcaps : caps.all = vall := by
        have h' := Option.some.inj heq; rw [← h']
      obtain ⟨o, l, ho, hl, hslc⟩ := hlist?_some hvall
      have ho' : nat? (erA m) (q.toNat + 15) = some o := by
        rw [show q.toNat + 15 = q.toNat + 5 + 10 by omega]; exact ho
      have hl' : nat? (erA m) (q.toNat + 16) = some l := by
        rw [show q.toNat + 16 = q.toNat + 5 + 10 + 1 by omega]; exact hl
      have hb : q.toNat + 16 < 2 ^ 64 := by
        simp only [nat?, Option.map_eq_some_iff] at hl'
        obtain ⟨w, hw, -⟩ := hl'; exact erecP_lt64 hw
      have e15 : (q + 15 : Word) = UInt64.ofNat (q.toNat + 15) := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by show _ < 2 ^ 64; omega)]
        simp; omega
      have e16 : (q + 16 : Word) = UInt64.ofNat (q.toNat + 16) := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by show _ < 2 ^ 64; omega)]
        simp; omega
      rw [e15, e16, erN_rdW ho', erN_rdW hl']
      have hoo : (UInt64.ofNat o).toNat = o := UInt64.toNat_ofNat_of_lt' (nat?_lt ho')
      have hll : (UInt64.ofNat l).toNat = l := UInt64.toNat_ofNat_of_lt' (nat?_lt hl')
      rw [hoo, hll, hallcaps]
      exact hslc
    · simp only [ite_eq_right hk3]
      cases ci with
      | indInfo cv caps =>
        exfalso; apply hk3
        have hk' := decCI_indInfo_kind hci
        rw [hk'] at hk; cases hk; exact hrd
      | _ => simp [hfound, hslice?]

/-- `nat?` reads inside the array. -/
theorem nat?_idx {a : Array Word} {i k : Nat} (h : nat? (aread a) i = some k) : i < a.size := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, -⟩ := h
  exact (Array.getElem?_eq_some_iff.mp hw).1

/-- An `indInfo` record's word `p + 16` (its `all` slice's length) is read. -/
theorem decCI_indInfo_bound {a : Nat → Option Word} {p : Nat}
    {cv : IConstantVal} {caps : IIndCaps} (h : decCI a p = some (.indInfo cv caps)) :
    ∃ v, a (p + 16) = some v := by
  obtain ⟨cv', caps', he, hcaps⟩ := decCI_kind3 h (decCI_indInfo_kind h)
  simp only [decCaps, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hcaps
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, vall, hvall, _, _, _, _, -⟩ := hcaps
  obtain ⟨o, l, ho, hl, hs⟩ := hlist?_some hvall
  simp only [nat?, Option.map_eq_some_iff] at hl
  obtain ⟨w, hw, -⟩ := hl
  exact ⟨w, by rw [show p + 16 = p + 5 + 10 + 1 by omega]; exact hw⟩

/-! ## `nest_ctor_entry_strip`, `nest_ctor_entry` -/

/-! ### Reading `EREC` records at a word index -/

theorem erec_rd {m : Mem} {w : Word} {c : Nat} {v : Word} (h : erecP m (w.toNat + c) = some v)
    (hc : c < 2 ^ 64) : erRd m (w + UInt64.ofNat c) = v := by
  have hlt := erecP_lt64 h
  have e : (w + UInt64.ofNat c).toNat = w.toNat + c := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hc]; exact Nat.mod_eq_of_lt (by omega)
  exact (erRd_of_erecP (by rw [e]; exact h)).1

theorem decCV_type {a : Nat → Option Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    hd? a (q + 3) = some cv.type := by
  simp only [decCV, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, hd, hq⟩ := h
  rw [← Option.some.inj hq]; exact hd

/-! ### `viewConst` against `view` -/

theorem ETables.getConst_of_get (t : ETables) (i : EIdx) (ht : i.tag = ETag.const) (n : NIdx) (us : LsIdx)
    (h : t.get i = some (.const n us)) : t.getConst i = some (n, us) := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const] at h
  simp only [ETables.getConst]
  revert h
  cases t.consts.node? i.idxNat <;> simp_all [ETag.const]

theorem EStore.viewConst_of_view (st : EStore) (i : EIdx) (ht : i.tag = ETag.const) (n : NIdx)
    (us : LsIdx) (h : st.view i = some (.const n us)) : st.viewConst i = some (n, us) := by
  unfold EStore.view at h
  unfold EStore.viewConst EStore.persGetConst
  split at h
  · rename_i hp; rw [ite_eq_left hp]; exact ETables.getConst_of_get _ _ ht n us h
  · rename_i hp; rw [ite_eq_right hp]
    split at h
    · rename_i hs; rw [ite_eq_left hs]; exact ETables.getConst_of_get _ _ ht n us h
    · simp at h

/-! ### `nest_ctor_entry` -/

theorem ETables.get_const (t : ETables) (i : EIdx) (ht : i.tag = ETag.const) (v : ENodeView)
    (h : t.get i = some v) : ∃ n us, v = .const n us := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const] at h
  cases hn : t.consts.node? i.idxNat with
  | none => simp [hn] at h
  | some x => simp [hn] at h; exact ⟨_, _, h.symm⟩

theorem EStore.view_const (st : EStore) (i : EIdx) (ht : i.tag = ETag.const) (v : ENodeView)
    (h : st.view i = some v) : ∃ n us, v = .const n us := by
  unfold EStore.view at h
  split at h
  · exact ETables.get_const _ _ ht v h
  · split at h
    · exact ETables.get_const _ _ ht v h
    · simp at h

/-! ## `nest_res_head` -/

/-! ## `inst_pis_with` -/

mutual
def instW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, ao, al, e =>
    if al = 0 then some ([1, e], m)
    else if tagW e ≠ 6 then some ([0, 0], m)
    else instK1 n m ao al (eViewW m e)
def instK1 (n : Nat) (m : Mem) (ao al : Word) (v : List Word) : Option (List Word × Mem) :=
  if v = [] then none
  else instK2 n ao al
    (i1F m [CWF, v.tail.tail.headD 0, rdW (m.arr64 IW) ao, 0])
def instK2 (n : Nat) (ao al : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m1) => instK3 (instW n m1 (ao + 1) (al - 1) (rb.headD 0))
def instK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0, r.tail.headD 0], m2)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (ao al e : Word) (v rb r : List Word)
theorem instW_nil (h : al = 0) : instW (n + 1) m ao al e = some ([1, e], m) := by simp [instW, h]
theorem instW_nopi (h : al ≠ 0) (h2 : tagW e ≠ 6) : instW (n + 1) m ao al e = some ([0, 0], m) := by
  simp [instW, h, h2]
theorem instW_pi (h : al ≠ 0) (h2 : ¬ tagW e ≠ 6) :
    instW (n + 1) m ao al e = instK1 n m ao al (eViewW m e) := by simp only [instW]; rw [ite_eq_right h, ite_eq_right h2]
theorem instK1_ok (h : v ≠ []) : instK1 n m ao al v = instK2 n ao al
    (i1F m [CWF, v.tail.tail.headD 0, rdW (m.arr64 IW) ao, 0]) := by simp [instK1, h]
theorem instK2_some : instK2 n ao al (some (rb, m1)) = instK3 (instW n m1 (ao + 1) (al - 1) (rb.headD 0)) := by rw [instK2]
theorem instK3_some : instK3 (some (r, m2)) = some ([r.headD 0, r.tail.headD 0], m2) := by rw [instK3]
end arms
grind_pattern [ind_grind] instW_nil => instW (n + 1) m ao al e
grind_pattern [ind_grind] instW_nopi => instW (n + 1) m ao al e
grind_pattern [ind_grind] instW_pi => instW (n + 1) m ao al e
grind_pattern [ind_grind] instK1_ok => instK1 n m ao al v
grind_pattern [ind_grind] instK2_some => instK2 n ao al (some (rb, m1))
grind_pattern [ind_grind] instK3_some => instK3 (some (r, m2))

theorem instPisWith_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "inst_pis_with" = some instPisWith) (hi1 : I1Prog p) (n : Nat) :
    ∀ (s₀ : St) (ao al e : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_pis_with" [ao, al, e]
    ⦃fun r s' => LocEq s' s₀ ∧ instW n s₀.mem ao al e = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ ao al e
    rw [invoke_eq _ hp]; simp only [callFn, instPisWith]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ao al e
    simp only [invoke_eq _ hp, callFn, instPisWith]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        eView_spec p hv n, i1F_spec p hi1 n, ih] <;> finish (gen := 20)

theorem ETables.get_forall (t : ETables) (i : EIdx) (ht : i.tag = ETag.forallE) (v : ENodeView)
    (h : t.get i = some v) : ∃ ty b, v = .forallE ty b := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
    ETag.forallE] at h
  cases hn : t.foralls.node? i.idxNat with
  | none => simp [hn] at h
  | some x => simp [hn] at h; exact ⟨_, _, h.symm⟩

theorem EStore.view_forall (st : EStore) (i : EIdx) (ht : i.tag = ETag.forallE) (v : ENodeView)
    (h : st.view i = some v) : ∃ ty b, v = .forallE ty b := by
  unfold EStore.view at h
  split at h
  · exact ETables.get_forall _ _ ht v h
  · split at h
    · exact ETables.get_forall _ _ ht v h
    · simp at h

theorem ETables.getBind_of_get (t : ETables) (i : EIdx) (ht : i.tag = ETag.forallE) (ty b : EIdx)
    (h : t.get i = some (.forallE ty b)) : t.getBind i = some (ty, b) := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
    ETag.forallE] at h
  simp only [ETables.getBind, ht, ETag.lam, ETag.forallE]
  cases hn : t.foralls.node? i.idxNat with
  | none => simp [hn] at h
  | some x => simp [hn] at h ⊢; simp [ETag.forallE] at *; exact h

theorem EStore.viewBind_of_view (st : EStore) (i : EIdx) (ht : i.tag = ETag.forallE) (ty b : EIdx)
    (h : st.view i = some (.forallE ty b)) : st.viewBind i = some (ty, b) := by
  unfold EStore.view at h
  unfold EStore.viewBind EStore.persGetBind
  split at h
  · rename_i hp; rw [ite_eq_left hp]; exact ETables.getBind_of_get _ _ ht ty b h
  · rename_i hp; rw [ite_eq_right hp]
    split at h
    · rename_i hs; rw [ite_eq_left hs]; exact ETables.getBind_of_get _ _ ht ty b h
    · simp at h

/-- `inst_pis_with` keeps the `abstract1` memo. -/
theorem instW_afr (n : Nat) : ∀ (m m' : Mem) (ao al e : Word) (r : List Word), instW n m ao al e = some (r, m') →
    AFr m m' := by
  induction n with
  | zero => intro m m' ao al e r h; simp [instW] at h
  | succ n ih =>
    intro m m' ao al e r h
    simp only [instW, instK1, instK2.eq_def, instK3.eq_def] at h
    afr_auto h [i1F_afr, ih _ _ _ _ _ _]

/-! ## `close_telescope` -/

mutual
def closeW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, dO, dl, i, body =>
    if dl = 0 then some ([body], m)
    else closeK1 dO i (closeW n m (dO + 1) (dl - 1) (i + 1) body)
def closeK1 (dO i : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => closeK2 dO (abF m1 [CWF, r1.headD 0, i, 0])
def closeK2 (dO : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => closeK3 (mkForallW m2 (rdW (m2.arr64 IW) dO) (r2.headD 0))
def closeK3 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => if 4294967296 ≤ r then none else some ([r], m3)
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (dO dl i body r : Word) (r1 r2 : List Word)
theorem closeW_nil (h : dl = 0) : closeW (n + 1) m dO dl i body = some ([body], m) := by simp [closeW, h]
theorem closeW_cons (h : dl ≠ 0) : closeW (n + 1) m dO dl i body =
    closeK1 dO i (closeW n m (dO + 1) (dl - 1) (i + 1) body) := by simp [closeW, h]
theorem closeK1_some : closeK1 dO i (some (r1, m1)) =
    closeK2 dO (abF m1 [CWF, r1.headD 0, i, 0]) := by rw [closeK1]
theorem closeK2_some : closeK2 dO (some (r2, m2)) =
    closeK3 (mkForallW m2 (rdW (m2.arr64 IW) dO) (r2.headD 0)) := by rw [closeK2]
theorem closeK3_big (h : 4294967296 ≤ r) : closeK3 (some (r, m3)) = none := by simp [closeK3, h]
theorem closeK3_ok (h : ¬ 4294967296 ≤ r) : closeK3 (some (r, m3)) = some ([r], m3) := by simp [closeK3, h]
end arms
grind_pattern [ind_grind] closeW_nil => closeW (n + 1) m dO dl i body
grind_pattern [ind_grind] closeW_cons => closeW (n + 1) m dO dl i body
grind_pattern [ind_grind] closeK1_some => closeK1 dO i (some (r1, m1))
grind_pattern [ind_grind] closeK2_some => closeK2 dO (some (r2, m2))
grind_pattern [ind_grind] closeK3_big => closeK3 (some (r, m3))
grind_pattern [ind_grind] closeK3_ok => closeK3 (some (r, m3))

section spec
variable (p : Prog) (hd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "forall_find" = some forallFind)
  (hpp : p.lookup "forall_push" = some forallPush) (hpi : p.lookup "intern_forall" = some internForallL)
  (hmk : p.lookup "mk_forall" = some mkForall)
  (hp : p.lookup "close_telescope" = some closeTelescope) (hab : AbF p)
include hd hpf hpp hpi hmk hp hab

theorem closeTelescope_spec (n : Nat) : ∀ (s₀ : St) (dO dl i body : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "close_telescope" [dO, dl, i, body]
    ⦃fun r s' => LocEq s' s₀ ∧ closeW n s₀.mem dO dl i body = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ dO dl i body
    rw [invoke_eq _ hp]; simp only [callFn, closeTelescope]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ dO dl i body
    simp only [invoke_eq _ hp, callFn, closeTelescope]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        abF_spec p hab n, mkForall_spec p hd hpf hpp hpi hmk n, ih] <;>
      finish (gen := 20)

end spec

theorem closeW_ok (n : Nat) : ∀ (_dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (dO dl i body : Word) (ds : List EIdx) (r : List Word),
    closeW n m dO dl i body = some (r, m') → StageR vis fe m a → H body →
    decHL m dO.toNat dl.toNat = some ds → dO.toNat + dl.toNat < 2 ^ 64 →
    dO.toNat + dl.toNat ≤ iwTop m → i.toNat + dl.toNat < 2 ^ 64 → AbsOK m →
    ∃ x a', (ConRon.Arena.closeTelescope ds i.toNat (decI body)).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ decW0E m' r x ∧ AbsOK m' := by
  induction n with
  | zero => intro _dn fe vis m m' a dO dl i body ds r h; simp [closeW] at h
  | succ n ih =>
    intro _dn fe vis m m' a dO dl i body ds r h hS hbody hdec hb hit hib hA
    by_cases hdl : dl = 0
    · rw [closeW_nil n m dO dl i body hdl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : ds = [] := by
        have h0 : dl.toNat = 0 := by rw [hdl]; rfl
        rw [h0] at hdec; simpa [decHL, hslice?] using hdec.symm
      subst this
      exact ⟨decI body, a, rfl, hS, IWGrow.refl _, ⟨hbody, rfl⟩, hA⟩
    · have hl1 : dl.toNat = (dl.toNat - 1) + 1 := by have := L.toNat_ne_zero_of_ne _ hdl; omega
      rw [hl1, decHL, hslice?_succ] at hdec
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hdec
      obtain ⟨d, hdd, bs, hbs, rfl⟩ := hdec
      rw [closeW_cons n m dO dl i body hdl] at h
      have hdo1 : (dO + 1).toNat = dO.toNat + 1 := L.toNat_add_one_of_lt (by omega)
      have hdl1 : (dl - 1).toNat = dl.toNat - 1 := L.toNat_sub_one_of_ne hdl
      have hi1 : (i + 1).toNat = i.toNat + 1 := L.toNat_add_one_of_lt (by omega)
      rcases hr1 : closeW n m (dO + 1) (dl - 1) (i + 1) body with _ | ⟨r1, m1⟩ <;> rw [hr1] at h; · simp [closeK1] at h
      rw [closeK1_some] at h
      obtain ⟨x1, a1, hrun1, hS1, hg1, ⟨hlt1, hdec1⟩, hA1⟩ :=
        ih _dn fe vis m m1 a (dO + 1) (dl - 1) (i + 1) body bs r1 hr1 hS hbody
          (by rw [hdo1, hdl1]; exact hbs) (by rw [hdo1, hdl1]; omega) (by rw [hdo1, hdl1]; omega)
          (by rw [hi1, hdl1]; omega) hA
      rw [hi1] at hrun1
      rcases hr2 : abF m1 [CWF, r1.headD 0, i, 0] with _ | ⟨r2, m2⟩ <;> rw [hr2] at h; · simp [closeK2] at h
      rw [closeK2_some] at h
      obtain ⟨x2, a2, hrun2, ⟨hS2, hg2, hlt2, hdec2⟩, hA2⟩ :=
        abF_ok _dn vis fe (r1.headD 0) i 0 hlt1 m1 m2 a1 r2 hr2 ⟨hS1, hA1⟩
      rw [CWF_eq, hdec1, show (0 : Word).toNat = 0 from rfl] at hrun2
      have hg12 := hg1.trans hg2
      have hd0 : dO.toNat < iwTop m := by omega
      obtain ⟨wd, hwd_eq, hwd_lt, hwd_dec⟩ := iwH_rdW hdd (by omega)
      rw [UInt64.ofNat_toNat] at hwd_eq
      rw [rdW_iw_grow hg12 hd0, hwd_eq] at h
      rcases hm : mkForallW m2 wd (r2.headD 0) with _ | ⟨rr, m3⟩ <;> rw [hm] at h; · simp [closeK3] at h
      by_cases hbig : 4294967296 ≤ rr
      · rw [closeK3_big _ _ hbig] at h; simp at h
      · rw [closeK3_ok _ _ hbig] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨a3, hrun3, hS3, hg3⟩ := mkForall_stage hS2 wd (r2.headD 0) hm
        refine ⟨decE rr, a3, ?_, hS3, hg12.trans hg3, ⟨?_, rfl⟩, mkForallW_afr hm hA2⟩
        · simp only [ConRon.Arena.closeTelescope, StateT.run_bind]
          simp only [hrun1, except_ok_bind, hrun2, ← hwd_dec, ← hdec2]
          exact hrun3
        · have : rr.toNat < 2 ^ 32 := by
            have : ¬ (4294967296 : Nat) ≤ rr.toNat := hbig
            omega
          simpa using this

end L.Ind

end
