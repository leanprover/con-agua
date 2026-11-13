module

public import ConAgua.Arena.IndRealAbs
public import ConAgua.Arena.IndRealAr
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Arena.IndPos
import ConAgua.L.WordOff
import ConAgua.L.ModelGen
import ConAgua.Arena.IndDecStab
import all ConAgua.Arena.Abs1
import all ConAgua.Arena.AppStore
import all ConAgua.Arena.ArRange
import all ConAgua.Arena.ArRangeSpec
import all ConAgua.Arena.BVarStore
import all ConAgua.Arena.BvarB
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.FVarRange
import all ConAgua.Arena.ForallStore
import all ConAgua.Arena.LamStore
import all ConAgua.Arena.LetStore
import all ConAgua.Arena.LiftL
import all ConAgua.Arena.MemoLib
import all ConAgua.Arena.ProjStore
import all ConAgua.Arena.Walk

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
  sorry

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
  obtain ⟨_, _, _, _, vall, hvall, _, _, _, _, -⟩ := hcaps
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

/-- The two closer functions. -/
def ctHead : Prog := [("close_telescope", closeTelescope), ("close_telescope_go", closeTelescopeGo)]

/-- The closers and `ar_entry`'s program (the store's `mk_forall` among it). -/
def ctP : Prog := ctHead ++ arProg

/-- The functions `close_telescope` reaches. -/
def ctFns : List FnName := ["close_telescope", "close_telescope_go"] ++ arFns

theorem ctP_closed : closedA ctP absA absC ctFns = true := by decide +kernel

/-- The program bundle. -/
abbrev CtF (p : Prog) : Prop := ProgHas p ctP

theorem CtF.ar {p : Prog} (hp : CtF p) : ArF p := ProgHas.right (l₁ := ctHead) hp

/-- **`close_telescope_go` is its model `ctgW`** (generated). -/
l_model ctgW_spec (p : Prog) (hp : CtF p)
  fns [hp.get "close_telescope_go" ↦ ctgW list]
  specs [arF_spec p (CtF.ar hp) n,
    mkForall_spec p (hp.get "der_b") (hp.get "forall_find") (hp.get "forall_push")
      (hp.get "intern_forall") (hp.get "mk_forall") n]
  grind [ind_grind] finish [rdW_eq]

/-- **`close_telescope` is its model `closeW`** (generated). -/
l_model closeW_spec (p : Prog) (hp : CtF p)
  fns [hp.get "close_telescope" ↦ closeW list]
  specs [ctgW_spec p hp n]
  grind [ind_grind]

/-- **The model of `close_telescope`** (program- and fuel-free). -/
noncomputable def closeF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF ctP "close_telescope" m args

theorem closeTelescope_spec (p : Prog) (hp : CtF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "close_telescope" args
    ⦃fun r s' => LocEq s' s₀ ∧ closeF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec ctP_closed (hp.agree ctFns) (by decide) n s₀ args

/-- `close_telescope` writes only `ar_entry`'s `absA`, `absC`. -/
theorem closeF_frame {m m' : Mem} {args r : List Word} (h : closeF m args = some (r, m')) :
    MemFrame absA absC m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame ctP_closed (by decide) (run_of_callW hc)).1

/-- A model run is `closeW` at some fuel. -/
theorem closeF_W {m m' : Mem} {dO dl i body : Word} {r : List Word}
    (h : closeF m [dO, dl, i, body] = some (r, m')) : ∃ n, closeW n m dO dl i body = some (r, m') := by
  obtain ⟨n, hc⟩ := callF_run h
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (closeW_spec ctP (ProgHas.refl _) n _ dO dl i body) hc
  rw [hs'] at hW
  exact ⟨n, hW⟩

theorem decHL_cons_rT {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL m o (l + 1) = some xs) :
    ∃ x ys, xs = x :: ys ∧ decHL m (o + 1) l = some ys ∧ iwH m o = some x := by
  simp only [decHL, hslice?_succ] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨x, hx, ys, hxs, rfl⟩ := h
  exact ⟨x, ys, rfl, hxs, hx⟩

theorem ctgW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (i k dO dl body : Word) (ds : List EIdx) (r : List Word),
    ctgW n m i k dO dl body = some (r, m') → StageR vis fe m a → H body →
    decHL m dO.toNat dl.toNat = some ds → dO.toNat + dl.toNat < 2 ^ 64 →
    dO.toNat + dl.toNat ≤ iwTop m → k.toNat + dl.toNat < 2 ^ 64 → AbsOK m →
    ∃ x a', (ConRon.Arena.closeTelescopeGo i.toNat k.toNat ds (decI body)).run a = .ok (x, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0E m' r x ∧ AbsOK m' := by
  induction n with
  | zero => intro m m' a i k dO dl body ds r h; simp [ctgW] at h
  | succ n ih =>
    intro m m' a i k dO dl body ds r h hS hb hds hdo hdt hkl hA
    by_cases hdl : dl = 0
    · rw [ctgW.arm1 n m i k dO dl body hdl] at h
      have hl0 : dl.toNat = 0 := by rw [hdl]; rfl
      rw [hl0] at hds
      simp [decHL, hslice?] at hds
      subst hds
      obtain ⟨⟨ra, m1⟩, ha, h⟩ := of_K h rfl
      rw [ctgW.k_ar_entry.arm1] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨x, a1, hrun, hpost, hA1⟩ := arF_ok dn vis fe body i k 0 hb m m1 a ra ha ⟨hS, hA⟩
      exact ⟨x, a1, by simpa [ConRon.Arena.closeTelescopeGo, CWF_eq] using hrun, hpost.1, hpost.2.1,
        by simpa [decW0E] using hpost.2.2, hA1⟩
    · rw [ctgW.arm2 n m i k dO dl body hdl] at h
      obtain ⟨l1, hl1, hdl1⟩ := L.exists_toNat_eq_succ hdl
      rw [hl1] at hds
      obtain ⟨dom, rest, rfl, hrest, hdom⟩ := decHL_cons_rT hds
      have hdO1 : (dO + 1).toNat = dO.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      obtain ⟨w, hw1, hw2, hw3⟩ := iwH_rdW hdom (by omega)
      rw [UInt64.ofNat_toNat] at hw1
      rw [hw1] at h
      obtain ⟨⟨ra, m1⟩, ha, h⟩ := of_K h (ctgW.k_ar_entry_2.none ..)
      obtain ⟨x1, a1, hrun1, ⟨hS1, hg1, hd11, hd12⟩, hA1⟩ := arF_ok dn vis fe w i k 0 hw2 m m1 a ra ha ⟨hS, hA⟩
      rw [ctgW.k_ar_entry_2.arm1] at h
      obtain ⟨⟨rb, m2⟩, hr, h⟩ := of_K h (ctgW.k_close_telescope_go.none ..)
      rw [ctgW.k_close_telescope_go.arm1] at h
      obtain ⟨x2, a2, hrun2, hS2, hg2, ⟨hd21, hd22⟩, hA2⟩ := ih m1 m2 a1 i (k + 1) (dO + 1) (dl - 1) body rest rb hr
        hS1 hb (by rw [hdO1, hdl1]; exact decHL_grow' hg1 (by omega) hrest) (by omega)
        (by have := hg1.iw; omega) (by omega) hA1
      obtain ⟨⟨rc, m3⟩, hm, h⟩ := of_K h (ctgW.k_mk_forall.none ..)
      by_cases hbig : 4294967296 ≤ rc
      · rw [ctgW.k_mk_forall.abort1 rc m3 hbig] at h; cases h
      rw [ctgW.k_mk_forall.arm1 rc m3 hbig] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨a3, hrun3, hS3, hg3⟩ := mkForall_stage hS2 (ra.headD 0) (rb.headD 0) hm
      have hlt : rc.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ rc.toNat := hbig; omega
      refine ⟨decE rc, a3, ?_, hS3, (hg1.trans hg2).trans hg3, ⟨by simpa using hlt, by simp [decE_eq]⟩,
        mkForallW_afr hm hA2⟩
      rw [show (0 : Word).toNat = 0 from rfl] at hrun1
      rw [hk1] at hrun2
      simp only [ConRon.Arena.closeTelescopeGo, StateT.run_bind]
      rw [← hw3, show (decI w : EIdx) = decI w from rfl, hrun1]
      simp only [bind, Except.bind]
      rw [hrun2]
      simp only
      rw [← hd12, ← hd22]
      exact hrun3

theorem closeW_ok (_dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (dO dl i body : Word) (ds : List EIdx) (r : List Word) :
    closeF m [dO, dl, i, body] = some (r, m') → StageR vis fe m a → H body →
    decHL m dO.toNat dl.toNat = some ds → dO.toNat + dl.toNat < 2 ^ 64 →
    dO.toNat + dl.toNat ≤ iwTop m → i.toNat + dl.toNat < 2 ^ 64 → AbsOK m →
    ∃ x a', (ConRon.Arena.closeTelescope ds i.toNat (decI body)).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ decW0E m' r x ∧ AbsOK m' := by
  intro h hS hb hds hdo hdt _ hA
  obtain ⟨n, hW⟩ := closeF_W h
  cases n with
  | zero => simp [closeW] at hW
  | succ n =>
  rw [closeW.arm1] at hW
  obtain ⟨⟨rg, m1⟩, hg, hW⟩ := of_K hW rfl
  rw [closeW.k_close_telescope_go.arm1] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨x, a', hrun, hS', hg', hd, hA'⟩ :=
    ctgW_ok _dn fe vis n m m1 a i 0 dO dl body ds rg hg hS hb hds hdo hdt (by simp; omega) hA
  exact ⟨x, a', hrun, hS', hg', by simpa [decW0E] using hd, hA'⟩

end L.Ind

end
