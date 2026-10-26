import ConAgua.Arena.DeclValRef
import ConAgua.Arena.IndDecStab

/-!
# Pin reads, `of_reduce_op`, `install_basis_decl(s)` (lane `decls3`)

* `pin_at(i)` as a word model (`pinAtW`) and its twin read (`pinAtW_ok`).
* `of_reduce_op(n)` refines `ofReduceOp` (pin reads only; sorry-free).
* `install_basis_decl(vis, c)` refines `installBasisDecl` (the duplicate check, the push) and
  `install_basis_decls(vis, o, l)` refines `installBasisDecls` (an `IW` slice of constant-record
  pointers), sorry-free.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-! ## `pin_at(i)` -/

/-- **The model of `pin_at(i)`**: the flag, the slot bound, the slot. -/
def pinAtW (m : Mem) (i : Word) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else if 51 ≤ i then none else some ([rdW (m.arr64 PINS) (1 + i)], m)

theorem pinAt_specW (p : Prog) (hp : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St)
    (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_at" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ pinAtW s₀.mem i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, pinAtL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [pinAtW, pinW_eq, rdW_eq]

/-- **A pin read is the twin's** (`pinAt`), the memory unchanged. -/
theorem pinAtW_ok {m m' : Mem} {a : AState} {i : Word} {r : List Word}
    (h : pinAtW m i = some (r, m')) (hP : PinsR m a.pins) :
    m' = m ∧ r = [pinW m (1 + i.toNat)] ∧ (pinW m (1 + i.toNat)).toNat < 2 ^ 32 ∧
      (pinAt i.toNat).run a = .ok (decI (pinW m (1 + i.toNat)), a) := by
  unfold pinAtW at h
  by_cases h0 : pinW m 0 = 0
  · simp [h0] at h
  rw [ite_eq_right h0] at h
  by_cases hi : 51 ≤ i
  · simp [hi] at h
  rw [ite_eq_right hi] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hF := hP.full h0
  have hi' : i.toNat < 51 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hi); simpa using this
  have e : rdW (m.arr64 PINS) (1 + i) = pinW m (1 + i.toNat) := by
    simp only [rdW, pinW]
    congr 2
    rw [UInt64.toNat_add]; simp; omega
  rw [e]
  exact ⟨rfl, rfl, hF.names_lt i.toNat hi', pinAt_run hF i.toNat hi'⟩

/-! ## `of_reduce_op(n)` -/

/-- After the `ofReduceNat` pin. -/
def oroK (n : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if n = r1.headD 0 then pinAtW m1 43 else pinAtW m1 44

/-- **The model of `of_reduce_op(n)`.** -/
def oroW (m : Mem) (n : Word) : Option (List Word × Mem) := oroK n (pinAtW m 45)

theorem oroK_some (n : Word) (r1 : List Word) (m1 : Mem) :
    oroK n (some (r1, m1)) = if n = r1.headD 0 then pinAtW m1 43 else pinAtW m1 44 := rfl

grind_pattern [ind_grind] oroK_some => oroK n (some (r1, m1))

theorem oro_specW (p : Prog) (hpa : p.lookup "pin_at" = some pinAtL)
    (hp : p.lookup "of_reduce_op" = some ofReduceOpL) (n : Nat) (s₀ : St) (w : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "of_reduce_op" [w]
    ⦃fun r s' => LocEq s' s₀ ∧ oroW s₀.mem w = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, ofReduceOpL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_specW p hpa n] <;>
      finish (gen := 20) [oroW, pinAtW]

theorem oroW_ok {m m' : Mem} {a : AState} {w : Word} {r : List Word}
    (h : oroW m w = some (r, m')) (hP : PinsR m a.pins) (hw : w.toNat < 2 ^ 32) :
    m' = m ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      (ofReduceOp (decI w)).run a = .ok (decI (r.headD 0), a) := by
  unfold oroW at h
  cases h1 : pinAtW m 45 with
  | none => rw [h1] at h; cases h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, oroK_some] at h
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok h1 hP
  have hbeq : ((decI w : NIdx) == decI (pinW m (1 + (45 : Word).toNat))) =
      decide (w = pinW m (1 + (45 : Word).toNat)) := decI_beq w _ hw hl1
  have e1 : r1.headD 0 = pinW m (1 + (45 : Word).toNat) := by rw [hr1]; rfl
  by_cases he : w = r1.headD 0
  · rw [ite_eq_left he, hm1] at h
    obtain ⟨hm, hr, hl, hrun⟩ := pinAtW_ok h hP
    subst hr
    rw [e1] at he
    refine ⟨hm, hl, ?_⟩
    simp only [ofReduceOp, ofReduceNatName, pinOfReduceNat, reduceNatName, pinReduceNat,
      StateT.run_bind, show PIN_OF_REDUCE_NAT = (45 : Word).toNat from rfl, hrun1, exc_ok_bind', he]
    simpa [PIN_REDUCE_NAT, PIN_REDUCE_BOOL] using hrun
  · rw [ite_eq_right he, hm1] at h
    obtain ⟨hm, hr, hl, hrun⟩ := pinAtW_ok h hP
    subst hr
    rw [e1] at he
    refine ⟨hm, hl, ?_⟩
    simp only [ofReduceOp, ofReduceNatName, pinOfReduceNat, reduceBoolName, pinReduceBool,
      StateT.run_bind, show PIN_OF_REDUCE_NAT = (45 : Word).toNat from rfl, hrun1, exc_ok_bind',
      hbeq, he, decide_false, Bool.false_eq_true, ite_false]
    simpa [PIN_REDUCE_NAT, PIN_REDUCE_BOOL] using hrun

local notation "V" => ConLeche.CheckMode.verified

/-- **`of_reduce_op(n)` refines `ofReduceOp`** (pin reads; the memory unchanged). -/
@[refines ConRon.Arena.ofReduceOp]
theorem ofReduceOp_refines (p : Prog) (hpa : p.lookup "pin_at" = some pinAtL)
    (hp : p.lookup "of_reduce_op" = some ofReduceOpL) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis w : Word)
    (hS : StageR dn vis fe s₀.mem a₀) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "of_reduce_op" [w]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ofReduceOp (decI w)) a₀ ∧
      KeepPost dn vis fe decW0N s₀.mem s'.mem (AM.st (ofReduceOp (decI w)) a₀) r
        (AM.res (ofReduceOp (decI w)) a₀); ⊤⦄ := by
  refine triple_post (oro_specW p hpa hp n s₀ w) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hmem, hrl, hrun⟩ := oroW_ok hm hS.1.pins hw
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hl, hok, ?_, ?_, hrl, by rw [hres]⟩
  · rw [hst, hmem]; exact hS
  · rw [hmem]; exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## `install_basis_decl(vis, c)` and `install_basis_decls(vis, o, l)` -/

/-- The lookups the basis install needs. -/
structure BasisProg (p : Prog) : Prop where
  ibd : p.lookup "install_basis_decl" = some installBasisDeclL
  ibds : p.lookup "install_basis_decls" = some installBasisDeclsL
  ih : IhProg p
  rcp : RecProg p

section models
variable (p : Prog)

/-- After the push. -/
def ibdK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => some ([r2.headD 0], m2)

/-- After the lookup: a hit aborts. -/
def ibdK1 (n : Nat) (vis c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if r1.headD 0 ≠ 0 then none else ibdK2 (callW p n "env_push" [vis, c] m1)

/-- **The model of `install_basis_decl(vis, c)`.** -/
def ibdW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, c => ibdK1 p n vis c (envFindW m (rdW (m.arr64 EREC) (c + 1)) vis)

section arms
variable (n : Nat) (m m1 m2 : Mem) (vis c : Word) (r1 r2 : List Word)
theorem ibdW_step : ibdW p (n + 1) m vis c =
    ibdK1 p n vis c (envFindW m (rdW (m.arr64 EREC) (c + 1)) vis) := rfl
theorem ibdK1_some : ibdK1 p n vis c (some (r1, m1)) =
    if r1.headD 0 ≠ 0 then none else ibdK2 (callW p n "env_push" [vis, c] m1) := rfl
theorem ibdK2_some : ibdK2 (some (r2, m2)) = some ([r2.headD 0], m2) := rfl
end arms

grind_pattern [ind_grind] ibdW_step => ibdW p (n + 1) m vis c
grind_pattern [ind_grind] ibdK1_some => ibdK1 p n vis c (some (r1, m1))
grind_pattern [ind_grind] ibdK2_some => ibdK2 (some (r2, m2))

theorem ibd_specW (h : BasisProg p) (n : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_basis_decl" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ ibdW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.ibd]
  simp only [callFn, installBasisDeclL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        envFind_specW p h.ih.ix h.ih.rowGet h.ih.find n, callW_spec p n "env_push"] <;>
      finish (gen := 20) [rdW_eq]

/-- After the head's install: the rest, through `callW` (the recursion). -/
def ibdsK1 (n : Nat) (o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    match callW p n "install_basis_decls" [r1.headD 0, o + 1, l - 1] m1 with
    | none => none
    | some (r2, m2) => some ([r2.headD 0], m2)

/-- **The model of `install_basis_decls(vis, o, l)`.** -/
def ibdsW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, vis, o, l =>
    if l = 0 then some ([vis], m)
    else ibdsK1 p n o l (callW p n "install_basis_decl" [vis, rdW (m.arr64 IW) o] m)

theorem ibdsW_step (n : Nat) (m : Mem) (vis o l : Word) : ibdsW p (n + 1) m vis o l =
    if l = 0 then some ([vis], m)
    else ibdsK1 p n o l (callW p n "install_basis_decl" [vis, rdW (m.arr64 IW) o] m) := rfl
theorem ibdsK1_some (n : Nat) (o l : Word) (r1 : List Word) (m1 : Mem) :
    ibdsK1 p n o l (some (r1, m1)) =
      match callW p n "install_basis_decls" [r1.headD 0, o + 1, l - 1] m1 with
      | none => none
      | some (r2, m2) => some ([r2.headD 0], m2) := rfl

grind_pattern [ind_grind] ibdsW_step => ibdsW p (n + 1) m vis o l
grind_pattern [ind_grind] ibdsK1_some => ibdsK1 p n o l (some (r1, m1))

theorem ibds_specW (h : BasisProg p) (n : Nat) (s₀ : St) (vis o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_basis_decls" [vis, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ibdsW p n s₀.mem vis o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.ibds]
  simp only [callFn, installBasisDeclsL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "install_basis_decl", callW_spec p n "install_basis_decls"] <;>
      finish (gen := 20) [rdW_eq]

end models

/-! ### The relational lemmas -/

/-- The cut record pool is the record pool below its top. -/
theorem truncM_erecP (m : Mem) : ArrExt (erA (truncM m)) (erecP m) := by
  intro i v h
  obtain ⟨hi, hv⟩ := truncM_er_get h
  rw [erecP_getE hi]; exact hv

/-- **`install_basis_decl` refines `installBasisDecl`** at the model level. -/
theorem ibdW_ok {p : Prog} (hRp : RecProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {c : Word} {r : List Word}
    {ci : IConstantInfo} (h : ibdW p n m vis c = some (r, m')) (hS : StageR dn vis fe m a)
    (hci : decCI (erecP m) dn c.toNat = some ci) :
    (installBasisDecl fe ci).run a = .ok (fe.push ci, a) ∧ StageR dn (r.headD 0) (fe.push ci) m' a ∧
      IWGrow m m' := by
  obtain ⟨w, hw1, hwl, hname⟩ := decCI_name hci
  have hcb : c.toNat + 1 < 2 ^ 64 := erecP_bound hw1 hS.2
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 hcb
  have ew : rdW (m.arr64 EREC) (c + 1) = w := rdW_of_get? hc1.symm (erecP_get hw1)
  cases n with
  | zero => simp [ibdW] at h
  | succ n =>
  rw [ibdW_step, ew] at h
  cases h1 : envFindW m w vis with
  | none => rw [h1] at h; simp [ibdK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, ibdK1_some] at h
  by_cases hb : r1.headD 0 ≠ 0
  · rw [ite_eq_left hb] at h; cases h
  rw [ite_eq_right hb] at h
  obtain ⟨rfl, hfind⟩ := envFindW_miss h1 hS.1.env hwl (by simpa using hb)
  have hw : (rdW (m1.arr64 EREC) (c + 1)).toNat < 2 ^ 32 := by rw [ew]; exact hwl
  cases h2 : callW p n "env_push" [vis, c] m1 with
  | none => rw [h2] at h; simp [ibdK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, ibdK2_some] at h
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (envPush_specW p hRp n ⟨m1, Locals.init []⟩ vis c hw) h2
  subst hs2
  obtain ⟨hS2, hg2⟩ := envPushW_ok hW2 hS hci
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by simpa using hS2, hg2⟩
  simp [installBasisDecl, hname, hfind, StateT.run_pure]
  rfl

/-- The basis list's decoding: an `IW` slice of constant-record pointers. -/
def basisDec (dn : NIdx → Option ConLeche.Name) (o l : Nat) (m : Mem) :
    Option (List IConstantInfo) :=
  decPL m (fun q => decCI (erA m) dn q) o l

theorem basisDec_mono (dn : NIdx → Option ConLeche.Name) (o l : Nat) :
    OMono (basisDec dn o l) :=
  OMono.decPL (f := fun m q => decCI (erA m) dn q) (fun _ => ⟨fun _ _ _ he h => he.2.decCI h⟩) o l

/-- **`install_basis_decls` refines `installBasisDecls`** at the run level, by induction on the
fuel (the recursion through `callW`). -/
theorem ibds_rel {p : Prog} (hp : BasisProg p) (dn : NIdx → Option ConLeche.Name) :
    ∀ (n : Nat) (m m' : Mem) (vis : Word) (fe : IFEnv) (a : AState) (o l : Word) (r : List Word)
      (cis : List IConstantInfo),
      callW p n "install_basis_decls" [vis, o, l] m = some (r, m') → StageR dn vis fe m a →
      DecB (basisDec dn o.toNat l.toNat) m cis →
      ∃ fe' a', (installBasisDecls fe cis).run a = .ok (fe', a') ∧
        StageR dn (r.headD 0) fe' m' a' ∧ IWGrow m m' := by
  intro n
  induction n with
  | zero => intro m m' vis fe a o l r cis h; simp [callW_zero] at h
  | succ n ih =>
  intro m m' vis fe a o l r cis h hS hD
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ibds_specW p hp (n + 1) ⟨m, Locals.init []⟩ vis o l) h
  subst hs'
  rw [ibdsW_step] at hW
  by_cases hl : l = 0
  · rw [ite_eq_left hl] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, hm⟩ := hW
    subst hl
    have : cis = [] := by
      simpa [DecB, basisDec, decPL] using hD.symm
    subst this
    rw [← hm]
    exact ⟨fe, a, rfl, by simpa using hS, IWGrow.refl _⟩
  rw [ite_eq_right hl] at hW
  -- the head
  obtain ⟨k, hk⟩ : ∃ k, l.toNat = k + 1 := ⟨l.toNat - 1, by
    have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hD' : basisDec dn o.toNat (k + 1) (truncM m) = some cis := by rw [← hk]; exact hD
  cases cis with
  | nil => have := decPL_length (truncM m) hD'; simp at this
  | cons ci cs =>
  obtain ⟨v, hv, hci⟩ := decPL_head hD'
  have hext := (IWGrow.refl m).truncExt
  have hvm : iwN m o.toNat = some v := hext.1.nat? hv
  have hci' : decCI (erecP m) dn v = some ci := ArrExt.decCI (truncM_erecP m) hci
  obtain ⟨w0, hw0, rfl⟩ : ∃ w0, (iwA m)[o.toNat]? = some w0 ∧ w0.toNat = v := by
    simp only [iwN, nat?, Option.map_eq_some_iff] at hvm; exact hvm
  have ew : rdW (m.arr64 IW) o = w0 := by simp [rdW, iwA] at hw0 ⊢; simp [hw0]
  rw [ew] at hW
  cases h1 : callW p n "install_basis_decl" [vis, w0] m with
  | none => rw [h1] at hW; simp [ibdsK1] at hW
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, ibdsK1_some] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ibd_specW p hp n ⟨m, Locals.init []⟩ vis w0) h1
  subst hs1
  obtain ⟨hrun1, hS1, hg1⟩ := ibdW_ok hp.rcp hW1 hS hci'
  -- the rest
  cases h2 : callW p n "install_basis_decls" [r1.headD 0, o + 1, l - 1] s1.mem with
  | none => rw [h2] at hW; simp at hW
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm2⟩ := hW
  subst hr
  rw [← hm2]
  have hob : o.toNat + 1 < 2 ^ 64 := by
    have := (Array.getElem?_eq_some_iff.mp hw0).1
    have := hS.2.2.2.1; simp only [iwA] at *; omega
  have ho1 : (o + 1).toNat = o.toNat + 1 := toNat_add_small o 1 hob
  have hl1 : (l - 1).toNat = k := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  have hDt : DecB (basisDec dn (o + 1).toNat (l - 1).toNat) m cs := by
    rw [ho1, hl1]; exact decPL_tail hD'
  obtain ⟨fe', a', hrun2, hS2, hg2⟩ :=
    ih s1.mem m2 (r1.headD 0) (fe.push ci) a (o + 1) (l - 1) r2 cs h2 hS1
      (DecB.grow (basisDec_mono dn _ _) hg1 hDt)
  refine ⟨fe', a', ?_, by simpa using hS2, hg1.trans hg2⟩
  simp only [installBasisDecls, StateT.run_bind, hrun1, exc_ok_bind']
  exact hrun2

local notation "V" => ConLeche.CheckMode.verified

/-- **`install_basis_decl(vis, c)` refines `installBasisDecl`** (sorry-free). -/
@[refines ConRon.Arena.installBasisDecl]
theorem installBasisDecl_refines (p : Prog) (hp : BasisProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis c : Word) (ci : IConstantInfo)
    (hS : StageR dn vis fe s₀.mem a₀) (hci : decCI (erecP s₀.mem) dn c.toNat = some ci) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_basis_decl" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installBasisDecl fe ci) a₀ ∧
      StageR dn (r.headD 0) (AM.res (installBasisDecl fe ci) a₀) s'.mem
        (AM.st (installBasisDecl fe ci) a₀) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (ibd_specW p hp n s₀ vis c) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hrun, hS', hg⟩ := ibdW_ok hp.rcp hm hS hci
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hS', hg⟩

/-- **`install_basis_decls(vis, o, l)` refines `installBasisDecls`** (an `IW` slice of
constant-record pointers decoded below the tops; sorry-free). -/
@[refines ConRon.Arena.installBasisDecls]
theorem installBasisDecls_refines (p : Prog) (hp : BasisProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis o l : Word) (cis : List IConstantInfo)
    (hS : StageR dn vis fe s₀.mem a₀) (hD : DecB (basisDec dn o.toNat l.toNat) s₀.mem cis) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_basis_decls" [vis, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installBasisDecls fe cis) a₀ ∧
      StageR dn (r.headD 0) (AM.res (installBasisDecls fe cis) a₀) s'.mem
        (AM.st (installBasisDecls fe cis) a₀) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (callW_spec p n "install_basis_decls" [vis, o, l] s₀) ?_
  rintro r s' ⟨hl, hc⟩
  obtain ⟨fe', a', hrun, hS', hg⟩ := ibds_rel hp dn n s₀.mem s'.mem vis fe a₀ o l r cis hc hS hD
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hS', hg⟩

end L.Arena
