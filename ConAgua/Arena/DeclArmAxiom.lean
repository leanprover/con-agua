import ConAgua.Arena.DeclArmQuot

/-!
# The axiom arm `check_decl_axiom(i, vis)` (lane `decls3`)

`checkDecl`'s `.axiomDecl` arm: `Quot.sound` against the pinned quotient block (installing
nothing; `ci_canon_eq` (helper `decls3-canon`'s `ciCanonEq_refines`, literals by handle: `LitInj`
from the twin state's `StateOK`, lane `decls4`)
it), else the constant check and the five recognised axioms (`std_axiom_ok`, `Lean.trustCompiler`,
the `ofReduce*` pair), `propext`/`choice` of another shape and every other axiom declining,
`sorryAx` skipped. Through the ROM stubs and the core's.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt CVAt dw)

section model
variable (p : Prog) (n : Nat) (vis : Word)

/-- After a push: its view. -/
def cdaRet : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

/-- A recognised axiom: abort unless its test passed, then the push. -/
def cdaT (c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else cdaRet (callW p n "env_push" [vis, c] m)

/-- After the `sorryAx` pin. -/
def cdaK10 (nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if nm = r.headD 0 then some ([vis], m) else none

/-- After the `choice` pin: `propext`/`choice` of another shape decline. -/
def cdaK9 (nm a : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if nm = a ∨ nm = r.headD 0 then none else cdaK10 vis nm (pinAtW m 13)

/-- After the `propext` pin. -/
def cdaK8 (nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cdaK9 vis nm (r.headD 0) (pinAtW m 33)

/-- After the `ofReduceBool` pin. -/
def cdaK7 (c nm a : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if nm = a ∨ nm = r.headD 0 then cdaT p n vis c (callW p n "of_reduce_ax_ok" [vis, c + 1] m)
    else cdaK8 vis nm (pinAtW m 32)

/-- After the `ofReduceNat` pin. -/
def cdaK6 (c nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cdaK7 p n vis c nm (r.headD 0) (pinAtW m 46)

/-- After the `trustCompiler` pin. -/
def cdaK5 (c nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if nm = r.headD 0 then cdaT p n vis c (callW p n "trust_compiler_ok" [vis, c + 1] m)
    else cdaK6 p n vis c nm (pinAtW m 45)

/-- After `std_axiom_ok`. -/
def cdaK4 (c nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then cdaRet (callW p n "env_push" [vis, c] m)
    else cdaK5 p n vis c nm (pinAtW m 42)

/-- After `check_constant_val`. -/
def cdaK3 (c nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => cdaK4 p n vis c nm (callW p n "std_axiom_ok" [vis, c + 1] m)

/-- `Quot.sound`: after `ci_canon_eq`. -/
def cdaQ2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else some ([vis], m)

/-- `Quot.sound`: after the block's read. -/
def cdaQ1 (c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.tail.headD 0 ≤ 4 then none
    else cdaQ2 vis (callW p n "ci_canon_eq" [c, rdW (m.arr64 IW) (r.headD 0 + 4)] m)

/-- After the `Quot.sound` pin. -/
def cdaK2 (c nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if nm = r.headD 0 then cdaQ1 p n vis c (callW p n "rom_basis_decls" [4] m)
    else cdaK3 p n vis c nm (callW p n "check_constant_val" [vis, c + 1] m)

/-- After `erec_ci`. -/
def cdaK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    cdaK2 p n vis (r.headD 0) (rdW (m.arr64 EREC) (r.headD 0 + 1)) (pinAtW m 4)

end model

/-- **The model of `check_decl_axiom(i, vis)`.** -/
def cdaW (p : Prog) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, i, vis => cdaK1 p n vis (erecCiW n m i 0)

section arms
variable (p : Prog) (n : Nat) (vis i c nm a : Word) (r : List Word) (m : Mem)
theorem cdaW_step : cdaW p (n + 1) m i vis = cdaK1 p n vis (erecCiW n m i 0) := rfl
theorem cdaK1_some : cdaK1 p n vis (some (r, m)) =
    cdaK2 p n vis (r.headD 0) (rdW (m.arr64 EREC) (r.headD 0 + 1)) (pinAtW m 4) := rfl
theorem cdaK2_some : cdaK2 p n vis c nm (some (r, m)) =
    if nm = r.headD 0 then cdaQ1 p n vis c (callW p n "rom_basis_decls" [4] m)
    else cdaK3 p n vis c nm (callW p n "check_constant_val" [vis, c + 1] m) := rfl
theorem cdaQ1_some : cdaQ1 p n vis c (some (r, m)) =
    if r.tail.headD 0 ≤ 4 then none
    else cdaQ2 vis (callW p n "ci_canon_eq" [c, rdW (m.arr64 IW) (r.headD 0 + 4)] m) := rfl
theorem cdaQ2_some : cdaQ2 vis (some (r, m)) = if r.headD 0 = 0 then none else some ([vis], m) :=
  rfl
theorem cdaK3_some : cdaK3 p n vis c nm (some (r, m)) =
    cdaK4 p n vis c nm (callW p n "std_axiom_ok" [vis, c + 1] m) := rfl
theorem cdaK4_some : cdaK4 p n vis c nm (some (r, m)) =
    if r.headD 0 ≠ 0 then cdaRet (callW p n "env_push" [vis, c] m)
    else cdaK5 p n vis c nm (pinAtW m 42) := rfl
theorem cdaK5_some : cdaK5 p n vis c nm (some (r, m)) =
    if nm = r.headD 0 then cdaT p n vis c (callW p n "trust_compiler_ok" [vis, c + 1] m)
    else cdaK6 p n vis c nm (pinAtW m 45) := rfl
theorem cdaK6_some : cdaK6 p n vis c nm (some (r, m)) =
    cdaK7 p n vis c nm (r.headD 0) (pinAtW m 46) := rfl
theorem cdaK7_some : cdaK7 p n vis c nm a (some (r, m)) =
    if nm = a ∨ nm = r.headD 0 then cdaT p n vis c (callW p n "of_reduce_ax_ok" [vis, c + 1] m)
    else cdaK8 vis nm (pinAtW m 32) := rfl
theorem cdaK8_some : cdaK8 vis nm (some (r, m)) = cdaK9 vis nm (r.headD 0) (pinAtW m 33) := rfl
theorem cdaK9_some : cdaK9 vis nm a (some (r, m)) =
    if nm = a ∨ nm = r.headD 0 then none else cdaK10 vis nm (pinAtW m 13) := rfl
theorem cdaK10_some : cdaK10 vis nm (some (r, m)) = if nm = r.headD 0 then some ([vis], m) else none :=
  rfl
theorem cdaT_some : cdaT p n vis c (some (r, m)) =
    if r.headD 0 = 0 then none else cdaRet (callW p n "env_push" [vis, c] m) := rfl
theorem cdaRet_some : cdaRet (some (r, m)) = some ([r.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] cdaW_step => cdaW p (n + 1) m i vis
grind_pattern [ind_grind] cdaK1_some => cdaK1 p n vis (some (r, m))
grind_pattern [ind_grind] cdaK2_some => cdaK2 p n vis c nm (some (r, m))
grind_pattern [ind_grind] cdaQ1_some => cdaQ1 p n vis c (some (r, m))
grind_pattern [ind_grind] cdaQ2_some => cdaQ2 vis (some (r, m))
grind_pattern [ind_grind] cdaK3_some => cdaK3 p n vis c nm (some (r, m))
grind_pattern [ind_grind] cdaK4_some => cdaK4 p n vis c nm (some (r, m))
grind_pattern [ind_grind] cdaK5_some => cdaK5 p n vis c nm (some (r, m))
grind_pattern [ind_grind] cdaK6_some => cdaK6 p n vis c nm (some (r, m))
grind_pattern [ind_grind] cdaK7_some => cdaK7 p n vis c nm a (some (r, m))
grind_pattern [ind_grind] cdaK8_some => cdaK8 vis nm (some (r, m))
grind_pattern [ind_grind] cdaK9_some => cdaK9 vis nm a (some (r, m))
grind_pattern [ind_grind] cdaK10_some => cdaK10 vis nm (some (r, m))
grind_pattern [ind_grind] cdaT_some => cdaT p n vis c (some (r, m))
grind_pattern [ind_grind] cdaRet_some => cdaRet (some (r, m))

set_option maxHeartbeats 3200000 in
theorem cda_specW (p : Prog) (hp : p.lookup "check_decl_axiom" = some checkDeclAxiom)
    (hR : RecProg p) (hpa : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (i vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_decl_axiom" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ cdaW p n s₀.mem i vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkDeclAxiom]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, erecCi_specW p hR n,
        pinAt_specW p hpa n, callW_spec p n "rom_basis_decls", callW_spec p n "ci_canon_eq",
        callW_spec p n "check_constant_val", callW_spec p n "std_axiom_ok",
        callW_spec p n "env_push", callW_spec p n "trust_compiler_ok",
        callW_spec p n "of_reduce_ax_ok"] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, pinAtW]

local notation "V" => ConLeche.CheckMode.verified

/-- An `env_push` call of a decoded record, at the stage relation. -/
theorem push_call {p : Prog} (hRp : RecProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {c : Word} {r : List Word}
    {ci : IConstantInfo} (hc : callW p n "env_push" [vis, c] m = some (r, m'))
    (hS : StageR dn vis fe m a) (hci : decCI (erecP m) dn c.toNat = some ci) :
    StageR dn (r.headD 0) (fe.push ci) m' a ∧ IWGrow m m' := by
  obtain ⟨w, hw1, hwl, -⟩ := decCI_name hci
  have hcb : c.toNat + 1 < 2 ^ 64 := erecP_bound hw1 hS.2
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 hcb
  have hw : (rdW (m.arr64 EREC) (c + 1)).toNat < 2 ^ 32 := by
    rw [rdW_of_get? hc1.symm (erecP_get hw1)]; exact hwl
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envPush_specW p hRp n ⟨m, Locals.init []⟩ vis c hw) hc
  rw [hs'] at hW
  exact envPushW_ok hW hS hci

/-- The lookups of the axiom arm. -/
structure AxProg (p : Prog) : Prop where
  quot : QuotProg p
  val : ValProg p
  std : StdProg2 p
  tco : TcoProg p
  ora : OraProg p
  cda : p.lookup "check_decl_axiom" = some checkDeclAxiom

/-- The calls of the axiom arm other than `erec_ci` and `check_constant_val` (all leaves of the
declaration loop: `cdaW_okT` carries the core's memos across them by their frame). -/
def cdaLeaves : List FnName :=
  ["rom_basis_decls", "ci_canon_eq", "std_axiom_ok", "env_push", "trust_compiler_ok",
    "of_reduce_ax_ok"]

/-- **The axiom arm at the stage relation, over the constant check's spec and a memory invariant
`J`** (kept by `erec_ci` and the calls of `cdaLeaves`, given by the constant check). `cdaW_ok`
(through the `StageR` spec of `check_constant_val`, `J` trivial) and `cdaW_okT` (through its
`StageT` spec, `J` the core's memos) instantiate it. -/
theorem cdaW_gen {p : Prog} (hX : AxProg p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {i : Word} {r : List Word}
    {ds : Array IDeclaration} {pins : List INatOpPinSet} {cv : IConstantVal} (J : Mem → Prop)
    (hJe : ∀ {k : Nat} {x y : Mem} {rx : List Word}, erecCiW k x i 0 = some (rx, y) → J x → J y)
    (hJ : ∀ {f : FnName} {k : Nat} {args : List Word} {x y : Mem} {rx : List Word}, f ∈ cdaLeaves →
      callW p k f args x = some (rx, y) → J x → J y)
    (hccv : ∀ {k : Nat} {r1 r3 : List Word} {m1 m3 : Mem}, k < n →
      erecCiW k m i 0 = some (r1, m1) → StageR dn vis fe m1 a →
      decCV (erecP m1) (r1.headD 0 + 1).toNat = some cv → (r1.headD 0).toNat + 8 < 2 ^ 64 →
      callW p k "check_constant_val" [vis, r1.headD 0 + 1] m1 = some (r3, m3) →
      AM.ok (checkConstantVal V fe cv) a ∧
        StageR dn vis fe m3 (AM.st (checkConstantVal V fe cv) a) ∧ IWGrow m1 m3 ∧ J m3)
    (h : cdaW p n m i vis = some (r, m')) (hS : StageR dn vis fe m a) (hJ0 : J m)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .axiomDecl cv) (hok : ConRon.Bridge.StateOK a)
    (hN : L.Rom.NamesDn dn a L.Rom.quotNames) :
    ∃ fe' a', (checkDecl V pins fe (.axiomDecl cv)).run a = .ok (fe', a') ∧
      StageR dn (r.headD 0) fe' m' a' ∧ IWGrow m m' ∧ J m' := by
  have hdecl := hD.recs i.toNat hi
  rw [hd] at hdecl
  obtain ⟨-, hcvAt⟩ := hdecl
  cases n with
  | zero => simp [cdaW] at h
  | succ n =>
  rw [cdaW_step] at h
  cases h1 : erecCiW n m i 0 with
  | none => rw [h1] at h; cases h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, cdaK1_some] at h
  obtain ⟨hS1, hg1, hci1, hcv1, htop1⟩ := erecCiW_okA h1 hS hD hi hcvAt
  have hJ1 : J m1 := hJe h1 hJ0
  have hccv1 := @hccv n r1
  generalize hq : r1.headD 0 = q at h hci1 hcv1 htop1 hccv1
  have hqb : q.toNat + 8 < 2 ^ 64 := by
    have := hS1.2.2.1; have := hS1.2.2.2.2.1; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 (by omega)
  obtain ⟨wn, hwn, hwnl, hname0⟩ := decCI_name hci1
  have hname : cv.name = decI wn := hname0
  rw [rdW_of_get? hq1.symm (erecP_get hwn)] at h
  -- `Quot.sound`
  cases e2 : pinAtW m1 4 with
  | none => rw [e2] at h; cases h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [e2, cdaK2_some] at h
  obtain ⟨hm2, hr2, hl2, hrun2⟩ := pinAtW_ok e2 hS1.1.pins
  have ep2 : r2.headD 0 = pinW m1 (1 + (4 : Word).toNat) := by rw [hr2]; rfl
  have hb2 := decI_beq (k := .name) wn _ hwnl hl2
  rw [hm2] at h
  simp only [checkDecl, StateT.run_bind, pinQuotSound, show PIN_QUOT_SOUND = (4 : Word).toNat from rfl,
    hrun2, exc_ok_bind', hname, hb2]
  have hcv1' : decCV (erecP m1) (q + 1).toNat = some cv := by rw [hq1]; exact hcv1
  by_cases eq2 : wn = r2.headD 0
  · ----- `Quot.sound`
    rw [if_pos eq2] at h
    rw [ep2] at eq2
    simp only [eq2, decide_true, if_true]
    cases e3 : callW p n "rom_basis_decls" [4] m1 with
    | none => rw [e3] at h; cases h
    | some rm3 =>
    obtain ⟨r3, m3⟩ := rm3
    rw [e3, cdaQ1_some] at h
    obtain ⟨blk, a3, hrun3, hS3, hg3, hD3, -⟩ :=
      hX.quot.rom.quot dn vis fe n m1 a r3 m3 ⟨hS1, hok, hN⟩ e3
    have hJ3 : J m3 := hJ (by simp [cdaLeaves]) e3 hJ1
    have hrun3' : (BasisKind.decls .quotK).run a = .ok (blk, a3) := hrun3
    have hok3 := (ConRon.Bridge.BasisKind.decls_run hok hrun3').1
    generalize r3.headD 0 = o3 at h hD3
    generalize r3.tail.headD 0 = l3 at h hD3
    obtain ⟨hl, h⟩ := of_ite_none h
    have hlt : 4 < (l3).toNat := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hl); simpa using this
    obtain ⟨v, ci, hv, hci, hget⟩ := decPL_get _ _ _ hD3 4 hlt
    have hvm : iwN m3 (o3.toNat + 4) = some v := (IWGrow.refl m3).truncExt.1.nat? hv
    obtain ⟨w, hw, rfl⟩ : ∃ w, (iwA m3)[o3.toNat + 4]? = some w ∧ w.toNat = v := by
      simp only [iwN, nat?, Option.map_eq_some_iff] at hvm; exact hvm
    have hob : o3.toNat + 4 < 2 ^ 64 := by
      have := (Array.getElem?_eq_some_iff.mp hw).1; have := hS3.2.2.2.1; simp only [iwA] at *; omega
    have ew : rdW (m3.arr64 IW) (o3 + 4) = w := by
      have : (o3 + 4).toNat = o3.toNat + 4 := by
        rw [UInt64.toNat_add]; simp; omega
      simp only [rdW, this]; simp only [iwA] at hw; simp [hw]
    rw [ew] at h
    cases e4 : callW p n "ci_canon_eq" [q, w] m3 with
    | none => rw [e4] at h; cases h
    | some rm4 =>
    obtain ⟨r4, m4⟩ := rm4
    rw [e4, cdaQ2_some] at h
    obtain ⟨s4, hs4, -, hok4, ⟨⟨hS4, hg4, hb4, -⟩, -⟩, -⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (ciCanonEq_refines p hX.quot.canon dn vis fe q w (.axiomInfo cv) ci n ⟨m3, Locals.init []⟩ a3
        ⟨hS3, ArrExt.decCI (IWGrow.erecPExt hg3) hci1, ArrExt.decCI (truncM_erecP m3) hci,
          poolSmall_of_stage hS3, fun x y l hx hy => hok3.view_inj hx hy⟩) e4
    subst hs4
    have hrun4 := AM.run_of_ok _ _ hok4
    obtain ⟨z4, h⟩ := of_ite_none h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hb : AM.res ((IConstantInfo.axiomInfo cv).canonEq ci) a3 = true := by
      rw [← hb4]; simpa using z4
    rw [hb] at hrun4
    refine ⟨fe, _, ?_, by simpa using hS4, hg1.trans (hg3.trans hg4),
      hJ (by simp [cdaLeaves]) e4 hJ3⟩
    rw [StateT.run_bind, hrun3', exc_ok_bind']
    simp only [hget, StateT.run_bind, hrun4, exc_ok_bind', if_true]
    rfl
  ----- the ordinary axioms
  rw [if_neg eq2] at h
  rw [ep2] at eq2
  simp only [eq2, decide_false, Bool.false_eq_true, if_false]
  -- the constant check
  cases e3 : callW p n "check_constant_val" [vis, q + 1] m1 with
  | none => rw [e3] at h; cases h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [e3, cdaK3_some] at h
  obtain ⟨hok3, hS3, hg3, hJ3⟩ := hccv1 (by omega) h1 hS1 hcv1' hqb e3
  have hrun3 := AM.run_of_ok _ _ hok3
  generalize AM.st (checkConstantVal V fe cv) a = a3 at hrun3 hS3
  have hP3 : ArrExt (erecP m1) (erecP m3) := IWGrow.erecPExt hg3
  -- the standard axioms
  cases e4 : callW p n "std_axiom_ok" [vis, q + 1] m3 with
  | none => rw [e4] at h; cases h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [e4, cdaK4_some] at h
  obtain ⟨s4, hs4, -, hok4, hS4, hg4, hb4, -⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (stdAxiomOk_refines p hX.std dn hdn vis fe (q + 1) cv n ⟨m3, Locals.init []⟩ a3
      ⟨hS3, ArrExt.decCV hP3 hcv1'⟩) e4
  subst hs4
  have hJ4 : J s4.mem := hJ (by simp [cdaLeaves]) e4 hJ3
  have hrun4 := AM.run_of_ok _ _ hok4
  generalize AM.res (stdAxiomOk fe cv) a3 = b4 at hrun4 hb4
  generalize AM.st (stdAxiomOk fe cv) a3 = a4 at hrun4 hS4
  have hP4 : ArrExt (erecP m1) (erecP s4.mem) := IWGrow.erecPExt (hg3.trans hg4)
  -- a push of the axiom, after a passed test
  have push : ∀ {mx : Mem} {ax : AState} {rx : List Word} {mf : Mem},
      StageR dn vis fe mx ax → IWGrow m1 mx → J mx →
      cdaRet (callW p n "env_push" [vis, q] mx) = some (r, m') →
      StageR dn (r.headD 0) (fe.push (.axiomInfo cv)) m' ax ∧ IWGrow mx m' ∧ J m' := by
    intro mx ax rx mf hSx hgx hJx hx
    cases e : callW p n "env_push" [vis, q] mx with
    | none => rw [e] at hx; cases hx
    | some rmx =>
    obtain ⟨ry, my⟩ := rmx
    rw [e, cdaRet_some] at hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hx)
    obtain ⟨hSy, hgy⟩ := push_call hX.val.rcp e hSx (ArrExt.decCI (IWGrow.erecPExt hgx) hci1)
    exact ⟨by simpa using hSy, hgy, hJ (by simp [cdaLeaves]) e hJx⟩
  by_cases z4 : r4.headD 0 ≠ 0
  · rw [if_pos z4] at h
    have hb : b4 = true := by rw [← hb4]; simpa using z4
    obtain ⟨hS', hg', hJ'⟩ := push (rx := []) (mf := m) hS4 (hg3.trans hg4) hJ4 h
    refine ⟨_, a4, ?_, hS', hg1.trans (hg3.trans (hg4.trans hg')), hJ'⟩
    simp only [StateT.run_bind, hrun3, exc_ok_bind', hrun4, hb, if_true]
    rfl
  rw [if_neg z4] at h
  have hb : b4 = false := by rw [← hb4]; simpa using z4
  simp only [StateT.run_bind, hrun3, exc_ok_bind', hrun4, hb, Bool.false_eq_true, if_false]
  -- `Lean.trustCompiler`
  cases e5 : pinAtW s4.mem 42 with
  | none => rw [e5] at h; cases h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [e5, cdaK5_some] at h
  obtain ⟨hm5, hr5, hl5, hrun5⟩ := pinAtW_ok e5 hS4.1.pins
  have ep5 : r5.headD 0 = pinW s4.mem (1 + (42 : Word).toNat) := by rw [hr5]; rfl
  have hb5 := decI_beq (k := .name) wn _ hwnl hl5
  rw [hm5] at h
  simp only [trustCompilerName, pinTrustCompiler, show PIN_TRUST_COMPILER = (42 : Word).toNat from rfl,
    StateT.run_bind, hrun5, exc_ok_bind', hb5]
  by_cases eq5 : wn = r5.headD 0
  · rw [if_pos eq5] at h
    rw [ep5] at eq5
    simp only [eq5, decide_true, if_true]
    cases e6 : callW p n "trust_compiler_ok" [vis, q + 1] s4.mem with
    | none => rw [e6] at h; cases h
    | some rm6 =>
    obtain ⟨r6, m6⟩ := rm6
    rw [e6, cdaT_some] at h
    obtain ⟨s6, hs6, -, hok6, hS6, hg6, hb6, -⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
      (trustCompilerOk_refines p hX.tco dn vis fe (q + 1) cv n ⟨s4.mem, Locals.init []⟩ a4
        ⟨hS4, ArrExt.decCV hP4 hcv1'⟩) e6
    subst hs6
    have hrun6 := AM.run_of_ok _ _ hok6
    obtain ⟨z6, h⟩ := of_ite_none h
    have ht6 : AM.res (trustCompilerOk fe cv) a4 = true := by rw [← hb6]; simpa using z6
    rw [ht6] at hrun6
    obtain ⟨hS', hg', hJ'⟩ := push (rx := []) (mf := m) hS6 (hg3.trans (hg4.trans hg6))
      (hJ (by simp [cdaLeaves]) e6 hJ4) h
    refine ⟨_, _, ?_, hS', hg1.trans (hg3.trans (hg4.trans (hg6.trans hg'))), hJ'⟩
    simp only [StateT.run_bind, hrun6, exc_ok_bind', if_true]
    rfl
  rw [if_neg eq5] at h
  rw [ep5] at eq5
  simp only [eq5, decide_false, Bool.false_eq_true, if_false]
  -- the `ofReduce*` pair
  cases e7 : pinAtW s4.mem 45 with
  | none => rw [e7] at h; cases h
  | some rm7 =>
  obtain ⟨r7, m7⟩ := rm7
  rw [e7, cdaK6_some] at h
  obtain ⟨hm7, hr7, hl7, hrun7⟩ := pinAtW_ok e7 hS4.1.pins
  have ep7 : r7.headD 0 = pinW s4.mem (1 + (45 : Word).toNat) := by rw [hr7]; rfl
  rw [hm7, ep7] at h
  cases e8 : pinAtW s4.mem 46 with
  | none => rw [e8] at h; cases h
  | some rm8 =>
  obtain ⟨r8, m8⟩ := rm8
  rw [e8, cdaK7_some] at h
  obtain ⟨hm8, hr8, hl8, hrun8⟩ := pinAtW_ok e8 hS4.1.pins
  have ep8 : r8.headD 0 = pinW s4.mem (1 + (46 : Word).toNat) := by rw [hr8]; rfl
  rw [hm8] at h
  have hb7 := decI_beq (k := .name) wn _ hwnl hl7
  have hb8 := decI_beq (k := .name) wn _ hwnl hl8
  simp only [ofReduceNatName, pinOfReduceNat, show PIN_OF_REDUCE_NAT = (45 : Word).toNat from rfl,
    ofReduceBoolName, pinOfReduceBool, show PIN_OF_REDUCE_BOOL = (46 : Word).toNat from rfl,
    StateT.run_bind, hrun7, hrun8, exc_ok_bind', hb7, hb8]
  by_cases eq8 : wn = pinW s4.mem (1 + (45 : Word).toNat) ∨ wn = r8.headD 0
  · rw [if_pos eq8] at h
    rw [ep8] at eq8
    have hor : (decide (wn = pinW s4.mem (1 + (45 : Word).toNat)) ||
        decide (wn = pinW s4.mem (1 + (46 : Word).toNat))) = true := by
      rcases eq8 with e | e <;> simp [e]
    simp only [hor, if_true]
    cases e9 : callW p n "of_reduce_ax_ok" [vis, q + 1] s4.mem with
    | none => rw [e9] at h; cases h
    | some rm9 =>
    obtain ⟨r9, m9⟩ := rm9
    rw [e9, cdaT_some] at h
    obtain ⟨s9, hs9, -, hok9, hS9, hg9, hb9, -⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
      (ofReduceAxOk_refines p hX.ora dn hdn vis fe (q + 1) cv n ⟨s4.mem, Locals.init []⟩ a4
        ⟨hS4, ArrExt.decCV hP4 hcv1'⟩) e9
    subst hs9
    have hrun9 := AM.run_of_ok _ _ hok9
    obtain ⟨z9, h⟩ := of_ite_none h
    have ht9 : AM.res (ofReduceAxOk fe cv) a4 = true := by rw [← hb9]; simpa using z9
    rw [ht9] at hrun9
    obtain ⟨hS', hg', hJ'⟩ := push (rx := []) (mf := m) hS9 (hg3.trans (hg4.trans hg9))
      (hJ (by simp [cdaLeaves]) e9 hJ4) h
    refine ⟨_, _, ?_, hS', hg1.trans (hg3.trans (hg4.trans (hg9.trans hg'))), hJ'⟩
    simp only [StateT.run_bind, hrun9, exc_ok_bind', if_true]
    rfl
  rw [if_neg eq8] at h
  rw [ep8] at eq8
  have hor : (decide (wn = pinW s4.mem (1 + (45 : Word).toNat)) ||
      decide (wn = pinW s4.mem (1 + (46 : Word).toNat))) = false := by
    simp only [not_or] at eq8; simp only [decide_eq_false eq8.1, decide_eq_false eq8.2, Bool.or_false]
  simp only [hor, Bool.false_eq_true, if_false]
  -- `propext`/`choice` of another shape decline
  cases e10 : pinAtW s4.mem 32 with
  | none => rw [e10] at h; cases h
  | some rm10 =>
  obtain ⟨r10, m10⟩ := rm10
  rw [e10, cdaK8_some] at h
  obtain ⟨hm10, hr10, hl10, hrun10⟩ := pinAtW_ok e10 hS4.1.pins
  have ep10 : r10.headD 0 = pinW s4.mem (1 + (32 : Word).toNat) := by rw [hr10]; rfl
  rw [hm10, ep10] at h
  cases e11 : pinAtW s4.mem 33 with
  | none => rw [e11] at h; cases h
  | some rm11 =>
  obtain ⟨r11, m11⟩ := rm11
  rw [e11, cdaK9_some] at h
  obtain ⟨hm11, hr11, hl11, hrun11⟩ := pinAtW_ok e11 hS4.1.pins
  have ep11 : r11.headD 0 = pinW s4.mem (1 + (33 : Word).toNat) := by rw [hr11]; rfl
  rw [hm11] at h
  obtain ⟨eq11, h⟩ := of_ite_none h
  rw [ep11] at eq11
  have hb10 := decI_beq (k := .name) wn _ hwnl hl10
  have hb11 := decI_beq (k := .name) wn _ hwnl hl11
  have hor2 : (decide (wn = pinW s4.mem (1 + (32 : Word).toNat)) ||
      decide (wn = pinW s4.mem (1 + (33 : Word).toNat))) = false := by
    simp only [not_or] at eq11; simp only [decide_eq_false eq11.1, decide_eq_false eq11.2, Bool.or_false]
  simp only [propextName, pinPropext, show PIN_PROPEXT = (32 : Word).toNat from rfl,
    choiceName, pinChoice, show PIN_CHOICE = (33 : Word).toNat from rfl,
    StateT.run_bind, hrun10, hrun11, exc_ok_bind', hb10, hb11, hor2, Bool.false_eq_true, if_false]
  -- `sorryAx` is skipped
  cases e12 : pinAtW s4.mem 13 with
  | none => rw [e12] at h; cases h
  | some rm12 =>
  obtain ⟨r12, m12⟩ := rm12
  rw [e12, cdaK10_some] at h
  obtain ⟨hm12, hr12, hl12, hrun12⟩ := pinAtW_ok e12 hS4.1.pins
  have ep12 : r12.headD 0 = pinW s4.mem (1 + (13 : Word).toNat) := by rw [hr12]; rfl
  rw [hm12] at h
  by_cases eq12 : wn = r12.headD 0
  · rw [if_pos eq12] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [ep12] at eq12
    have hb12 := decI_beq (k := .name) wn _ hwnl hl12
    refine ⟨fe, a4, ?_, by simpa using hS4, hg1.trans (hg3.trans hg4), hJ4⟩
    simp only [pinSorryAx, show PIN_SORRY_AX = (13 : Word).toNat from rfl, StateT.run_bind, hrun12,
      exc_ok_bind', hb12, eq12, decide_true, if_true, beq_self_eq_true]
    rfl
  · rw [if_neg eq12] at h; cases h

end L.Arena
