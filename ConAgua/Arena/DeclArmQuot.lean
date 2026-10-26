import ConAgua.Arena.DeclAxiomSpec4
import ConAgua.Arena.DeclArmOpaque
import ConAgua.Arena.DeclCanonInfo
import ConAgua.Arena.DeclTwin

/-!
# The quotient pin: `quot_pin_hit(k, q)` (lane `decls3`)

`quotPinHit k cv`: the record is the pinned quotient block's constant at its own slot, compared at
`toConstantVal` up to the canonical form (`cv_canon_eq`, helper `decls3-canon`'s
`cvCanonEq_refines`, which compares literals by handle: `LitInj`, from the twin state's
well-formedness `StateOK`, lane `decls4`). Through the ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

section model
variable (p : Prog)

/-- After the comparison. -/
def qphK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([r3.headD 0], m3)

/-- After `ci_to_cv`. -/
def qphK2 (n : Nat) (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => qphK3 (callW p n "cv_canon_eq" [q, r2.headD 0] m2)

/-- After the block's read. -/
def qphK1 (n : Nat) (k q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.tail.headD 0 ≤ k then some ([0], m1)
    else qphK2 p n q (callW p n "ci_to_cv" [rdW (m1.arr64 IW) (r1.headD 0 + k)] m1)

/-- **The model of `quot_pin_hit(k, q)`.** -/
def qphW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, k, q => qphK1 p n k q (callW p n "rom_basis_decls" [4] m)

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (k q : Word) (r1 r2 r3 : List Word)
theorem qphW_step : qphW p (n + 1) m k q = qphK1 p n k q (callW p n "rom_basis_decls" [4] m) := rfl
theorem qphK1_some : qphK1 p n k q (some (r1, m1)) =
    if r1.tail.headD 0 ≤ k then some ([0], m1)
    else qphK2 p n q (callW p n "ci_to_cv" [rdW (m1.arr64 IW) (r1.headD 0 + k)] m1) := rfl
theorem qphK2_some : qphK2 p n q (some (r2, m2)) =
    qphK3 (callW p n "cv_canon_eq" [q, r2.headD 0] m2) := rfl
theorem qphK3_some : qphK3 (some (r3, m3)) = some ([r3.headD 0], m3) := rfl
end arms

grind_pattern [ind_grind] qphW_step => qphW p (n + 1) m k q
grind_pattern [ind_grind] qphK1_some => qphK1 p n k q (some (r1, m1))
grind_pattern [ind_grind] qphK2_some => qphK2 p n q (some (r2, m2))
grind_pattern [ind_grind] qphK3_some => qphK3 (some (r3, m3))

theorem qph_specW (hp : p.lookup "quot_pin_hit" = some quotPinHitL) (n : Nat) (s₀ : St)
    (k q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "quot_pin_hit" [k, q]
    ⦃fun r s' => LocEq s' s₀ ∧ qphW p n s₀.mem k q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, quotPinHitL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "rom_basis_decls", callW_spec p n "ci_to_cv",
        callW_spec p n "cv_canon_eq"] <;>
      finish (gen := 20) [rdW_eq]

end model

/-- The pool's size bound canon's comparisons take (`LitR`'s `PoolOK`). -/
theorem poolSmall_of_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {m : Mem} {a : AState} (h : StageR dn vis fe m a) : PoolSmall m := by
  have := h.1.arena.1.lit.1.2.2.1
  unfold PoolSmall; omega

theorem slot_lt (k : ConLeche.QuotKind) : k.slot < 5 := by cases k <;> decide

/-- **`quot_pin_hit(k, q)` refines `quotPinHit`** at the model level. -/
theorem qphW_ok {p : Prog} (hC : CanonProg p) (hR : L.Rom.RomRefs p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal} {k : ConLeche.QuotKind}
    (hW : qphW p n m (UInt64.ofNat k.slot) q = some (r, m')) (hS : StageR dn vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) (hok : ConRon.Bridge.StateOK a)
    (hN : L.Rom.NamesDn dn a L.Rom.quotNames) :
    ∃ b a', (quotPinHit k cv).run a = .ok (b, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      decW0B m' r b := by
  have hks : (UInt64.ofNat k.slot).toNat = k.slot :=
    UInt64.toNat_ofNat_of_lt' (by have := slot_lt k; rw [UInt64_size_eq]; omega)
  cases n with
  | zero => simp [qphW] at hW
  | succ n =>
  rw [qphW_step] at hW
  cases h1 : callW p n "rom_basis_decls" [4] m with
  | none => rw [h1] at hW; cases hW
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, qphK1_some] at hW
  obtain ⟨blk, a1, hrun1, hS1, hg1, hD1, hr1⟩ := hR.quot dn vis fe n m a r1 m1 ⟨hS, hok, hN⟩ h1
  have hrun1' : (BasisKind.decls .quotK).run a = .ok (blk, a1) := hrun1
  have hok1 := (ConRon.Bridge.BasisKind.decls_run hok hrun1').1
  have hlen : blk.length = (r1.tail.headD 0).toNat := decPL_length (truncM m1) hD1
  generalize r1.headD 0 = o at hW hD1 hlen
  generalize r1.tail.headD 0 = l at hW hD1 hlen
  by_cases hl : l ≤ UInt64.ofNat k.slot
  · rw [if_pos hl] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hn : blk[k.slot]? = none := by
      apply List.getElem?_eq_none; rw [hlen]
      have := UInt64.le_iff_toNat_le.mp hl; omega
    refine ⟨false, a1, ?_, hS1, hg1, by simp [decW0B]⟩
    simp only [quotPinHit, StateT.run_bind, hrun1', exc_ok_bind', hn]
    rfl
  rw [if_neg hl] at hW
  have hlt : k.slot < (l).toNat := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hl); omega
  obtain ⟨v, ci, hv, hci, hget⟩ := decPL_get _ _ _ hD1 k.slot hlt
  -- the pointer word
  have hvm : iwN m1 (o.toNat + k.slot) = some v :=
    (IWGrow.refl m1).truncExt.1.nat? hv
  obtain ⟨w, hw, rfl⟩ : ∃ w, (iwA m1)[o.toNat + k.slot]? = some w ∧ w.toNat = v := by
    simp only [iwN, nat?, Option.map_eq_some_iff] at hvm; exact hvm
  have hob : o.toNat + k.slot < 2 ^ 64 := by
    have := (Array.getElem?_eq_some_iff.mp hw).1; have := hS1.2.2.2.1; simp only [iwA] at *; omega
  have hidx : (o + UInt64.ofNat k.slot).toNat = o.toNat + k.slot := by
    rw [UInt64.toNat_add, hks]; simp; omega
  have ew : rdW (m1.arr64 IW) (o + UInt64.ofNat k.slot) = w := by
    simp only [rdW, hidx]; simp only [iwA] at hw; simp [hw]
  rw [ew] at hW
  have hciP : decCI (erecP m1) dn w.toNat = some ci := ArrExt.decCI (truncM_erecP m1) hci
  -- `ci_to_cv`
  cases h2 : callW p n "ci_to_cv" [w] m1 with
  | none => rw [h2] at hW; cases hW
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, qphK2_some] at hW
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, hcv2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (ciToCv_refines p hC dn vis fe w ci n ⟨m1, Locals.init []⟩ a1 ⟨hS1, hciP⟩) h2
  subst hs2
  simp only [AM.res_pure, AM.st_pure] at hS2 hcv2
  -- `cv_canon_eq`
  cases h3 : callW p n "cv_canon_eq" [q, r2.headD 0] s2.mem with
  | none => rw [h3] at hW; cases hW
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, qphK3_some] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl⟩ := hW
  have hg12 := hg1.trans hg2
  obtain ⟨s3, hs3, -, hok3, ⟨⟨hS3, hg3, hd3⟩, -⟩, -⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (cvCanonEq_refines p hC dn vis fe q (r2.headD 0) cv ci.toConstantVal n ⟨s2.mem, Locals.init []⟩
      a1 ⟨hS2, ArrExt.decCV (IWGrow.erecPExt hg12) hq, hcv2, poolSmall_of_stage hS2,
        fun x y l hx hy => hok1.view_inj hx hy⟩) h3
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  refine ⟨_, _, ?_, hS3, hg12.trans hg3, hd3⟩
  simp only [quotPinHit, StateT.run_bind, hrun1', exc_ok_bind', hget]
  exact hrun3

/-! ## The quotient arm `check_decl_quot(i, vis)` -/

open L.Front (DECL DLP DeclsF DeclAt CVAt dw quotW)

/-- The slot word `check_decl_quot` computes from the record's kind word. -/
def slotOfW (kw : Word) : Word := if kw = 1 then 0 else if kw = 2 then 1 else if kw = 3 then 2 else 3

theorem slotOfW_eq (kw : Word) : slotOfW kw = UInt64.ofNat (quotW kw).slot := by
  unfold slotOfW quotW
  by_cases h1 : kw = 1 <;> by_cases h2 : kw = 2 <;> by_cases h3 : kw = 3 <;> simp_all <;> rfl

section qmodel
variable (p : Prog)

/-- After `check_basis_decl`. -/
def cdqK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([r3.headD 0], m3)

/-- After `quot_pin_hit`. -/
def cdqK2 (n : Nat) (vis ks : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then none
    else if ks = 0 then cdqK3 (callW p n "check_basis_decl" [vis, 4] m2) else some ([vis], m2)

/-- After `erec_ci`. -/
def cdqK1 (n : Nat) (vis ks : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => cdqK2 p n vis ks (callW p n "quot_pin_hit" [ks, r1.headD 0 + 1] m1)

/-- **The model of `check_decl_quot(i, vis)`.** -/
def cdqW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, i, vis =>
    cdqK1 p n vis (slotOfW (rdW (m.arr64 DECL) (7 + 8 * i))) (erecCiW n m i 0)

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (i vis ks : Word) (r1 r2 r3 : List Word)
theorem cdqW_step : cdqW p (n + 1) m i vis =
    cdqK1 p n vis (slotOfW (rdW (m.arr64 DECL) (7 + 8 * i))) (erecCiW n m i 0) := rfl
theorem cdqK1_some : cdqK1 p n vis ks (some (r1, m1)) =
    cdqK2 p n vis ks (callW p n "quot_pin_hit" [ks, r1.headD 0 + 1] m1) := rfl
theorem cdqK2_some : cdqK2 p n vis ks (some (r2, m2)) =
    if r2.headD 0 = 0 then none
    else if ks = 0 then cdqK3 (callW p n "check_basis_decl" [vis, 4] m2) else some ([vis], m2) := rfl
theorem cdqK3_some : cdqK3 (some (r3, m3)) = some ([r3.headD 0], m3) := rfl
end arms

grind_pattern [ind_grind] cdqW_step => cdqW p (n + 1) m i vis
grind_pattern [ind_grind] cdqK1_some => cdqK1 p n vis ks (some (r1, m1))
grind_pattern [ind_grind] cdqK2_some => cdqK2 p n vis ks (some (r2, m2))
grind_pattern [ind_grind] cdqK3_some => cdqK3 (some (r3, m3))

set_option maxHeartbeats 1600000 in
theorem cdq_specW (hp : p.lookup "check_decl_quot" = some checkDeclQuot) (hR : RecProg p)
    (n : Nat) (s₀ : St) (i vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_decl_quot" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ cdqW p n s₀.mem i vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkDeclQuot]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, erecCi_specW p hR n,
        callW_spec p n "quot_pin_hit", callW_spec p n "check_basis_decl"] <;>
      finish (gen := 20) [rdW_eq, slotOfW]

end qmodel

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups of the quotient arm. -/
structure QuotProg (p : Prog) : Prop where
  canon : CanonProg p
  rom : L.Rom.RomRefs p
  basis : BasisProg p
  qph : p.lookup "quot_pin_hit" = some quotPinHitL
  cbd : p.lookup "check_basis_decl" = some checkBasisDeclL
  pa : p.lookup "pin_at" = some pinAtL
  cdq : p.lookup "check_decl_quot" = some checkDeclQuot

/-- **The quotient arm at the stage relation, with a memory invariant `J`** kept by `erec_ci`,
`quot_pin_hit` and `check_basis_decl` (`cdqW_ok`: `J` trivial; `cdqW_okT`: the core's memos,
kept by the leaves' frame). -/
theorem cdqW_gen {p : Prog} (hQ : QuotProg p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {i : Word} {r : List Word}
    {ds : Array IDeclaration} {pins : List INatOpPinSet} {k : ConLeche.QuotKind}
    {cv : IConstantVal} (J : Mem → Prop)
    (hJe : ∀ {k : Nat} {x y : Mem} {rx : List Word}, erecCiW k x i 0 = some (rx, y) → J x → J y)
    (hJ : ∀ {f : FnName} {k : Nat} {args : List Word} {x y : Mem} {rx : List Word},
      f ∈ ["quot_pin_hit", "check_basis_decl"] → callW p k f args x = some (rx, y) → J x → J y)
    (h : cdqW p n m i vis = some (r, m')) (hS : StageR dn vis fe m a) (hJ0 : J m)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .quotDecl k cv) (hok : ConRon.Bridge.StateOK a)
    (hN : L.Rom.NamesDn dn a L.Rom.quotNames)
    (hcvD : ∃ c, ConRon.Arena.Frontend.denoteCV a.store cv = some c) :
    ∃ fe' a', (checkDecl V pins fe (.quotDecl k cv)).run a = .ok (fe', a') ∧
      StageR dn (r.headD 0) fe' m' a' ∧ IWGrow m m' ∧ J m' := by
  have hdecl := hD.recs i.toNat hi
  rw [hd] at hdecl
  obtain ⟨-, hcvAt, hk⟩ := hdecl
  have h1r := hD.room
  have h2r := hD.dsize
  have hkw : rdW (m.arr64 DECL) (7 + 8 * i) = dw (m.arr64 DECL) i.toNat 6 :=
    rdW_dw _ (by omega) (by decide) (by decide)
  cases n with
  | zero => simp [cdqW] at h
  | succ n =>
  rw [cdqW_step, hkw, slotOfW_eq, hk] at h
  cases h1 : erecCiW n m i 0 with
  | none => rw [h1] at h; cases h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, cdqK1_some] at h
  obtain ⟨hS1, hg1, -, hcv1, htop1⟩ := erecCiW_okA h1 hS hD hi hcvAt
  have hJ1 : J m1 := hJe h1 hJ0
  have hqb : (r1.headD 0).toNat + 8 < 2 ^ 64 := by
    have := hS1.2.2.1; have := hS1.2.2.2.2.1; omega
  have hq1 : (r1.headD 0 + 1).toNat = (r1.headD 0).toNat + 1 := toNat_add_small _ 1 (by omega)
  -- `quot_pin_hit`
  cases h2 : callW p n "quot_pin_hit" [UInt64.ofNat k.slot, r1.headD 0 + 1] m1 with
  | none => rw [h2] at h; cases h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, cdqK2_some] at h
  have hJ2 : J m2 := hJ (by simp) h2 hJ1
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (qph_specW p hQ.qph n ⟨m1, Locals.init []⟩ _ _) h2
  rw [hs2] at hW2
  obtain ⟨b, a2, hrun2, hS2, hg2, hd2⟩ :=
    qphW_ok hQ.canon hQ.rom hW2 hS1 (by rw [hq1]; exact hcv1) hok hN
  obtain ⟨c, hc⟩ := hcvD
  have hrun2' : quotPinHit k cv a = .ok (b, a2) := hrun2
  obtain ⟨hok2, hx2, -⟩ := ConRon.Bridge.quotPinHit_run hok hc hrun2'
  by_cases z2 : r2.headD 0 = 0
  · rw [if_pos z2] at h; cases h
  rw [if_neg z2] at h
  have hb : b = true := by rw [← hd2.1]; simpa using z2
  rw [hb] at hrun2
  by_cases ht : UInt64.ofNat k.slot = 0
  · rw [if_pos ht] at h
    have hk0 : k = .type := by
      cases k <;> simp_all [ConLeche.QuotKind.slot] <;> exact absurd ht (by decide)
    subst hk0
    cases h3 : callW p n "check_basis_decl" [vis, 4] m2 with
    | none => rw [h3] at h; cases h
    | some rm3 =>
    obtain ⟨r3, m3⟩ := rm3
    rw [h3, cdqK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨s3, hs3, -, hok3, hS3, hg3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (checkBasisDecl_refines p hQ.basis hQ.canon hQ.rom hQ.pa hQ.cbd n ⟨m2, Locals.init []⟩ a2 dn hdn fe
        vis 4 (by decide) hS2 (fun _ => ⟨hok2, L.Rom.NamesDn.ext hN hx2⟩)) h3
    subst hs3
    have hrun3 := AM.run_of_ok _ _ hok3
    refine ⟨_, _, ?_, by simpa using hS3, hg1.trans (hg2.trans hg3), hJ (by simp) h3 hJ2⟩
    show (do if ← quotPinHit .type cv then checkBasisDecl fe .quotK
             else fail (.notImplemented "quotient declaration mismatch")).run a = _
    simp only [StateT.run_bind, hrun2, exc_ok_bind', if_true]
    exact hrun3
  · rw [if_neg ht] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨fe, a2, ?_, by simpa using hS2, hg1.trans hg2, hJ2⟩
    cases k with
    | type => exact absurd rfl ht
    | ctor =>
      show (do if ← quotPinHit .ctor cv then pure fe
               else fail (.notImplemented "quotient declaration mismatch")).run a = _
      simp only [StateT.run_bind, hrun2, exc_ok_bind', if_true]; rfl
    | lift =>
      show (do if ← quotPinHit .lift cv then pure fe
               else fail (.notImplemented "quotient declaration mismatch")).run a = _
      simp only [StateT.run_bind, hrun2, exc_ok_bind', if_true]; rfl
    | ind =>
      show (do if ← quotPinHit .ind cv then pure fe
               else fail (.notImplemented "quotient declaration mismatch")).run a = _
      simp only [StateT.run_bind, hrun2, exc_ok_bind', if_true]; rfl
    | sound =>
      show (do if ← quotPinHit .sound cv then pure fe
               else fail (.notImplemented "quotient soundness axiom mismatch")).run a = _
      simp only [StateT.run_bind, hrun2, exc_ok_bind', if_true]; rfl

end L.Arena
