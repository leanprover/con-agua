import ConAgua.Arena.RecCheckSpec.TruncSl
import ConAgua.Arena.RecGenSpec.CtorLp
import ConAgua.Arena.InferBodyIntern
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# DecTMSlices

`cxoK8`, `cxoK7`, `cxoK6`, `cxoK5`, `cxoK4`, `cxoK3` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The model -/

section model
variable (p : Prog) (n : Nat)

/-- After `inst_pis_with`: the record. -/
def cxoK8 (cv cA ko kl e0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else
      cxoK9 (callW p n "rec6" [cv, rdW (m.arr64 IW) (cA + 1), ko, kl, r.tail.headD 0, rdW (m.arr64 IW) (e0 + 4)] m)

/-- After `target_ctor_at`: the type at the class's parameters. -/
def cxoK7 (mw cv cA ko kl e0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cxoK8 p n cv cA ko kl e0
      (callW p n "inst_pis_with" [rdW (m.arr64 IW) (mw + 2), rdW (m.arr64 IW) (mw + 3), r.headD 0] m)

/-- After `class_fields_agree`: the constructor's type at the class. -/
def cxoK6 (mw cv cA ko kl e0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => cxoK7 p n mw cv cA ko kl e0 (callW p n "target_ctor_at" [mw, cv] m)

/-- After `class_fields_of`: node agreement. -/
def cxoK5 (vis q fto ftl mo ml mw cv cA fvo fvl eo el e0 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cxoK6 p n mw cv cA (r.headD 0) (r.tail.headD 0) e0
      (callW p n "class_fields_agree" [vis, q, fto, ftl, mo, ml, fvo, fvl, eo, el, 0, r.headD 0, r.tail.headD 0] m)

/-- After `open_pis_at_fvars_f`: the fields' kinds. -/
def cxoK4 (vis q fto ftl mo ml mw cv cA io il eo el e0 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else
      cxoK5 p n vis q fto ftl mo ml mw cv cA (r.tail.headD 0) (r.tail.tail.headD 0) eo el e0
        (callW p n "class_fields_of" [q, io, il, 0, r.tail.headD 0, r.tail.tail.headD 0] m)

/-- After `class_minor_slot`: the datum's telescope. -/
def cxoK3 (vis q fto ftl mo ml mw cv cA eo el e0 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cxoK4 p n vis q fto ftl mo ml mw cv cA (r.tail.headD 0) (r.tail.tail.headD 0) eo el e0
      (callW p n "open_pis_at_fvars_f" [rdW (m.arr64 IW) (cA + 1), rdW (m.arr64 IW) (e0 + 4),
        rdW (m.arr64 IW) (q + 4) + rdW (m.arr64 IW) (q + 1)] m)

/-- After `class_ctor_of_nfs`: the minor premise. -/
def cxoK2 (vis q fto ftl rd mo ml c mw cv cA : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.tail.headD 0 = 0 then none else
      cxoK3 p n vis q fto ftl mo ml mw cv cA (r.headD 0) (r.tail.headD 0) (rdW (m.arr64 IW) (r.headD 0))
        (callW p n "class_minor_slot" [rd, c, rdW (m.arr64 EREC) cv] m)

/-- After `target_major_at`: the class's entries of the constructor. -/
def cxoK1 (vis q fto ftl rd mo ml c cA : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cxoK2 p n vis q fto ftl rd mo ml c (r.headD 0) (rdW (m.arr64 IW) cA) cA
      (callW p n "class_ctor_of_nfs" [rdW (m.arr64 IW) (r.headD 0 + 9), rdW (m.arr64 IW) (r.headD 0 + 10),
        rdW (m.arr64 EREC) (rdW (m.arr64 IW) cA)] m)

/-- **The model of `class_ctor_of(vis, p, ft.off, ft.len, rd, ms.off, ms.len, c, cA)`** (callees
at fuel `n`). -/
def cxoW (m : Mem) (vis q fto ftl rd mo ml c cA : Word) : Option (List Word × Mem) :=
  cxoK1 p n vis q fto ftl rd mo ml c cA (callW p n "target_major_at" [mo, ml, c] m)

section arms
variable (m : Mem) (r : List Word) (vis q fto ftl rd mo ml c cA mw cv eo el e0 io il fvo fvl ko kl : Word)
theorem cxoK9_some : cxoK9 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem cxoK8_bad (h : r.headD 0 = 0) : cxoK8 p n cv cA ko kl e0 (some (r, m)) = none := by
  simp only [cxoK8]; rw [ite_eq_left h]
theorem cxoK8_ok (h : ¬ r.headD 0 = 0) : cxoK8 p n cv cA ko kl e0 (some (r, m)) =
    cxoK9 (callW p n "rec6" [cv, rdW (m.arr64 IW) (cA + 1), ko, kl, r.tail.headD 0, rdW (m.arr64 IW) (e0 + 4)] m) := by
  simp only [cxoK8]; rw [ite_eq_right h]
theorem cxoK7_some : cxoK7 p n mw cv cA ko kl e0 (some (r, m)) = cxoK8 p n cv cA ko kl e0
    (callW p n "inst_pis_with" [rdW (m.arr64 IW) (mw + 2), rdW (m.arr64 IW) (mw + 3), r.headD 0] m) := rfl
theorem cxoK6_some : cxoK6 p n mw cv cA ko kl e0 (some (r, m)) =
    cxoK7 p n mw cv cA ko kl e0 (callW p n "target_ctor_at" [mw, cv] m) := rfl
theorem cxoK5_some : cxoK5 p n vis q fto ftl mo ml mw cv cA fvo fvl eo el e0 (some (r, m)) =
    cxoK6 p n mw cv cA (r.headD 0) (r.tail.headD 0) e0
      (callW p n "class_fields_agree" [vis, q, fto, ftl, mo, ml, fvo, fvl, eo, el, 0, r.headD 0, r.tail.headD 0] m) := rfl
theorem cxoK4_bad (h : r.headD 0 = 0) :
    cxoK4 p n vis q fto ftl mo ml mw cv cA io il eo el e0 (some (r, m)) = none := by
  simp only [cxoK4]; rw [ite_eq_left h]
theorem cxoK4_ok (h : ¬ r.headD 0 = 0) : cxoK4 p n vis q fto ftl mo ml mw cv cA io il eo el e0 (some (r, m)) =
    cxoK5 p n vis q fto ftl mo ml mw cv cA (r.tail.headD 0) (r.tail.tail.headD 0) eo el e0
      (callW p n "class_fields_of" [q, io, il, 0, r.tail.headD 0, r.tail.tail.headD 0] m) := by
  simp only [cxoK4]; rw [ite_eq_right h]
theorem cxoK3_some : cxoK3 p n vis q fto ftl mo ml mw cv cA eo el e0 (some (r, m)) =
    cxoK4 p n vis q fto ftl mo ml mw cv cA (r.tail.headD 0) (r.tail.tail.headD 0) eo el e0
      (callW p n "open_pis_at_fvars_f" [rdW (m.arr64 IW) (cA + 1), rdW (m.arr64 IW) (e0 + 4),
        rdW (m.arr64 IW) (q + 4) + rdW (m.arr64 IW) (q + 1)] m) := rfl
theorem cxoK2_bad (h : r.tail.headD 0 = 0) : cxoK2 p n vis q fto ftl rd mo ml c mw cv cA (some (r, m)) = none := by
  simp only [cxoK2]; rw [ite_eq_left h]
theorem cxoK2_ok (h : ¬ r.tail.headD 0 = 0) : cxoK2 p n vis q fto ftl rd mo ml c mw cv cA (some (r, m)) =
    cxoK3 p n vis q fto ftl mo ml mw cv cA (r.headD 0) (r.tail.headD 0) (rdW (m.arr64 IW) (r.headD 0))
      (callW p n "class_minor_slot" [rd, c, rdW (m.arr64 EREC) cv] m) := by
  simp only [cxoK2]; rw [ite_eq_right h]
theorem cxoK1_some : cxoK1 p n vis q fto ftl rd mo ml c cA (some (r, m)) =
    cxoK2 p n vis q fto ftl rd mo ml c (r.headD 0) (rdW (m.arr64 IW) cA) cA
      (callW p n "class_ctor_of_nfs" [rdW (m.arr64 IW) (r.headD 0 + 9), rdW (m.arr64 IW) (r.headD 0 + 10),
        rdW (m.arr64 EREC) (rdW (m.arr64 IW) cA)] m) := rfl
end arms

end model

attribute [ind_grind] cxoK9_some cxoK8_bad cxoK8_ok cxoK7_some cxoK6_some cxoK5_some cxoK4_bad cxoK4_ok
  cxoK3_some cxoK2_bad cxoK2_ok cxoK1_some

/-! ## The `vcgen` specs: the body's tail as a named block -/

/-- The tail of `classCtorOfL` (RecGen.lean) from `class_fields_of` on, named for its spec. -/
-- con-ron: none — `classCtorOfL`'s own tail (`rfl`), a named block for the proof
def cxoB2 : Stmt := lblk (vis, p, ftOff, ftLen, rd, msOff, msLen, c, cA, m, cv, esOff, esLen, e0, s0,
    ihsOff, ihsLen, ok, fvsOff, fvsLen, body, kindsOff, kindsLen, t0, tyD, cc, r) {
  (kindsOff, kindsLen) := call class_fields_of(p, ihsOff, ihsLen, 0, fvsOff, fvsLen);
  r := call class_fields_agree(vis, p, ftOff, ftLen, msOff, msLen, fvsOff, fvsLen, esOff, esLen, 0,
    kindsOff, kindsLen);
  t0 := call target_ctor_at(m, cv);
  (ok, tyD) := call inst_pis_with(IW.u64[m + 2], IW.u64[m + 3], t0);
  if ok == 0 { abort };
  cc := call rec6(cv, IW.u64[cA + 1], kindsOff, kindsLen, tyD, IW.u64[e0 + 4]);
  return cc
}

/-- `classCtorOfL`, with its tail spliced from `cxoB2`. -/
-- con-ron: none — `classCtorOfL` itself (`rfl`), its tail a named block for the proof
def classCtorOfL' : FunDecl := lfn (vis, p, ftOff, ftLen, rd, msOff, msLen, c, cA)
    locals (m, cv, esOff, esLen, e0, s0, ihsOff, ihsLen, ok, fvsOff, fvsLen, body, kindsOff,
      kindsLen, t0, tyD, cc, r) {
  m := call target_major_at(msOff, msLen, c);
  cv := IW.u64[cA];
  (esOff, esLen) := call class_ctor_of_nfs(IW.u64[m + 9], IW.u64[m + 10], EREC.u64[cv]);
  if esLen == 0 { abort };
  e0 := IW.u64[esOff];
  (s0, ihsOff, ihsLen) := call class_minor_slot(rd, c, EREC.u64[cv]);
  (ok, fvsOff, fvsLen, body) := call open_pis_at_fvars_f(IW.u64[cA + 1], IW.u64[e0 + 4],
    IW.u64[p + 4] + IW.u64[p + 1]);
  if ok == 0 { abort };
  ⟪cxoB2⟫
}

theorem classCtorOfL_eq : classCtorOfL = classCtorOfL' := rfl

theorem cxoB2_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p (n + 1) cxoB2
    ⦃fun r s' => cxoK5 p n (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 5) (s₀.loc 6) (s₀.loc 9)
      (s₀.loc 10) (s₀.loc 8) (s₀.loc 18) (s₀.loc 19) (s₀.loc 11) (s₀.loc 12) (s₀.loc 13)
      (callW p n "class_fields_of" [s₀.loc 1, s₀.loc 15, s₀.loc 16, 0, s₀.loc 18, s₀.loc 19] s₀.mem) =
        some (r.retVal, s'.mem); ⊤⦄ := by
  rw [exec]
  unfold cxoB2
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec,
      callW_spec p n "class_fields_of", callW_spec p n "class_fields_agree",
      callW_spec p n "target_ctor_at", callW_spec p n "inst_pis_with", callW_spec p n "rec6"] <;>
    finish (gen := 40) (instances := 20000)

theorem cxoW_eq (p : Prog) (n : Nat) (m : Mem) (vis q fto ftl rd mo ml c cA : Word) :
    cxoW p n m vis q fto ftl rd mo ml c cA =
      cxoK1 p n vis q fto ftl rd mo ml c cA (callW p n "target_major_at" [mo, ml, c] m) := rfl

theorem cxo_spec (p : Prog) (hp : p.lookup "class_ctor_of" = some classCtorOfL) (n : Nat)
    (s₀ : St) (vis q fto ftl rd mo ml c cA : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "class_ctor_of" [vis, q, fto, ftl, rd, mo, ml, c, cA]
    ⦃fun r s' => LocEq s' s₀ ∧ cxoW p n s₀.mem vis q fto ftl rd mo ml c cA = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp, classCtorOfL_eq]
  simp only [callFn, classCtorOfL']
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec,
      callW_spec p n "target_major_at", callW_spec p n "class_ctor_of_nfs",
      callW_spec p n "class_minor_slot", callW_spec p n "open_pis_at_fvars_f",
      fun s => Triple.step_exec (cxoB2_spec p n s)] <;>
    finish (gen := 40) (instances := 20000) [cxoW_eq, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8]

/-! ## Reading the records -/

/-- A `TargetMajor` decoded below the tops: its entries' slice (words 9, 10) and its parameters'
slice (words 2, 3). -/
theorem decTM_slices {m : Mem} {mw : Word} {M : TargetMajor} (h : DecB (fun m => decTM m mw.toNat) m M)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (∃ o l : Nat, rdW (m.arr64 IW) (mw + 9) = UInt64.ofNat o ∧ rdW (m.arr64 IW) (mw + 10) = UInt64.ofNat l ∧
      o < 2 ^ 64 ∧ l < 2 ^ 64 ∧ DecB (fun m => decPL m (decNCN m) o l) m M.nfs) ∧
    HSl0 m (rdW (m.arr64 IW) (mw + 2)) (rdW (m.arr64 IW) (mw + 3)) M.ds ∧ mw.toNat + 13 < 2 ^ 64 := by
  have h' : decTM (truncM m) mw.toNat = some M := h
  simp only [decTM, bind, Option.bind_eq_some_iff, pure] at h'
  obtain ⟨i, hi, lv, hlv, ds, hds, nPc, hnPc, nIdx, hnIdx, ctors, hctors, mem, hmem, nfs, hnfs, pf, hpf, hM⟩ := h'
  cases hM
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hnfs
  obtain ⟨o2, l2, ho2, hl2, hd2⟩ := decAt_some hds
  obtain ⟨o3, l3, ho3, hl3, -⟩ := decAt_some hpf
  obtain ⟨h12, -⟩ := rec2IwN_trunc hl3
  obtain ⟨-, ho'⟩ := rec2IwN_trunc ho
  obtain ⟨-, hl'⟩ := rec2IwN_trunc hl
  have r9 := iwN_rdW_at (w := mw) (k := 9) ho' hsz
  have r10 := iwN_rdW_at (w := mw) (k := 10) (by simpa [Nat.add_assoc] using hl') hsz
  refine ⟨⟨o, l, by simpa using r9.1, by simpa using r10.1, r9.2, r10.2, hd⟩, ?_, by
    have := (rdW (m.arr64 CTL) 200).toNat_lt; simp only [iwTop] at h12; omega⟩
  have := truncSl (w := mw) (i := 2) ho2 (by simpa [Nat.add_assoc] using hl2) hd2 hsz
  simpa using this

/-- A pointer slice decoded below the tops is empty or below the top. -/
theorem decB_decPL_bound {α : Type} {f : Mem → Nat → Option α} {m : Mem} {o l : Nat} {xs : List α}
    (h : DecB (fun m => decPL m (f m) o l) m xs) : l = 0 ∨ o + l ≤ iwTop m := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · exact .inl h0
  right
  obtain ⟨v, hv, -⟩ := decPL_getH (truncM m) (show decPL (truncM m) (f (truncM m)) o l = some xs from h) (l - 1) (by omega)
  have := (rec2IwN_trunc hv).1
  omega

/-- `target_ctor_at` writes no walk memo. -/
theorem tcW_mfr {cR : CallM} {n : Nat} (hF : IlpFr cR) {m m' : Mem} {M c : Word} {r : List Word}
    (h : tcW cR n m M c = some (r, m')) : MFr [] [] m m' := by
  simp only [tcW] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl
  simp only [tcK1] at h
  refine (posmemo_cvLpsW_mfr h1).trans ?_
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl
  simp only [tcK2, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  obtain ⟨A, C, hA, hC, hfr⟩ := hF _ _ _ _ _ h2
  exact MFr.of_frame hfr hA hC

/-- `inst_pis_with` with its arguments a slice below the top unless empty. -/
theorem instW_ok0 (n : Nat) {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m' : Mem}
    {a : AState} {ao al e : Word} {args : List EIdx} {r : List Word} (h : instW n m ao al e = some (r, m'))
    (hS : StageR dn vis fe m a) (he : H e) (hsl : HSl0 m ao al args) :
    ∃ x a', (ConRon.Arena.instPisWith args (decI e)).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decOE m' r x := by
  rcases hsl.2 with h0 | hb
  · subst h0
    have : args = [] := by have := decHL_length _ hsl.1; simpa using this
    subst this
    rcases n with _ | n
    · simp [instW] at h
    rw [instW_nil (h := rfl)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨some (decI e), a, rfl, hS, IWGrow.refl _, rfl, he, rfl⟩
  · exact instW_ok n dn fe vis m m' a ao al e args r h hS he hsl.1 (hS.lt64 hb) hb

end L.Ind

end
