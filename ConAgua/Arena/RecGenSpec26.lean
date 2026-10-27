import ConAgua.Arena.RecGenSpec24
import ConAgua.Arena.RecGenSpec6

/-!
# `classCtorOf` (lane `indproofs4`, helper `cls`)

`class_ctor_of(vis, p, ft.off, ft.len, rd, ms.off, ms.len, c, cA)`: class `c`'s constructor `cA`,
read for the generator: its class (`target_major_at`), its entries (`class_ctor_of_nfs`), its
minor premise (`class_minor_slot`), the datum's telescope (the `open_pis_at_fvars_f` stub), the
fields' kinds (`class_fields_of`), node agreement (`class_fields_agree`), the constructor's type at
the class (`target_ctor_at`, `inst_pis_with`), the `rec6` record. A straight-line chain: the model
`cxoW` (callees by `callW`), the relational lemma `cxoW_ok` one callee at a time.

* **The minor premise's inductive hypotheses below the top.** `class_minor_slot`'s refinement
  decodes the `ihs` slice in the memory at hand; `class_fields_of` wants it stable. The scan's
  result words are the hit record's words 3 and 4 (`cmsGo_words`), and that record is decoded
  below the tops with the class reading (`decCR`, `DecB`), so the slice is too.
* **The pool's size**: `class_minor_slot` needs `IW`'s size `+ 5` word-sized; every call keeps
  the size (`callW_keepW`), so the bound at the entry suffices.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `class_minor_slot`'s slice, decoded below the tops -/

/-- **The scan's result words**: the initial ones, or the words 3 and 4 of the record at the
result's slot index. -/
theorem cmsGo_words (n : Nat) : ∀ (m : Mem) (off rem j c cc cnt rS rOff rLen x y z w : Word),
    classMinorSlotGoW n m off rem j c cc cnt rS rOff rLen = some (x, y, z, w) →
    (y = rS ∧ z = rOff ∧ w = rLen) ∨
    (z = rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + y) + 3) ∧ w = rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + y) + 4)) := by
  induction n with
  | zero => intro m off rem j c cc cnt rS rOff rLen x y z w h; simp [classMinorSlotGoW] at h
  | succ n ih =>
  intro m off rem j c cc cnt rS rOff rLen x y z w h
  by_cases hrem : rem = 0
  · rw [classMinorSlotGoW_base n m off rem j c cc cnt rS rOff rLen hrem] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact .inl ⟨rfl, rfl, rfl⟩
  by_cases hp : (off + j).toNat < (m.arr64 IW).size
  rotate_left
  · rw [classMinorSlotGoW_oob n m off rem j c cc cnt rS rOff rLen hrem hp] at h; cases h
  rcases hh : classMinorSlotHit (m.arr64 IW) (rdW (m.arr64 IW) (off + j)) c cc with _ | b
  · rw [classMinorSlotGoW_oob2 n m off rem j c cc cnt rS rOff rLen hrem hp hh] at h; cases h
  cases b with
  | false =>
    rw [classMinorSlotGoW_miss n m off rem j c cc cnt rS rOff rLen hrem hp hh] at h
    rcases ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ h with ⟨rfl, rfl, rfl⟩ | h2
    · exact .inl ⟨rfl, rfl, rfl⟩
    · exact .inr h2
  | true =>
    rw [classMinorSlotGoW_hit n m off rem j c cc cnt rS rOff rLen hrem hp hh] at h
    rcases ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ h with ⟨rfl, rfl, rfl⟩ | h2
    · exact .inr ⟨rfl, rfl⟩
    · exact .inr h2

/-- A hit of the twin's scan is a minor slot of the list. -/
theorem hitsFrom_get (c : Nat) (C : NIdx) : ∀ (j : Nat) (sls : List ClassSlot) (s : Nat)
    (ihs : List (Nat × Nat)), (s, ihs) ∈ hitsFrom c C j sls →
    j ≤ s ∧ sls[s - j]? = some (.minor c C ihs)
  | _, [], _, _, h => by simp [hitsFrom] at h
  | j, .motive k :: sls, s, ihs, h => by
    simp only [hitsFrom] at h
    obtain ⟨h1, h2⟩ := hitsFrom_get c C (j + 1) sls s ihs h
    refine ⟨by omega, ?_⟩
    rw [show s - j = (s - (j + 1)) + 1 by omega]; simpa using h2
  | j, .minor c' C' ihs' :: sls, s, ihs, h => by
    simp only [hitsFrom] at h
    split at h
    · rename_i hc
      simp only [List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        simp
      · obtain ⟨h1, h2⟩ := hitsFrom_get c C (j + 1) sls s ihs h
        refine ⟨by omega, ?_⟩
        rw [show s - j = (s - (j + 1)) + 1 by omega]; simpa using h2
    · obtain ⟨h1, h2⟩ := hitsFrom_get c C (j + 1) sls s ihs h
      refine ⟨by omega, ?_⟩
      rw [show s - j = (s - (j + 1)) + 1 by omega]; simpa using h2

/-- **`class_minor_slot` with the class reading decoded below the tops**: the twin's unique hit,
its slice decoded below the tops too. -/
theorem cms_decB (n : Nat) {m : Mem} {rd c cc : Word} {R : ClassRead} {r : List Word}
    (h : classMinorSlotW n m rd c cc = some r) (hR : DecB (fun m => decCR m rd.toNat) m R)
    (hcc : cc.toNat < 2 ^ 32) (hsz : (m.arr64 IW).size + 5 < 2 ^ 64) :
    ∃ s ihs, hitsFrom c.toNat (decI cc) 0 R.slots = [(s, ihs)] ∧ r.headD 0 = UInt64.ofNat s ∧
      DecB (fun m => decPL m (decNN m) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat) m ihs := by
  have hR0 : decCR (truncM m) rd.toNat = some R := hR
  obtain ⟨s, ihs, hh, e1, e2⟩ := classMinorSlotW_ok n m rd c cc R r (hR.get (decCR_mono _)) hcc hsz h
  refine ⟨s, ihs, hh, e1, ?_⟩
  -- the scan's words
  simp only [classMinorSlotW] at h
  split at h
  rotate_left
  · cases h
  rcases hg : classMinorSlotGoW n m (rdW (m.arr64 IW) rd) (rdW (m.arr64 IW) (rd + 1)) 0 c cc 0 0 0 0 with _ | xyzw
  · rw [hg] at h; cases h
  obtain ⟨x, y, z, w⟩ := xyzw
  rw [hg] at h
  by_cases hx : x ≠ 1
  · simp [hx] at h
  simp only [hx, ite_false, Option.some.injEq] at h
  subst h
  simp only [List.headD_cons, List.tail_cons] at e1 e2 ⊢
  rcases cmsGo_words n _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg with ⟨-, rfl, rfl⟩ | ⟨hz, hw⟩
  · have : ihs = [] := by simpa [decPL] using e2.symm
    subst this
    show decPL (truncM m) _ _ _ = _
    simp [decPL]
  -- the hit record, decoded below the tops
  simp only [decCR, bind, Option.bind_eq_some_iff, pure] at hR0
  obtain ⟨slots, hsl, rcs, -, hRe⟩ := hR0
  cases hRe
  obtain ⟨o, l, ho, hl, hdec⟩ := decAt_some hsl
  have hmem : (s, ihs) ∈ hitsFrom c.toNat (decI cc) 0 slots := by rw [hh]; simp
  obtain ⟨-, hget⟩ := hitsFrom_get c.toNat (decI cc) 0 slots s ihs hmem
  simp only [Nat.sub_zero] at hget
  have hsl' : s < slots.length := by
    rcases (List.getElem?_eq_some_iff.mp hget) with ⟨h1, -⟩; exact h1
  have hsl2 : s < l := by rw [← decPL_length _ hdec]; exact hsl'
  obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m) hdec s hsl2
  rw [List.getElem?_eq_getElem hsl'] at hget
  have hslot : slots[s] = .minor c.toNat (decI cc) ihs := Option.some.inj hget
  rw [hslot] at hdv
  obtain ⟨-, -, -, o', l', h3, h4, hd⟩ := decCS_minor hdv
  -- the words
  have hsz64 : (m.arr64 IW).size < 2 ^ 64 := by omega
  obtain ⟨-, ho'⟩ := rec2IwN_trunc ho
  obtain ⟨-, hl'⟩ := rec2IwN_trunc hl
  obtain ⟨-, hv'⟩ := rec2IwN_trunc hv
  obtain ⟨-, h3'⟩ := rec2IwN_trunc h3
  obtain ⟨-, h4'⟩ := rec2IwN_trunc h4
  have hrd : rdW (m.arr64 IW) rd = UInt64.ofNat o := by
    have := iwN_rdW_at (w := rd) (k := 0) (by simpa using ho') hsz64; simpa using this.1
  have hy : y = UInt64.ofNat s := by rw [← e1]
  have hos : (UInt64.ofNat o : Word) + UInt64.ofNat s = UInt64.ofNat (o + s) := by
    apply UInt64.toNat_inj.mp
    have := iwN_lt_size hv'; have := (iwN_rdW ho' (by omega)).2
    rw [UInt64.toNat_add]; simp <;> omega
  have hvw := iwN_rdW hv' (by have := iwN_lt_size hv'; omega)
  have hv3 : UInt64.ofNat v + 3 = UInt64.ofNat (v + 3) := by
    apply UInt64.toNat_inj.mp; have := iwN_lt_size h3'; rw [UInt64.toNat_add]; simp <;> omega
  have hv4 : UInt64.ofNat v + 4 = UInt64.ofNat (v + 4) := by
    apply UInt64.toNat_inj.mp; have := iwN_lt_size h4'; rw [UInt64.toNat_add]; simp <;> omega
  have hz' : z = UInt64.ofNat o' := by
    rw [hz, hrd, hy, hos, hvw.1, hv3, (iwN_rdW h3' (by have := iwN_lt_size h3'; omega)).1]
  have hw' : w = UInt64.ofNat l' := by
    rw [hw, hrd, hy, hos, hvw.1, hv4, (iwN_rdW h4' (by have := iwN_lt_size h4'; omega)).1]
  rw [hz', hw', UInt64.toNat_ofNat_of_lt' (iwN_rdW h3' (by have := iwN_lt_size h3'; omega)).2,
    UInt64.toNat_ofNat_of_lt' (iwN_rdW h4' (by have := iwN_lt_size h4'; omega)).2]
  exact hd

/-! ## The model -/

section model
variable (p : Prog) (n : Nat)

/-- After `rec6`: the record. -/
def cxoK9 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

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

/-- A `[cv, nF]` record decoded below the tops: the constant's pointer, its name word, `nF`. -/
theorem decCN_words {m : Mem} {cA : Word} {x : IConstantVal × Nat} (h : DecB (fun m => decCN m cA.toNat) m x)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    ∃ a : Nat, rdW (m.arr64 IW) cA = UInt64.ofNat a ∧ a + 3 < erTop m ∧
      DecB (fun m => decCVp m a) m x.1 ∧ H (rdW (m.arr64 EREC) (UInt64.ofNat a)) ∧
      decI (rdW (m.arr64 EREC) (UInt64.ofNat a)) = x.1.name ∧
      rdW (m.arr64 IW) (cA + 1) = UInt64.ofNat x.2 ∧ x.2 < 2 ^ 64 ∧ cA.toNat + 1 < iwTop m := by
  have h' : decCN (truncM m) cA.toNat = some x := h
  obtain ⟨⟨a, ha, hcv⟩, hn⟩ := decCN_some h'
  obtain ⟨-, ha'⟩ := rec2IwN_trunc ha
  obtain ⟨hnt, hn'⟩ := rec2IwN_trunc hn
  have ra := iwN_rdW_at (w := cA) (k := 0) (by simpa using ha') hsz
  have rn := iwN_rdW_at (w := cA) (k := 1) hn' hsz
  obtain ⟨hnm, -, hty⟩ := decCV_some (a := erA (truncM m)) (q := a) hcv
  simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hnm hty
  obtain ⟨w0, hw0, -⟩ := hnm
  obtain ⟨w3, hw3, -⟩ := hty
  obtain ⟨-, hw0'⟩ := truncM_er_get hw0
  obtain ⟨h3t, -⟩ := truncM_er_get hw3
  have hcv' : decCVp m a = some x.1 := (show DecB (fun m => decCVp m a) m x.1 from hcv).get (OMono.decCVp _)
  obtain ⟨hnm2, -, -⟩ := decCV_some (a := erA m) (q := a) hcv'
  obtain ⟨w, hw, hwH, hwD⟩ := erH_rdW hnm2 (by have := ra.2; omega)
  refine ⟨a, by simpa using ra.1, h3t, hcv, by rw [hw]; exact hwH, by rw [hw]; exact hwD, by simpa using rn.1, rn.2,
    hnt⟩

/-- A fresh `rec6` record (at or above `b`) of parts stable above `b` decodes stably above `b` as a
`ClassCtor`. -/
theorem rec6_decCC {m m' : Mem} {q : Word} {cvw nFw ko kl tyD tyN : Word} {cv : IConstantVal}
    {kinds : List ClassField} {b : Nat}
    (hget : ∀ j < 6, (m'.arr64 IW)[q.toNat + j]? = [cvw, nFw, ko, kl, tyD, tyN][j]?)
    (hq : q.toNat + 6 ≤ iwTop m') (hb : b ≤ q.toNat) (hg : IWGrow m m')
    (hcv : DecB (fun m => decCVp m cvw.toNat) m cv)
    (hks : SPLA b decCF m ko.toNat kl.toNat kinds) (hD : H tyD) (hN : H tyN) :
    StabA b (fun m => decCC m q.toNat) m' ⟨cv, nFw.toNat, kinds, decI tyD, decI tyN⟩ := by
  intro m'' hA
  have hA0 : AgreeA b m m'' := (AgreeA.of_grow hg).trans hA
  have hw : ∀ j (hj : j < 6), iwN m'' (q.toNat + j) =
      some ([cvw, nFw, ko, kl, tyD, tyN][j]'(by simpa using hj)).toNat := fun j hj => by
    rw [hA.iwN (by omega) (by omega)]
    simp only [iwN, nat?, iwA]
    rw [hget j hj, List.getElem?_eq_getElem (by simp; omega)]; rfl
  have h0 := hw 0 (by omega)
  have h1 := hw 1 (by omega)
  have h2 := hw 2 (by omega)
  have h3 := hw 3 (by omega)
  have hhD : (iwH m'' (q.toNat + 4) : Option EIdx) = some (decI tyD) := by
    rw [hA.iwH (by omega) (by omega)]
    simp only [iwH, hd?, iwA]
    rw [hget 4 (by omega)]
    simp [hD]
  have hhN : (iwH m'' (q.toNat + 5) : Option EIdx) = some (decI tyN) := by
    rw [hA.iwH (by omega) (by omega)]
    simp only [iwH, hd?, iwA]
    rw [hget 5 (by omega)]
    simp [hN]
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3
  have e1 : decCVp m'' cvw.toNat = some cv := stabA_decCVp hcv b m'' hA0
  have e3 := hks.stab m'' hA0
  simp only [decCC, decAt, h0, Nat.add_assoc, Nat.reduceAdd, h1, h2, h3, Option.bind_eq_bind,
    Option.bind_some, e1, e3, hhD, hhN]
  rfl

/-- A word of the constant records below their top stays. -/
theorem rdW_er_grow {m m' : Mem} (hg : IWGrow m m') {x : Word} (hi : x.toNat < erTop m) :
    rdW (m'.arr64 EREC) x = rdW (m.arr64 EREC) x := by
  simp only [rdW, hg.2.2.2 _ hi]

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

/-! ## The relational side -/

/-- The lookups of `class_ctor_of`. -/
structure CxoProg (p : Prog) : Prop extends CfaProg p where
  cnf : p.lookup "class_ctor_of_nfs" = some classCtorOfNfs
  cmsg : p.lookup "class_minor_slot_go" = some classMinorSlotGo
  cms : p.lookup "class_minor_slot" = some classMinorSlotL
  cfo : CfoProg p
  erc : p.lookup "er_copy" = some erCopy
  eri : p.lookup "er_to_iw" = some erToIw
  cvl : p.lookup "cv_lps" = some cvLps
  tca : p.lookup "target_ctor_at" = some targetCtorAt
  ipw : p.lookup "inst_pis_with" = some instPisWith
  r6 : p.lookup "rec6" = some rec6
  cxo : p.lookup "class_ctor_of" = some classCtorOfL

/-- The constant's level-parameter slice lies in `EREC` or is empty (`target_ctor_at`'s
hypothesis), at the constant of the `[cv, nF]` record `cA`. -/
def CtorLp (m : Mem) (cA : Word) : Prop :=
  (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cA + 2)).toNat = 0 ∨
  (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cA + 1)).toNat + (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cA + 2)).toNat ≤
    (m.arr64 EREC).size

section rel
variable {p : Prog} (P : CxoProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
include P

end rel

end L.Ind
