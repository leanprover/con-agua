import ConAgua.Arena.RecGenSpec25
import ConAgua.Arena.InferBodyIntern

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
  cases hh : classMinorSlotHit (m.arr64 IW) (rdW (m.arr64 IW) (off + j)) c cc with
  | none => rw [classMinorSlotGoW_oob2 n m off rem j c cc cnt rS rOff rLen hrem hp hh] at h; cases h
  | some b =>
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
  cases hg : classMinorSlotGoW n m (rdW (m.arr64 IW) rd) (rdW (m.arr64 IW) (rd + 1)) 0 c cc 0 0 0 0 with
  | none => rw [hg] at h; cases h
  | some xyzw =>
  obtain ⟨x, y, z, w⟩ := xyzw
  rw [hg] at h
  by_cases hx : x ≠ 1
  · simp [hx] at h
  simp only [hx, if_false, Option.some.injEq] at h
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
  simp only [cxoK8]; rw [if_pos h]
theorem cxoK8_ok (h : ¬ r.headD 0 = 0) : cxoK8 p n cv cA ko kl e0 (some (r, m)) =
    cxoK9 (callW p n "rec6" [cv, rdW (m.arr64 IW) (cA + 1), ko, kl, r.tail.headD 0, rdW (m.arr64 IW) (e0 + 4)] m) := by
  simp only [cxoK8]; rw [if_neg h]
theorem cxoK7_some : cxoK7 p n mw cv cA ko kl e0 (some (r, m)) = cxoK8 p n cv cA ko kl e0
    (callW p n "inst_pis_with" [rdW (m.arr64 IW) (mw + 2), rdW (m.arr64 IW) (mw + 3), r.headD 0] m) := rfl
theorem cxoK6_some : cxoK6 p n mw cv cA ko kl e0 (some (r, m)) =
    cxoK7 p n mw cv cA ko kl e0 (callW p n "target_ctor_at" [mw, cv] m) := rfl
theorem cxoK5_some : cxoK5 p n vis q fto ftl mo ml mw cv cA fvo fvl eo el e0 (some (r, m)) =
    cxoK6 p n mw cv cA (r.headD 0) (r.tail.headD 0) e0
      (callW p n "class_fields_agree" [vis, q, fto, ftl, mo, ml, fvo, fvl, eo, el, 0, r.headD 0, r.tail.headD 0] m) := rfl
theorem cxoK4_bad (h : r.headD 0 = 0) :
    cxoK4 p n vis q fto ftl mo ml mw cv cA io il eo el e0 (some (r, m)) = none := by
  simp only [cxoK4]; rw [if_pos h]
theorem cxoK4_ok (h : ¬ r.headD 0 = 0) : cxoK4 p n vis q fto ftl mo ml mw cv cA io il eo el e0 (some (r, m)) =
    cxoK5 p n vis q fto ftl mo ml mw cv cA (r.tail.headD 0) (r.tail.tail.headD 0) eo el e0
      (callW p n "class_fields_of" [q, io, il, 0, r.tail.headD 0, r.tail.tail.headD 0] m) := by
  simp only [cxoK4]; rw [if_neg h]
theorem cxoK3_some : cxoK3 p n vis q fto ftl mo ml mw cv cA eo el e0 (some (r, m)) =
    cxoK4 p n vis q fto ftl mo ml mw cv cA (r.tail.headD 0) (r.tail.tail.headD 0) eo el e0
      (callW p n "open_pis_at_fvars_f" [rdW (m.arr64 IW) (cA + 1), rdW (m.arr64 IW) (e0 + 4),
        rdW (m.arr64 IW) (q + 4) + rdW (m.arr64 IW) (q + 1)] m) := rfl
theorem cxoK2_bad (h : r.tail.headD 0 = 0) : cxoK2 p n vis q fto ftl rd mo ml c mw cv cA (some (r, m)) = none := by
  simp only [cxoK2]; rw [if_pos h]
theorem cxoK2_ok (h : ¬ r.tail.headD 0 = 0) : cxoK2 p n vis q fto ftl rd mo ml c mw cv cA (some (r, m)) =
    cxoK3 p n vis q fto ftl mo ml mw cv cA (r.headD 0) (r.tail.headD 0) (rdW (m.arr64 IW) (r.headD 0))
      (callW p n "class_minor_slot" [rd, c, rdW (m.arr64 EREC) cv] m) := by
  simp only [cxoK2]; rw [if_neg h]
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
  cases h1 : cvLpsW n m c with
  | none => rw [h1] at h; simp [tcK1] at h
  | some x =>
  obtain ⟨r1, m1⟩ := x
  rw [h1] at h
  simp only [tcK1] at h
  refine (posmemo_cvLpsW_mfr h1).trans ?_
  cases h2 : cR n "inst_lp_fast" [CWF, r1.headD 0, r1.tail.headD 0, rdW (m.arr64 IW) (M + 1),
      rdW (m1.arr64 EREC) (c + 3)] m1 with
  | none => rw [h2] at h; simp [tcK2] at h
  | some y =>
  obtain ⟨r2, m2⟩ := y
  rw [h2] at h
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
    cases n with
    | zero => simp [instW] at h
    | succ n =>
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

/-- **`class_ctor_of`'s model refines `classCtorOf`.** -/
theorem cxoW_ok (n : Nat) {m m' : Mem} {a : AState} {vis q fto ftl rd mo ml c cA : Word} {r : List Word}
    {bs : BlockShape} {formerTys : List EIdx} {R : ClassRead} {ms : List TargetMajor}
    {cA' : IConstantVal × Nat}
    (h : cxoW p n m vis q fto ftl rd mo ml c cA = some (r, m')) (hS : StageR dn vis fe m a)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hR : DecB (fun m => decCR m rd.toNat) m R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hcA : DecB (fun m => decCN m cA.toNat) m cA') (hlp : CtorLp m cA) (hnpk : bs.nP + bs.k < 2 ^ 64)
    (hsz5 : (m.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR m) :
    ∃ x a', (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cA').run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ StabA (iwTop m) (fun m => decCC m (r.headD 0).toNat) m' x ∧
        RcMR m' := by
  have hsz := hS.2.2.2.1
  have hbsD : DecB (fun m => decBS m q.toNat) m bs := hbs.1
  have hq9 : q.toNat + 9 ≤ iwTop m := by have := hbs.ptop; omega
  have hq64 := hS.lt64 hq9
  unfold cxoW at h
  -- `target_major_at`
  cases c1 : callW p n "target_major_at" [mo, ml, c] m with
  | none => rw [c1] at h; cases h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [c1, cxoK1_some] at h
  obtain ⟨s1, hs1, -, hw1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (targetMajorAt_spec p P.ha P.pw P.mtm P.tmd P.tma P.na n _ mo ml c) c1
  simp only at hs1 hw1; subst hs1
  obtain ⟨tm, a1, run1, hS1, hg1, hTM⟩ := rec3TMA_sim dn vis fe n m a mo ml c ms hS hms hmsb _ hw1
  dsimp only at hS1 hg1 hTM
  have hP1 := hP.fr (tmaW_mfr hw1)
  have hk1 := callW_keepW c1
  have hsz1 := hS1.2.2.2.1
  obtain ⟨⟨no, nl, h9, h10, hno, hnl, hnfs⟩, hds, hmw13⟩ := decTM_slices hTM hsz1
  obtain ⟨ca, hca, hca3, hcv, hnmH, hnmD, hnF, hnFb, -⟩ := decCN_words (hcA.grow (decCN_mono _) hg1) hsz1
  obtain ⟨cam, hcam, hca3m, -, -, -, -, -, hcAt⟩ := decCN_words hcA hsz
  rw [h9, h10, hca] at h
  -- `class_ctor_of_nfs`
  cases c2 : callW p n "class_ctor_of_nfs" [UInt64.ofNat no, UInt64.ofNat nl,
      rdW (s1.mem.arr64 EREC) (UInt64.ofNat ca)] s1.mem with
  | none => rw [c2] at h; simp [cxoK2] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [c2] at h
  cases n with
  | zero =>
    obtain ⟨_, _, hf⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩) (invoke_exec_zero p _ _ _) c2
    exact hf.elim
  | succ n =>
  obtain ⟨s2, hs2, -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (cnf_spec p P.ha P.cnf n _ (UInt64.ofNat no) (UInt64.ofNat nl) (rdW (s1.mem.arr64 EREC) (UInt64.ofNat ca))) c2
  simp only at hs2 hw2; subst hs2
  obtain ⟨hS2, hg2, hf2, hes⟩ := cnfF_ok _ _ _ tm.nfs n hw2 hS1 (by
    rw [UInt64.toNat_ofNat_of_lt' hno, UInt64.toNat_ofNat_of_lt' hnl]; exact hnfs) hnmH
  rw [hnmD] at hes
  have hP2 := hP1.fr hf2
  have hk2 := callW_keepW c2
  have hg12 := hg1.trans hg2
  -- the first entry
  by_cases hel : r2.tail.headD 0 = 0
  · rw [cxoK2_bad (h := hel)] at h; cases h
  rw [cxoK2_ok (h := hel)] at h
  -- the class's entries: the first
  obtain ⟨e0', es', hes_eq, he0, -⟩ := hes.uncons hel hS2.2.2.2.1
  rw [hes_eq] at hes
  have hsz2 := hS2.2.2.2.1
  generalize hE0 : rdW (s2.mem.arr64 IW) (r2.headD 0) = e0w at h he0
  obtain ⟨htyH, htyD⟩ := decNCN_ty he0 hsz2
  have hca64 : ca < 2 ^ 64 := by
    have := (rdW (s1.mem.arr64 CTL) 129).toNat_lt; simp only [erTop] at hca3; omega
  have hcaT : (UInt64.ofNat ca : Word).toNat = ca := UInt64.toNat_ofNat_of_lt' hca64
  have hcaeq : cam = ca := by
    have hcm64 : cam < 2 ^ 64 := by
      have := (rdW (m.arr64 CTL) 129).toNat_lt; simp only [erTop] at hca3m; omega
    have e := hca
    rw [rdW_grow hg1 (by omega), hcam] at e
    have := congrArg UInt64.toNat e
    rwa [UInt64.toNat_ofNat_of_lt' hcm64, hcaT] at this
  subst cam
  have hER2 : rdW (s2.mem.arr64 EREC) (UInt64.ofNat ca) = rdW (s1.mem.arr64 EREC) (UInt64.ofNat ca) :=
    rdW_er_grow hg2 (by rw [hcaT]; omega)
  rw [hER2] at h
  -- `class_minor_slot`
  cases c3 : callW p (n + 1) "class_minor_slot" [rd, c, rdW (s1.mem.arr64 EREC) (UInt64.ofNat ca)] s2.mem with
  | none => rw [c3] at h; simp [cxoK3] at h
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [c3, cxoK3_some] at h
  obtain ⟨s3, hs3, -, hm3, hw3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (classMinorSlot_spec p P.cmsg P.cms n _ rd c (rdW (s1.mem.arr64 EREC) (UInt64.ofNat ca))) c3
  simp only at hs3 hm3 hw3; subst hs3
  rw [hm3] at h
  have hsz5' : (s2.mem.arr64 IW).size + 5 < 2 ^ 64 := by rw [hk2 IW, hk1 IW]; exact hsz5
  obtain ⟨s, ihs, hhits, -, hihs⟩ := cms_decB n hw3 (hR.grow (decCR_mono _) hg12) hnmH hsz5'
  have hrun3 : (ConRon.Arena.classMinorSlot R c.toNat cA'.1.name).run a1 = .ok ((s, ihs), a1) := by
    have hits := hitsFrom_eq c.toNat (decI (rdW (s1.mem.arr64 EREC) (UInt64.ofNat ca))) 0 R.slots
    simp only [Nat.zero_add] at hits
    rw [← hnmD]
    simp only [ConRon.Arena.classMinorSlot]
    erw [hits, hhits]
    rfl
  -- `open_pis_at_fvars_f`
  obtain ⟨ca2, hca2, -, -, -, -, hnF2, -, -⟩ := decCN_words (hcA.grow (decCN_mono _) hg12) hsz2
  have hq4 : rdW (s2.mem.arr64 IW) (q + 4) = UInt64.ofNat bs.nP := (partsShapeWords hg12 hbsD hq9).1
  have hq1 : rdW (s2.mem.arr64 IW) (q + 1) = UInt64.ofNat bs.k := by
    have e : (q + 1 : Word) = UInt64.ofNat (q.toNat + 1) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp <;> omega
    rw [e]; exact decBS_k ((hbsD.grow (decBS_mono _) hg12).get (decBS_mono _)) (by omega)
  have hsum : (UInt64.ofNat bs.nP + UInt64.ofNat bs.k : Word) = UInt64.ofNat (bs.nP + bs.k) := by
    apply UInt64.toNat_inj.mp; simp [UInt64.toNat_add] <;> omega
  rw [hnF2, hq4, hq1, hsum] at h
  cases c4 : callW p (n + 1) "open_pis_at_fvars_f" [UInt64.ofNat cA'.2, rdW (s2.mem.arr64 IW) (e0w + 4),
      UInt64.ofNat (bs.nP + bs.k)] s2.mem with
  | none => rw [c4] at h; simp [cxoK4] at h
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  rw [c4] at h
  obtain ⟨s4, hs4, -, hw4⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (stubM_spec p "open_pis_at_fvars_f" (n + 1) _ [UInt64.ofNat cA'.2, rdW (s2.mem.arr64 IW) (e0w + 4),
      UInt64.ofNat (bs.nP + bs.k)]) c4
  simp only at hs4 hw4; subst hs4
  obtain ⟨ox, a4, run4, hS4, hg4, hd4⟩ := openPisAtFvarsF_spec dn vis fe _ _ (UInt64.ofNat (bs.nP + bs.k)) htyH
    _ _ a1 r4 hw4 hS2
  have hP4 := hP2.fr (MFr.ofStub hw4)
  rw [UInt64.toNat_ofNat_of_lt' hnFb, UInt64.toNat_ofNat_of_lt' hnpk, htyD] at run4
  have hk4 := callW_keepW c4
  rcases ox with _ | ⟨fvs, body⟩
  · have h0 : r4.headD 0 = 0 := hd4
    rw [cxoK4_bad (h := h0)] at h; cases h
  obtain ⟨h41, ⟨hdl, hbl⟩, -⟩ := hd4
  have h0 : ¬ r4.headD 0 = 0 := by rw [h41]; decide
  rw [cxoK4_ok (h := h0)] at h
  simp only [getD_one, show (1 + 1 : Nat) = 2 from rfl, getD_two] at hdl hbl
  have hg24 := hg4
  have hg14 := hg12.trans hg4
  -- `class_fields_of`
  obtain ⟨mp0, hM0⟩ := hP4.pos.no
  cases c5 : callW p (n + 1) "class_fields_of" [q, r3.tail.headD 0, r3.tail.tail.headD 0, 0, r4.tail.headD 0,
      r4.tail.tail.headD 0] s4.mem with
  | none => rw [c5] at h; simp [cxoK5] at h
  | some x5 =>
  obtain ⟨r5, m5⟩ := x5
  rw [c5, cxoK5_some] at h
  have hihB := hihs.grow (OMono.decPL (fun q => decNN_mono q) _ _) hg24
  have hib : (r3.tail.headD 0).toNat + (r3.tail.tail.headD 0).toNat < 2 ^ 64 := by
    rcases decB_decPL_bound hihB with h0 | h0
    · rw [h0]; exact (r3.tail.headD 0).toNat_lt
    · exact hS4.lt64 h0
  obtain ⟨s5, hs5, -, hok5, hS5, hg5, hsp5, ⟨mp5, hM5⟩, hf5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (classFieldsOf_refines p P.cfo (n + 1) _ a4 dn vis fe q (r3.tail.headD 0) (r3.tail.tail.headD 0) 0
      (r4.tail.headD 0) (r4.tail.tail.headD 0) bs ihs fvs mp0 hS4 (hbs.grow hg14)
      (DecB.stab (OMono.decPL (fun q => decNN_mono q) _ _) hihB) hib hdl hbl
      (by simpa using (r4.tail.tail.headD 0).toNat_lt) hM0) c5
  simp only at hs5 hS5 hg5 hsp5 hM5 hf5; subst hs5
  have hP5 := hP4.setNo hf5 ⟨mp5, hM5⟩
  have run5 := AM.run_of_ok _ a4 hok5
  generalize hx5 : AM.res (ConRon.Arena.classFieldsOf bs ihs (0 : Word).toNat fvs) a4 = kinds at run5 hsp5
  generalize ha5 : AM.st (ConRon.Arena.classFieldsOf bs ihs (0 : Word).toNat fvs) a4 = a5 at run5 hS5
  have hg15 := hg14.trans hg5
  have hk5 := callW_keepW c5
  -- `class_fields_agree`
  cases c6 : callW p (n + 1) "class_fields_agree" [vis, q, fto, ftl, mo, ml, r4.tail.headD 0,
      r4.tail.tail.headD 0, r2.headD 0, r2.tail.headD 0, 0, r5.headD 0, r5.tail.headD 0] s5.mem with
  | none => rw [c6] at h; simp [cxoK6] at h
  | some x6 =>
  obtain ⟨r6, m6⟩ := x6
  rw [c6, cxoK6_some] at h
  obtain ⟨s6, hs6, -, hok6, hS6, hg6, hP6⟩ := triple_of_callW (s₀ := ⟨s5.mem, Locals.init []⟩)
    (classFieldsAgree_refines P.toCfaProg (n + 1) _ a5 dn fe vis q fto ftl mo ml (r4.tail.headD 0)
      (r4.tail.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) 0 (r5.headD 0) (r5.tail.headD 0) bs formerTys ms fvs
      (e0' :: es') kinds hS5 (hbs.grow hg15) (by rw [decHL_grow hg15 hftb]; exact hft)
      (Nat.le_trans hftb hg15.1) (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg15)
      hmsb (by rw [decHL_grow hg5 hbl]; exact hdl) (Nat.le_trans hbl hg5.1)
      (hes.grow (fun q => decNCN_mono q) (hg4.trans hg5)) hsp5.toSPL
      (by simpa using (r5.tail.headD 0).toNat_lt) hP5) c6
  simp only at hs6 hS6 hg6 hP6; subst hs6
  have run6 := AM.run_of_ok _ a5 hok6
  generalize ha6 : AM.st (ConRon.Arena.classFieldsAgree V fe bs formerTys ms fvs (e0' :: es') (0 : Word).toNat
    kinds) a5 = a6 at run6 hS6
  have hg16 := hg15.trans hg6
  have hk6 := callW_keepW c6
  -- `target_ctor_at`
  cases c7 : callW p (n + 1) "target_ctor_at" [r1.headD 0, UInt64.ofNat ca] s6.mem with
  | none => rw [c7] at h; simp [cxoK7] at h
  | some x7 =>
  obtain ⟨r7, m7⟩ := x7
  rw [c7, cxoK7_some] at h
  have hgm6 := hg16
  have hg26 : IWGrow s1.mem s6.mem := hg2.trans (hg4.trans (hg5.trans hg6))
  have hca3' : ca + 3 < 2 ^ 64 := by
    have := (rdW (s1.mem.arr64 CTL) 129).toNat_lt; simp only [erTop] at hca3; omega
  have hkm6 : KeepW m s6.mem := hk1.trans (hk2.trans (hk4.trans (hk5.trans hk6)))
  have hlp6 : (rdW (s6.mem.arr64 EREC) (UInt64.ofNat ca + 2)).toNat = 0 ∨
      (rdW (s6.mem.arr64 EREC) (UInt64.ofNat ca + 1)).toNat +
      (rdW (s6.mem.arr64 EREC) (UInt64.ofNat ca + 2)).toNat ≤ (s6.mem.arr64 EREC).size := by
    have e1 : (UInt64.ofNat ca + 1 : Word).toNat = ca + 1 := by rw [UInt64.toNat_add]; simp <;> omega
    have e2 : (UInt64.ofNat ca + 2 : Word).toNat = ca + 2 := by rw [UInt64.toNat_add]; simp <;> omega
    rw [rdW_er_grow hgm6 (by rw [e2]; omega), rdW_er_grow hgm6 (by rw [e1]; omega), hkm6 EREC]
    have := hlp; simp only [CtorLp] at this; rw [hcam] at this; exact this
  obtain ⟨s7, hs7, -, hok7, hS7, hg7, ht7H, ht7D⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (targetCtorAt_refines p P.ha P.erc P.eri P.cvl P.tca n _ a6 dn vis fe (r1.headD 0) (UInt64.ofNat ca) tm cA'.1
      hS6 ((hTM.grow (decTM_mono _) hg26).get (decTM_mono _))
      (by rw [hcaT]; exact (hcv.grow (OMono.decCVp _) hg26).get (OMono.decCVp _)) hmw13 (by rw [hcaT]; omega)
      hlp6) c7
  simp only at hs7 hS7 hg7 ht7H ht7D; subst hs7
  have run7 := AM.run_of_ok _ a6 hok7
  rw [← ht7D] at run7
  generalize ha7 : AM.st (ConRon.Arena.targetCtorAt tm cA'.1) a6 = a7 at run7 hS7
  obtain ⟨s7', hs7', -, hw7⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (targetCtorAt_spec p P.ha P.erc P.eri P.cvl P.tca stubCall (stubCall_spec p) n _ (r1.headD 0)
      (UInt64.ofNat ca)) c7
  simp only at hs7' hw7; rw [hs7'] at hw7
  have hP7 := hP6.fr (tcW_mfr IlpFr.stub hw7)
  have hk7 := callW_keepW c7
  have hg17 := hg16.trans hg7
  -- `inst_pis_with`
  have hsz7 := hS7.2.2.2.1
  obtain ⟨-, hds7, -⟩ := decTM_slices (hTM.grow (decTM_mono _) (hg26.trans hg7)) hsz7
  cases c8 : callW p (n + 1) "inst_pis_with" [rdW (s7.mem.arr64 IW) (r1.headD 0 + 2),
      rdW (s7.mem.arr64 IW) (r1.headD 0 + 3), r7.headD 0] s7.mem with
  | none => rw [c8] at h; simp [cxoK8] at h
  | some x8 =>
  obtain ⟨r8, m8⟩ := x8
  rw [c8] at h
  obtain ⟨s8, hs8, -, hw8⟩ := triple_of_callW (s₀ := ⟨s7.mem, Locals.init []⟩)
    (instPisWith_spec p P.hv P.ipw P.hi1 (n + 1) _ _ _ _) c8
  simp only at hs8 hw8; subst hs8
  obtain ⟨ox, a8, run8, hS8, hg8, hd8⟩ := instW_ok0 (n + 1) hw8 hS7 ht7H hds7
  have hP8 := hP7.fr (instW_mfr _ _ _ _ _ _ _ hw8)
  have hg18 := hg17.trans hg8
  rcases ox with _ | tyD
  · have h0 : r8.headD 0 = 0 := hd8
    rw [cxoK8_bad (h := h0)] at h; cases h
  obtain ⟨h81, h8H, h8D⟩ := hd8
  have h0 : ¬ r8.headD 0 = 0 := by rw [h81]; decide
  rw [cxoK8_ok (h := h0)] at h
  -- `rec6`
  have hsz8 := hS8.2.2.2.1
  obtain ⟨ca8, hca8, -, hcv8, -, -, hnF8, -, -⟩ := decCN_words (hcA.grow (decCN_mono _) hg18) hsz8
  obtain ⟨hty8H, hty8D⟩ := decNCN_ty (he0.grow (decNCN_mono _) (hg4.trans (hg5.trans (hg6.trans (hg7.trans hg8)))))
    hsz8
  rw [hnF8] at h
  cases c9 : callW p (n + 1) "rec6" [UInt64.ofNat ca, UInt64.ofNat cA'.2, r5.headD 0, r5.tail.headD 0,
      r8.tail.headD 0, rdW (s8.mem.arr64 IW) (e0w + 4)] s8.mem with
  | none => rw [c9] at h; simp [cxoK9] at h
  | some x9 =>
  obtain ⟨r9, m9⟩ := x9
  rw [c9, cxoK9_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s9, hs9, -, hw9⟩ := triple_of_callW (s₀ := ⟨s8.mem, Locals.init []⟩)
    (rec6_specW p P.ha P.r6 (n + 1) _ _ _ _ _ _ _) c9
  simp only at hs9 hw9; subst hs9
  obtain ⟨hS9, hg9, hq9', ht9, hget9⟩ := posRecW_stage hw9 hS8 (by simp)
  have hP9 := hP8.fr (posRecW_mfr hw9)
  refine ⟨⟨cA'.1, cA'.2, kinds, tyD, e0'.ty⟩, a8, ?_, hS9, hg18.trans hg9, ?_, hP9⟩
  · simp only [ConRon.Arena.classCtorOf, StateT.run_bind, run1, except_ok_bind]
    rw [hes_eq]
    simp only [show (0 : Word).toNat = 0 from rfl] at run5 run6
    simp only [StateT.run_bind, hrun3, except_ok_bind, run4, run5, run6, run7, run8]
    rfl
  · have := rec6_decCC (m := s8.mem) (q := r9.headD 0) (cvw := UInt64.ofNat ca) (nFw := UInt64.ofNat cA'.2)
      (ko := r5.headD 0) (kl := r5.tail.headD 0) (tyD := r8.tail.headD 0) (tyN := rdW (s8.mem.arr64 IW) (e0w + 4))
      (fun j hj => by simpa using hget9 j (by simpa using hj)) (by simp at ht9; omega)
      (by rw [hq9']; exact hg18.1) hg9
      (by rw [hcaT]; exact hcv.grow (OMono.decCVp _) (hg26.trans (hg7.trans hg8)))
      ((hsp5.mono hg14.1).grow (AgreeA.of_grow (hg6.trans (hg7.trans hg8)))) h8H hty8H
    simp only [List.headD_cons]
    rw [h8D, hty8D, UInt64.toNat_ofNat_of_lt' hnFb] at this
    exact this

end rel


/-- **`class_ctor_of` refines `classCtorOf`** (through the `open_pis_at_fvars_f`, `fvar_type_d`
stubs and `target_k53`'s contracts): the class's shape (`BSOK`, its parameter count plus member
count word-sized), former types, the class reading, the classes and the `[cv, nF]` record decoded
below the tops, the constant's level-parameter slice in `EREC` (`CtorLp`), the pool's size `+ 5`
word-sized (`class_minor_slot`), the walk memos well formed; the `ClassCtor` record decoded stably
above the entry's top (`StabA`). Under `StageR`; the census link is `classCtorOf_refinesC`
(`IndT/RecGen27`). -/
theorem classCtorOf_refines {p : Prog} (P : CxoProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl rd mo ml c cA : Word) (bs : BlockShape)
    (formerTys : List EIdx) (R : ClassRead) (ms : List TargetMajor) (cA' : IConstantVal × Nat)
    (hS : StageR dn vis fe s₀.mem a₀) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hR : DecB (fun m => decCR m rd.toNat) s₀.mem R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) s₀.mem ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hcA : DecB (fun m => decCN m cA.toNat) s₀.mem cA') (hlp : CtorLp s₀.mem cA) (hnpk : bs.nP + bs.k < 2 ^ 64)
    (hsz5 : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_ctor_of" [vis, q, fto, ftl, rd, mo, ml, c, cA]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cA') a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cA') a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      StabA (iwTop s₀.mem) (fun m => decCC m (r.headD 0).toNat) s'.mem
        (AM.res (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cA') a₀) ∧ RcMR s'.mem; ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
  refine triple_post (cxo_spec p P.cxo n s₀ vis q fto ftl rd mo ml c cA) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', run, hS', hg, hd, hP'⟩ := cxoW_ok P dn fe n hm hS hbs hft hftb hR hms hmsb hcA hlp hnpk hsz5 hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hd, hP'⟩

end L.Ind
