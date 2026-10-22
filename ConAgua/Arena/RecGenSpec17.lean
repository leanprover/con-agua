import ConAgua.Arena.RecGenSpec16
import ConAgua.Arena.RecCheckSpec6
import ConAgua.Arena.RecCheckSpec5
import ConAgua.Arena.DeclBasisSpec

/-!
# `targetMajorOf`'s outside branch (lane `indproofs3`, helper `indproofs3-pos-cls`)

`target_major_of_outside_closed` (the same closedness test as `class_key_of_closed`, model
`ckc2W`), `target_major_of_outside_occ` (`ds.anyM (nestOcc names 0 0)`, a recursion),
`target_ctors_of` (`nest_container`), and the frames the walk memos need.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `target_major_of_outside_closed` -/

theorem tmoc_spec (p : Prog) (hb : BvbProg p)
    (hp : p.lookup "target_major_of_outside_closed" = some targetMajorOfOutsideClosed) (k : Nat) :
    ∀ (s₀ : St) (o l nP : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "target_major_of_outside_closed" [o, l, nP]
    ⦃fun r s' => LocEq s' s₀ ∧ ckc2W k s₀.mem nP o l = some (r, s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ o l nP; rw [invoke_eq _ hp]; simp only [callFn, targetMajorOfOutsideClosed]
    vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ o l nP
    rw [invoke_eq _ hp]
    simp only [callFn, targetMajorOfOutsideClosed]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        bvarBL_spec p hb k, stubM_spec p "fvar_b" k, ih] <;>
      finish (gen := 20)

/-! ## `target_major_of_outside_occ` -/

def ocK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

mutual
/-- **The model of `target_major_of_outside_occ(no, nl, o, l)`.** -/
def ocW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, no, nl, o, l =>
    if l = 0 then some ([0], m)
    else ocK1 p n no nl o l (callW p n "nest_occ" [no, nl, 0, 0, rdW (m.arr64 IW) o] m)
def ocK1 (p : Prog) (n : Nat) (no nl o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 ≠ 0 then some ([1], m) else ocK2 (ocW p n m no nl (o + 1) (l - 1))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (no nl o l : Word) (r : List Word)
theorem ocW_zero : ocW p 0 m no nl o l = none := by simp [ocW]
theorem ocW_nil (h : l = 0) : ocW p (n + 1) m no nl o l = some ([0], m) := by simp [ocW, h]
theorem ocW_cons (h : l ≠ 0) : ocW p (n + 1) m no nl o l =
    ocK1 p n no nl o l (callW p n "nest_occ" [no, nl, 0, 0, rdW (m.arr64 IW) o] m) := by simp [ocW, h]
theorem ocK1_hit (h : r.headD 0 ≠ 0) : ocK1 p n no nl o l (some (r, m)) = some ([1], m) := by
  simp only [ocK1]; rw [if_pos h]
theorem ocK1_miss (h : ¬ r.headD 0 ≠ 0) : ocK1 p n no nl o l (some (r, m)) = ocK2 (ocW p n m no nl (o + 1) (l - 1)) := by
  simp only [ocK1]; rw [if_neg h]
theorem ocK2_some : ocK2 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms
attribute [ind_grind] ocW_nil ocW_cons ocK1_hit ocK1_miss ocK2_some

theorem oc_spec (p : Prog) (hp : p.lookup "target_major_of_outside_occ" = some targetMajorOfOutsideOcc)
    (n : Nat) : ∀ (s₀ : St) (no nl o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_major_of_outside_occ" [no, nl, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ocW p n s₀.mem no nl o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ no nl o l; rw [invoke_eq _ hp]; simp only [callFn, targetMajorOfOutsideOcc]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ no nl o l
    rw [invoke_eq _ hp]
    simp only [callFn, targetMajorOfOutsideOcc]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "nest_occ", ih] <;>
      finish (gen := 20) [rdW_eq]

/-- The lookups of `nest_occ`. -/
structure NoProg (p : Prog) : Prop where
  hv : p.lookup "e_view" = some eView
  hc : p.lookup "sl_contains" = some slContains
  hf : p.lookup "no_find" = some (memoFindG noSch)
  hput : p.lookup "no_put" = some (memoPutG noSch)
  hgo : p.lookup "nest_occ_go" = some nestOccGo
  hnode : p.lookup "nest_occ_node" = some nestOccNode
  hcl : p.lookup "no_clear" = some (memoClearG noSch)
  hp : p.lookup "nest_occ" = some nestOcc

theorem slR_grow {m m' : Mem} (hg : IWGrow m m') (hT : iwTop m < 2 ^ 64) :
    ∀ {o l : Word} {ws : List Word}, SlR m o l ws → (∀ i < l.toNat, o.toNat + i < iwTop m) → SlR m' o l ws := by
  intro o l ws h
  induction h with
  | nil => intro _; exact SlR.nil
  | @cons o l ws hl _ ih =>
    intro hb
    have hl1 : 1 ≤ l.toNat := by
      rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl
      · omega
    have ho : o.toNat < iwTop m := by have := hb 0 hl1; simpa using this
    have e : rdW (m.arr64 IW) o = rdW (m'.arr64 IW) o := by simp only [rdW]; rw [hg.2.2.1 _ ho]
    rw [e]
    refine SlR.cons hl (ih fun i hi => ?_)
    have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hlm : (l - 1).toNat = l.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hl1))]; simp
    rw [ho1]; rw [hlm] at hi; have := hb (i + 1) (by omega); omega

/-- **`target_major_of_outside_occ`'s model simulates `ds.anyM (nestOcc names 0 0)`.** -/
theorem ocW_sim {p : Prog} (hN : NoProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (no nl : Word) (ws : List Word) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (n : Nat) :
    ∀ (m : Mem) (a : AState) (o l : Word) (ds : List EIdx),
    StageR dn vis fe m a → SlR m no nl ws → (∀ i < nl.toNat, no.toNat + i < iwTop m) →
    decHL m o.toNat l.toNat = some ds → o.toNat + l.toNat ≤ iwTop m → PosMR m →
    Sim (ocW p n m no nl o l) (ds.anyM (fun x => ConRon.Arena.nestOcc (ws.map (fun w => (decI w : NIdx))) 0 0 x)) a
      (fun r b m' a' => (r.headD 0 != 0) = b ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PosMR m') := by
  induction n with
  | zero => intro m a o l ds _ _ _ _ _ _; rw [ocW_zero]; exact Sim.of_none
  | succ n ih =>
  intro m a o l ds hS hws hwsb hds hdsb hP
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  by_cases hl : l = 0
  · rw [ocW_nil p n m no nl o l hl]
    have : ds = [] := by rw [hl] at hds; simpa [decHL, hslice?] using hds.symm
    subst this
    exact Sim.ret ⟨rfl, hS, IWGrow.refl m, hP⟩
  obtain ⟨w, ds', rfl, hw, hw32, hd'⟩ := decHL_cons hds hl (by omega)
  obtain ⟨hsum, -⟩ := toNat_succ_of_lt (by omega : o.toNat + l.toNat < 2 ^ 64) hl
  rw [ocW_cons p n m no nl o l hl, hw, partsAnyM_cons]
  refine Sim.bindK (K := ocK1 p n no nl o l)
    (body := fun r1 m1 => if r1.headD 0 ≠ 0 then some ([1], m1) else ocK2 (ocW p n m1 no nl (o + 1) (l - 1)))
    (by simp [ocK1])
    (fun r m₁ => by
      by_cases h : r.headD 0 ≠ 0
      · rw [ocK1_hit p n m₁ no nl o l r h, if_pos h]
      · rw [ocK1_miss p n m₁ no nl o l r h, if_neg h])
    (Q := fun r b m' a' => (r.headD 0 != 0) = b ∧ a' = a ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PosMR m') ?_ ?_
  · intro r1 m1 e1
    cases n with
    | zero => rw [callW_zero] at e1; cases e1
    | succ k =>
    obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (nestOcc_spec p hN.hv hN.hc hN.hf hN.hput hN.hgo hN.hnode hN.hcl hN.hp k _ no nl 0 0 w) e1
    obtain ⟨mp, hM⟩ := hP.no
    obtain ⟨b, hrun, hb, hM', hS1, hg1, hf1⟩ := noConstW_ok k dn fe vis m s1.mem a no nl 0 0 w _ ws mp hW1 hS hw32 hws
      hwlt hM
    exact ⟨b, a, hrun, hb, rfl, hS1, hg1, hP.setNo hf1 ⟨∅, hM'⟩⟩
  rintro r1 b m1 a1 ⟨hb1, rfl, hS1, hg1, hP1⟩
  cases b with
  | true =>
    have h1 : r1.headD 0 ≠ 0 := by simpa using hb1
    simp only [h1, if_true, ne_eq, not_false_eq_true]
    exact Sim.ret ⟨rfl, hS1, hg1, hP1⟩
  | false =>
    have h1 : ¬ r1.headD 0 ≠ 0 := by simpa using hb1
    rw [if_neg h1]
    simp only [Bool.false_eq_true, if_false]
    refine Sim.post (K := ocK2) (f := fun r => [r.headD 0]) rfl (fun _ _ => rfl)
      (ih m1 a1 (o + 1) (l - 1) ds' hS1 (slR_grow hg1 hT hws hwsb) (fun i hi => Nat.lt_of_lt_of_le (hwsb i hi) hg1.1)
        (by rw [decHL_grow hg1 (by omega)]; exact hd')
        (by have := hg1.1; omega) hP1) ?_
    rintro r b' m' a' ⟨h1, h2, h3, h4⟩
    exact ⟨by simpa using h1, h2, hg1.trans h3, h4⟩

/-! ## `target_ctors_of`, `target_outside_inst`'s frame, the constructors' slice -/

/-- After `nest_container`: its four words. -/
def tcoK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], m)

theorem tcoK_some (r : List Word) (m : Mem) :
    tcoK (some (r, m)) = some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], m) := rfl
attribute [ind_grind] tcoK_some

theorem tco_spec (p : Prog) (hl : NtLook p) (hp : p.lookup "target_ctors_of" = some targetCtorsOf) (k : Nat)
    (s₀ : St) (vis I : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "target_ctors_of" [vis, I]
    ⦃fun r s' => LocEq s' s₀ ∧ tcoK (ntWf k s₀.mem vis I) = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, targetCtorsOf]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, nt_spec' p hl k] <;>
    finish (gen := 20)

theorem toiW_mfr {N : Nat} {m m' : Mem} {vis I us dso dsl : Word} {r : List Word}
    (h : toiW N m vis I us dso dsl = some (r, m')) : MFr [] [] m m' := by
  cases N with
  | zero => simp [toiW] at h
  | succ N =>
  rw [toiW_eq] at h
  unfold toiK1 toiK2 toiK3 toiK4 toiK5 at h
  mfr_auto h [envFindW_mfr, erToIwW_mfr, MFr.ofStub, instW_mfr _ _ _ _ _ _ _, piBW_mfr _ _ _ _ _ _]

/-- **A constructor slice read by `nest_container` is decoded below the tops.** -/
theorem csAt_decB {m : Mem} {o : Nat} {xs : List (IConstantVal × Nat)} (h : CsAt m o xs (· < iwTop m))
    (hb : o + xs.length ≤ iwTop m) : DecB (fun m => decPL m (decCN m) o xs.length) m xs := by
  show decPL (truncM m) (decCN (truncM m)) o xs.length = some xs
  refine decPL_of_get _ xs o fun j hj => ?_
  obtain ⟨w, hw, h0, h1, q, hq, hcv, hn⟩ := h j hj
  have hE : ArrExt (erecP m) (erA (truncM m)) := fun i v hv => by
    have hi : i < erTop m := by
      have := (Array.getElem?_eq_some_iff.mp hv).1
      simp only [erecP, Array.size_extract] at this
      have : erecTop m = erTop m := rfl
      omega
    rw [truncM_er_eq hi]; rw [erecP_getE hi] at hv; exact hv
  refine ⟨w.toNat, by rw [iwN_truncM (by omega)]; simp [iwN, nat?, iwA, hw], ?_⟩
  simp only [decCN, decCVp, bind, Option.bind, iwN_truncM h0, iwN_truncM h1, hq, hn, hE.decCV hcv]
  rfl

/-! ## `target_major_of_outside` -/

def tmtK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
def tmtK2 (p : Prog) (n : Nat) (I us dso dsl cso csl pfo pfl : Word) (r1 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 ≠ 2 then none
      else tmtK3 (callW p n "mk_target_major" [I, us, dso, dsl, dsl, r1.headD 0, cso, csl, 0, 0, 0, pfo, pfl] m)
def tmtK1 (p : Prog) (n : Nat) (pp I us dso dsl cso csl pfo pfl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => tmtK2 p n I us dso dsl cso csl pfo pfl r
      (callW p n "lvl_eq_c" [r.tail.headD 0, rdW (m.arr64 IW) (pp + 6)] m)

/-- **The model of `target_major_of_outside_tail`** at exec fuel `n + 1`. -/
def tmtW (p : Prog) (n : Nat) (m : Mem) (vis pp pfo pfl I us dso dsl cso csl : Word) : Option (List Word × Mem) :=
  tmtK1 p n pp I us dso dsl cso csl pfo pfl (callW p n "target_outside_inst" [vis, I, us, dso, dsl] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (pp I us dso dsl cso csl pfo pfl : Word) (r r1 : List Word)
theorem tmtK1_some : tmtK1 p n pp I us dso dsl cso csl pfo pfl (some (r, m)) =
    tmtK2 p n I us dso dsl cso csl pfo pfl r (callW p n "lvl_eq_c" [r.tail.headD 0, rdW (m.arr64 IW) (pp + 6)] m) := rfl
theorem tmtK2_some : tmtK2 p n I us dso dsl cso csl pfo pfl r1 (some (r, m)) =
    if r.headD 0 ≠ 2 then none
      else tmtK3 (callW p n "mk_target_major" [I, us, dso, dsl, dsl, r1.headD 0, cso, csl, 0, 0, 0, pfo, pfl] m) := rfl
theorem tmtK3_some : tmtK3 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms
attribute [ind_grind] tmtK1_some tmtK2_some tmtK3_some

theorem tmt_spec (p : Prog) (hp : p.lookup "target_major_of_outside_tail" = some targetMajorOfOutsideTail)
    (n : Nat) (s₀ : St) (vis pp pfo pfl I us dso dsl cso csl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "target_major_of_outside_tail" [vis, pp, pfo, pfl, I, us, dso, dsl, cso, csl]
    ⦃fun r s' => LocEq s' s₀ ∧ tmtW p n s₀.mem vis pp pfo pfl I us dso dsl cso csl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, targetMajorOfOutsideTail]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "target_outside_inst", callW_spec p n "lvl_eq_c", callW_spec p n "mk_target_major"] <;>
    finish (gen := 40) (instances := 20000) [tmtW, rdW_eq]

def tmoK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
def tmoK3 (p : Prog) (n : Nat) (vis pp I us ao pfo pfl : Word) (r2 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
      else tmoK4 (callW p n "target_major_of_outside_tail" [vis, pp, pfo, pfl, I, us, ao, r2.tail.headD 0,
        r2.tail.tail.headD 0, r2.tail.tail.tail.headD 0] m)
def tmoK2b (p : Prog) (n : Nat) (vis pp I us ao pfo pfl mno mnl : Word) (r2 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
      else tmoK3 p n vis pp I us ao pfo pfl r2 (callW p n "target_major_of_outside_occ" [mno, mnl, ao, r2.tail.headD 0] m)
def tmoK2 (p : Prog) (n : Nat) (vis pp I us ao al pfo pfl mno mnl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else if al < r.tail.headD 0 then none
      else tmoK2b p n vis pp I us ao pfo pfl mno mnl r (callW p n "target_major_of_outside_closed"
        [ao, r.tail.headD 0, rdW (m.arr64 IW) (pp + 4)] m)
def tmoK1 (p : Prog) (n : Nat) (vis pp I us ao al pfo pfl mno mnl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if I = r.headD 0 then none
      else tmoK2 p n vis pp I us ao al pfo pfl mno mnl (callW p n "target_ctors_of" [vis, I] m)

/-- **The model of `target_major_of_outside`** at exec fuel `n + 1`. -/
def tmoW (p : Prog) (n : Nat) (m : Mem) (vis pp pfo pfl I us ao al mno mnl : Word) : Option (List Word × Mem) :=
  tmoK1 p n vis pp I us ao al pfo pfl mno mnl (callW p n "pin_at" [47] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis pp I us ao al pfo pfl mno mnl : Word) (r r2 : List Word)
theorem tmoK1_some : tmoK1 p n vis pp I us ao al pfo pfl mno mnl (some (r, m)) =
    if I = r.headD 0 then none
      else tmoK2 p n vis pp I us ao al pfo pfl mno mnl (callW p n "target_ctors_of" [vis, I] m) := rfl
theorem tmoK2_some : tmoK2 p n vis pp I us ao al pfo pfl mno mnl (some (r, m)) =
    if r.headD 0 = 0 then none else if al < r.tail.headD 0 then none
      else tmoK2b p n vis pp I us ao pfo pfl mno mnl r (callW p n "target_major_of_outside_closed"
        [ao, r.tail.headD 0, rdW (m.arr64 IW) (pp + 4)] m) := rfl
theorem tmoK2b_some : tmoK2b p n vis pp I us ao pfo pfl mno mnl r2 (some (r, m)) =
    if r.headD 0 = 0 then none
      else tmoK3 p n vis pp I us ao pfo pfl r2 (callW p n "target_major_of_outside_occ" [mno, mnl, ao, r2.tail.headD 0] m) := rfl
theorem tmoK3_some : tmoK3 p n vis pp I us ao pfo pfl r2 (some (r, m)) =
    if r.headD 0 = 0 then none
      else tmoK4 (callW p n "target_major_of_outside_tail" [vis, pp, pfo, pfl, I, us, ao, r2.tail.headD 0,
        r2.tail.tail.headD 0, r2.tail.tail.tail.headD 0] m) := rfl
theorem tmoK4_some : tmoK4 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms
attribute [ind_grind] tmoK1_some tmoK2_some tmoK2b_some tmoK3_some tmoK4_some

theorem tmo_spec (p : Prog) (hp : p.lookup "target_major_of_outside" = some targetMajorOfOutside) (n : Nat)
    (s₀ : St) (vis pp pfo pfl I us ao al mno mnl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "target_major_of_outside" [vis, pp, pfo, pfl, I, us, ao, al, mno, mnl]
    ⦃fun r s' => LocEq s' s₀ ∧ tmoW p n s₀.mem vis pp pfo pfl I us ao al mno mnl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, targetMajorOfOutside]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_at", callW_spec p n "target_ctors_of", callW_spec p n "target_major_of_outside_closed",
      callW_spec p n "target_major_of_outside_occ", callW_spec p n "target_major_of_outside_tail"] <;>
    finish (gen := 40) (instances := 20000) [tmoW, rdW_eq]

/-- The lookups of `target_major_of_outside_tail`. -/
structure TmtProg (p : Prog) : Prop where
  toi : ToiProg p
  mkTm : p.lookup "mk_target_major" = some mkTargetMajor
  tail : p.lookup "target_major_of_outside_tail" = some targetMajorOfOutsideTail

/-- **`target_major_of_outside_tail`'s model simulates the outside branch's tail.** -/
theorem tmtW_sim {p : Prog} (hP : TmtProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (n : Nat) {m : Mem} {a : AState} {pp pfo pfl I us dso dsl cso csl : Word} {bs : BlockShape}
    {pfvs ds : List EIdx} {ctors : List (IConstantVal × Nat)}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hq9 : pp.toNat + 9 ≤ iwTop m)
    (hI : H I) (hus : H us) (hds : DecB (fun m => decHL m dso.toNat dsl.toNat) m ds)
    (hdsb : dso.toNat + dsl.toNat < 2 ^ 64)
    (hct : DecB (fun m => decPL m (decCN m) cso.toNat csl.toNat) m ctors)
    (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) m pfvs) (hPm : PosMR m) :
    Sim (tmtW p n m vis pp pfo pfl I us dso dsl cso csl)
      (tmoTailT fe bs pfvs ds dsl.toNat ctors (decI I) (decI us)) a
      (fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
        IWGrow m m' ∧ PosMR m') := by
  unfold tmtW tmoTailT
  refine Sim.bindK (K := tmtK1 p n pp I us dso dsl cso csl pfo pfl) rfl (fun _ _ => rfl)
    (Q := fun r x m' a' => ToiR r x ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PosMR m') ?_ ?_
  · intro r1 m1 e1
    obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (targetOutsideInst_spec p hP.toi n _ vis I us dso dsl) e1
    obtain ⟨x, a', hrun, hS1, hg1, hT1⟩ := toiW_ok hW1 hS hI hus hds hdsb
    exact ⟨x, a', hrun, hT1, hS1, hg1, hPm.fr (toiW_mfr hW1)⟩
  rintro r1 ⟨nIdx, sI⟩ m1 a1 ⟨⟨hr1, hn1, hsH, hsd⟩, hS1, hg1, hP1⟩
  obtain ⟨-, -, hrsH, hrsd⟩ := partsShapeWords hg1 hq hq9
  rw [tmtK1_some]
  refine Sim.bindK (K := tmtK2 p n I us dso dsl cso csl pfo pfl r1) rfl (fun _ _ => rfl)
    (Q := fun r x m' a' => decLvlEq m' r x ∧ StageR dn vis fe m' a' ∧ IWGrow m1 m' ∧ PosMR m') ?_ ?_
  · intro r2 m2 e2
    obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (stubM_spec p "lvl_eq_c" n _ [r1.tail.headD 0, rdW (m1.arr64 IW) (pp + 6)]) e2
    obtain ⟨x, a', hrun, hS2, hg2, hx⟩ := lvlEqStub_spec dn vis fe _ _ hsH hrsH m1 s2.mem a1 r2 hW2 hS1
    rw [hsd, hrsd] at hrun
    exact ⟨x, a', hrun, hx, hS2, hg2, hP1.fr (MFr.ofStub hW2)⟩
  rintro r2 o m2 a2 ⟨hd2, hS2, hg2, hP2⟩
  rw [tmtK2_some]
  by_cases h2 : r2.headD 0 ≠ 2
  · rw [if_pos h2]; exact Sim.of_none
  rw [if_neg h2]
  have ho : o = some true := by
    rcases o with _ | b
    · simp only [decLvlEq] at hd2; exact absurd (by rw [hd2]; decide) h2
    · cases b
      · simp only [decLvlEq] at hd2; exact absurd (by rw [hd2]; decide) h2
      · rfl
  subst ho
  simp only [liftFueled, pure_bind]
  refine Sim.mstep (K := tmtK3) rfl (fun _ _ => rfl) fun r4 m4 e4 => ?_
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (mkTargetMajor_spec p hP.toi.alloc hP.mkTm n _ _ _ _ _ _ _ _ _ _ _ _ _ _) e4
  rw [mkTMW_eq, Option.map_eq_some_iff] at hW4
  obtain ⟨⟨q, m4'⟩, hpr, he⟩ := hW4
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨hS4, hg4, hq4, ht4, hget4⟩ := posRecW_stage hpr hS2 (by simp)
  simp only [List.length_cons, List.length_nil] at ht4
  have hg04 := (hg1.trans hg2).trans hg4
  have hq4' : q.toNat = iwTop m2 := hq4
  have ht4' : iwTop s4.mem = iwTop m2 + 13 := ht4
  have hdec := decTM_decB_of (m := s4.mem) (q := q.toNat) (by omega)
    (by simpa using hget4 0 (by simp)) (by simpa using hget4 1 (by simp)) (by simpa using hget4 2 (by simp))
    (by simpa using hget4 3 (by simp)) (by simpa using hget4 4 (by simp)) (by simpa using hget4 5 (by simp))
    (by simpa using hget4 6 (by simp)) (by simpa using hget4 7 (by simp)) (by simpa using hget4 8 (by simp))
    (by simpa using hget4 9 (by simp)) (by simpa using hget4 10 (by simp)) (by simpa using hget4 11 (by simp))
    (by simpa using hget4 12 (by simp)) hI hus (hds.grow (OMono.decHL _ _) hg04)
    (hct.grow (OMono.decPL decCN_mono _ _) hg04)
    (show decPL (truncM s4.mem) (decNCN (truncM s4.mem)) (0 : Word).toNat (0 : Word).toNat = some [] by
      simp [decPL])
    (hpf.grow (OMono.decHL _ _) hg04)
  have hn1' : (r1.head?.getD 0).toNat = nIdx := by simpa using hn1
  rw [hn1'] at hdec
  exact Sim.ret ⟨by simpa [decON] using hdec, hS4, hg04, hP2.fr (posRecW_mfr hpr)⟩

end L.Ind
