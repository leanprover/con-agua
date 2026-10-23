import ConAgua.Arena.RecGenSpec23
import ConAgua.Arena.RecGenSpec10
import ConAgua.Arena.StripTeleSpec

/-!
# `classFieldsAgree` (lane `indproofs4`, helper `cls`)

`class_fields_agree(vis, p, ft.off, ft.len, ms.off, ms.len, fvs.off, fvs.len, es.off, es.len, i0,
ks.off, ks.len)`: node agreement at every recursive field. L walks `ks` with a `while` loop (the
twin: a list recursion over `ks` and the field index `i`); the loop is a named block (`cfaLoop`),
its model `cfaW` runs the callees by `callW`, and `cfaW_ok` relates it to the twin on the
entries `ks.drop j` by induction on the loop fuel. Callees: `intern_bvar` (the out-of-range
datum variable, as `exprGetD`), the `fvar_type_d` stub, `strip_pis` (`stripPis_refines`),
`target_major_at` (`rec3TMA_sim`, its record decoded below the tops), `class_leaf_at`,
`class_nodes_agree` (`RecGenSpec23`). The walk memos (`RcMR`) are carried across the callees
without a memo post by their write sets (`MFr`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The loop as a named block -/

/-- The loop of `classFieldsAgreeL` (RecGen.lean), named for its spec. -/
-- con-ron: none — `classFieldsAgreeL`'s own loop (`rfl`), a named block for the proof
def cfaLoop : Stmt := lblk (vis, p, ftOff, ftLen, msOff, msLen, fvsOff, fvsLen, esOff, esLen, i0,
    ksOff, ksLen, j, i, kf, tag, t, tele, fv, fty, ok, teleOff, teleLen, leaf, mt, b) {
  while j < ksLen {
    kf := IW.u64[ksOff + j];
    tag := IW.u64[kf];
    if tag == 1 {
      t := IW.u64[kf + 1];
      tele := IW.u64[kf + 2];
      if i < fvsLen { fv := IW.u64[fvsOff + i] } else { fv := call intern_bvar(0) };
      fty := call fvar_type_d(fv);
      (ok, teleOff, teleLen, leaf) := call strip_pis(tele, fty);
      if ok == 0 { abort };
      mt := call target_major_at(msOff, msLen, t);
      b := call class_leaf_at(mt, leaf);
      if b == 0 { abort };
      b := call class_nodes_agree(vis, p, ftOff, ftLen, mt, teleOff, teleLen, leaf, fvsOff, fvsLen,
        i, esOff, esLen)
    };
    i := i + 1;
    j += 1
  }
}

/-- `classFieldsAgreeL`, with its loop spliced from `cfaLoop`. -/
-- con-ron: none — `classFieldsAgreeL` itself (`rfl`), its loop a named block for the proof
def classFieldsAgreeL' : FunDecl := lfn
    (vis, p, ftOff, ftLen, msOff, msLen, fvsOff, fvsLen, esOff, esLen, i0, ksOff, ksLen)
    locals (j, i, kf, tag, t, tele, fv, fty, ok, teleOff, teleLen, leaf, mt, b) {
  j := 0;
  i := i0;
  ⟪cfaLoop⟫;
  return 0
}

theorem classFieldsAgreeL_eq : classFieldsAgreeL = classFieldsAgreeL' := rfl

/-! ## The model -/

section model
variable (p : Prog) (k : Nat)

/-- After `class_nodes_agree`: the next field. -/
def cfaK6 (rest : Mem → Option Mem) : Option (List Word × Mem) → Option Mem
  | none => none
  | some (_, m) => rest m

/-- After `class_leaf_at`: node agreement. -/
def cfaK5 (vis q fto ftl fvo fvl i eo el teo tel leaf mt : Word) (rest : Mem → Option Mem) :
    Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else
      cfaK6 rest (callW p k "class_nodes_agree" [vis, q, fto, ftl, mt, teo, tel, leaf, fvo, fvl, i, eo, el] m)

/-- After `target_major_at`: the leaf's class. -/
def cfaK4 (vis q fto ftl fvo fvl i eo el teo tel leaf : Word) (rest : Mem → Option Mem) :
    Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m) => cfaK5 p k vis q fto ftl fvo fvl i eo el teo tel leaf (r.headD 0) rest
      (callW p k "class_leaf_at" [r.headD 0, leaf] m)

/-- After `strip_pis`: the field's class. -/
def cfaK3 (vis q fto ftl mo ml fvo fvl i eo el t : Word) (rest : Mem → Option Mem) :
    Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else
      cfaK4 p k vis q fto ftl fvo fvl i eo el (r.tail.headD 0) (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) rest (callW p k "target_major_at" [mo, ml, t] m)

/-- After `fvar_type_d`: the field's telescope. -/
def cfaK2 (vis q fto ftl mo ml fvo fvl i eo el t tele : Word) (rest : Mem → Option Mem) :
    Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m) => cfaK3 p k vis q fto ftl mo ml fvo fvl i eo el t rest
      (callW p k "strip_pis" [tele, r.headD 0] m)

/-- After the datum variable: its type. -/
def cfaK1 (vis q fto ftl mo ml fvo fvl i eo el t tele : Word) (rest : Mem → Option Mem) :
    Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m) => cfaK2 p k vis q fto ftl mo ml fvo fvl i eo el t tele rest
      (callW p k "fvar_type_d" [r.headD 0] m)

/-- The datum variable `i` (in range), else the interned `.bvar 0`. -/
def cfaFv (m : Mem) (fvo fvl i : Word) : Option (List Word × Mem) :=
  if i < fvl then some ([rdW (m.arr64 IW) (fvo + i)], m) else callW p k "intern_bvar" [0] m

/-- **The model of `class_fields_agree`'s loop** at L fuel `k`, from cursor `j` and field `i`: the
memory at the exit. -/
def cfaW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, q, fto, ftl, mo, ml, fvo, fvl, eo, el, ko, kl, j, i =>
    if j < kl then
      if rdW (m.arr64 IW) (rdW (m.arr64 IW) (ko + j)) = 1 then
        cfaK1 p k vis q fto ftl mo ml fvo fvl i eo el
          (rdW (m.arr64 IW) (rdW (m.arr64 IW) (ko + j) + 1)) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (ko + j) + 2))
          (fun m' => cfaW k m' vis q fto ftl mo ml fvo fvl eo el ko kl (j + 1) (i + 1))
          (cfaFv p k m fvo fvl i)
      else cfaW k m vis q fto ftl mo ml fvo fvl eo el ko kl (j + 1) (i + 1)
    else some m

section arms
variable (m : Mem) (vis q fto ftl mo ml fvo fvl eo el ko kl j i t tele teo tel leaf mt : Word)
  (r : List Word) (rest : Mem → Option Mem)
theorem cfaK6_some : cfaK6 rest (some (r, m)) = rest m := rfl
theorem cfaK5_bad (h : r.headD 0 = 0) :
    cfaK5 p k vis q fto ftl fvo fvl i eo el teo tel leaf mt rest (some (r, m)) = none := by
  simp only [cfaK5]; rw [if_pos h]
theorem cfaK5_ok (h : ¬ r.headD 0 = 0) :
    cfaK5 p k vis q fto ftl fvo fvl i eo el teo tel leaf mt rest (some (r, m)) =
      cfaK6 rest (callW p k "class_nodes_agree" [vis, q, fto, ftl, mt, teo, tel, leaf, fvo, fvl, i, eo, el] m) := by
  simp only [cfaK5]; rw [if_neg h]
theorem cfaK4_some : cfaK4 p k vis q fto ftl fvo fvl i eo el teo tel leaf rest (some (r, m)) =
    cfaK5 p k vis q fto ftl fvo fvl i eo el teo tel leaf (r.headD 0) rest
      (callW p k "class_leaf_at" [r.headD 0, leaf] m) := rfl
theorem cfaK3_bad (h : r.headD 0 = 0) :
    cfaK3 p k vis q fto ftl mo ml fvo fvl i eo el t rest (some (r, m)) = none := by
  simp only [cfaK3]; rw [if_pos h]
theorem cfaK3_ok (h : ¬ r.headD 0 = 0) :
    cfaK3 p k vis q fto ftl mo ml fvo fvl i eo el t rest (some (r, m)) =
      cfaK4 p k vis q fto ftl fvo fvl i eo el (r.tail.headD 0) (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) rest (callW p k "target_major_at" [mo, ml, t] m) := by
  simp only [cfaK3]; rw [if_neg h]
theorem cfaK2_some : cfaK2 p k vis q fto ftl mo ml fvo fvl i eo el t tele rest (some (r, m)) =
    cfaK3 p k vis q fto ftl mo ml fvo fvl i eo el t rest (callW p k "strip_pis" [tele, r.headD 0] m) := rfl
theorem cfaK1_some : cfaK1 p k vis q fto ftl mo ml fvo fvl i eo el t tele rest (some (r, m)) =
    cfaK2 p k vis q fto ftl mo ml fvo fvl i eo el t tele rest (callW p k "fvar_type_d" [r.headD 0] m) := rfl
theorem cfaFv_in (h : i < fvl) : cfaFv p k m fvo fvl i = some ([rdW (m.arr64 IW) (fvo + i)], m) := by
  simp only [cfaFv]; rw [if_pos h]
theorem cfaFv_out (h : ¬ i < fvl) : cfaFv p k m fvo fvl i = callW p k "intern_bvar" [0] m := by
  simp only [cfaFv]; rw [if_neg h]
theorem cfaW_exit (h : ¬ j < kl) :
    cfaW p (k + 1) m vis q fto ftl mo ml fvo fvl eo el ko kl j i = some m := by
  simp only [cfaW]; rw [if_neg h]
theorem cfaW_ord (h : j < kl) (h1 : ¬ rdW (m.arr64 IW) (rdW (m.arr64 IW) (ko + j)) = 1) :
    cfaW p (k + 1) m vis q fto ftl mo ml fvo fvl eo el ko kl j i =
      cfaW p k m vis q fto ftl mo ml fvo fvl eo el ko kl (j + 1) (i + 1) := by
  simp only [cfaW]; rw [if_pos h, if_neg h1]
theorem cfaW_rec (h : j < kl) (h1 : rdW (m.arr64 IW) (rdW (m.arr64 IW) (ko + j)) = 1) :
    cfaW p (k + 1) m vis q fto ftl mo ml fvo fvl eo el ko kl j i =
      cfaK1 p k vis q fto ftl mo ml fvo fvl i eo el
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (ko + j) + 1)) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (ko + j) + 2))
        (fun m' => cfaW p k m' vis q fto ftl mo ml fvo fvl eo el ko kl (j + 1) (i + 1))
        (cfaFv p k m fvo fvl i) := by
  simp only [cfaW]; rw [if_pos h, if_pos h1]
end arms

end model

attribute [ind_grind] cfaK6_some cfaK5_bad cfaK5_ok cfaK4_some cfaK3_bad cfaK3_ok cfaK2_some cfaK1_some
  cfaFv_in cfaFv_out cfaW_exit cfaW_ord cfaW_rec

/-! ## The `vcgen` specs -/

set_option maxHeartbeats 1600000 in
theorem cfaLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p k cfaLoop
    ⦃fun r s' => r = .normal ∧
      cfaW p k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)
        (s₀.loc 7) (s₀.loc 8) (s₀.loc 9) (s₀.loc 11) (s₀.loc 12) (s₀.loc 13) (s₀.loc 14) = some s'.mem; ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := cfaLoop) rfl]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        callW_spec p k "intern_bvar", callW_spec p k "fvar_type_d", callW_spec p k "strip_pis",
        callW_spec p k "target_major_at", callW_spec p k "class_leaf_at",
        callW_spec p k "class_nodes_agree"] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

theorem cfa_spec (p : Prog) (hp : p.lookup "class_fields_agree" = some classFieldsAgreeL) (n : Nat)
    (s₀ : St) (vis q fto ftl mo ml fvo fvl eo el i0 ko kl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fields_agree"
      [vis, q, fto, ftl, mo, ml, fvo, fvl, eo, el, i0, ko, kl]
    ⦃fun _ s' => LocEq s' s₀ ∧
      cfaW p n s₀.mem vis q fto ftl mo ml fvo fvl eo el ko kl 0 i0 = some s'.mem; ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
  rw [invoke_eq _ hp, classFieldsAgreeL_eq]
  simp only [callFn, classFieldsAgreeL']
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      fun s => Triple.step_exec (cfaLoop_spec p (n + 1) s)] <;>
    finish (gen := 40) (instances := 20000) [loc_init4, loc_init5, loc_init6, loc_init7, loc_init8,
      loc_init9, loc_init10, loc_init11, loc_init12]

/-! ## Write sets -/

theorem tmdW_mfr {m m' : Mem} {r : List Word} (h : tmdW m = some (r, m')) : MFr [] [] m m' := by
  rw [tmdW_eq] at h
  cases h1 : stubM "intern_nanon" m [] with
  | none => rw [h1] at h; simp [tmdK1] at h
  | some x1 =>
  obtain ⟨ra, m1⟩ := x1
  rw [h1, tmdK1_some] at h
  refine (MFr.ofStub h1).trans ?_
  cases hp : pinWordV m1 52 with
  | none => rw [hp] at h; simp [tmdK2] at h
  | some ls =>
  rw [hp, tmdK2_some] at h
  cases hmk : mkTMW m1 (ra.headD 0) ls 0 0 0 0 0 0 0 0 0 0 0 with
  | none => rw [hmk] at h; simp [tmdK3] at h
  | some x3 =>
  obtain ⟨r3, m2⟩ := x3
  rw [hmk, tmdK3_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  simp only [mkTMW] at hmk
  cases hal : allocW m1 13 with
  | none => rw [hal] at hmk; simp at hmk
  | some qm =>
  obtain ⟨q, m1a⟩ := qm
  rw [hal] at hmk
  simp only [Option.some.injEq, Prod.mk.injEq] at hmk
  rw [← hmk.2]
  refine (allocW_mfr hal).trans ?_
  have e : tmWr m1a q (ra.headD 0) ls 0 0 0 0 0 0 0 0 0 0 0 =
      wrIW m1a q [ra.headD 0, ls, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    simp [tmWr, wrIW, UInt64.add_assoc]
  rw [e]; exact MFr.of_iw (wrIW_frame _ _ _)

theorem tmaW_mfr {n : Nat} {m m' : Mem} {mo ml c : Word} {r : List Word} (h : tmaW n m mo ml c = some (r, m')) :
    MFr [] [] m m' := by
  cases n with
  | zero => simp [tmaW] at h
  | succ n =>
  by_cases hc : c < ml
  · rw [tmaW_hit n m mo ml c hc] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
  rw [tmaW_miss n m mo ml c hc] at h
  cases ho : fuelW n (tmdW m) with
  | none => rw [ho] at h; cases h
  | some b0 =>
  obtain ⟨r0, m0⟩ := b0
  rw [ho, tmaK_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
  cases n with
  | zero => cases ho
  | succ n => simp only [fuelW_succ] at ho; exact tmdW_mfr ho

theorem leafAtW_mfr {m m' : Mem} {mm leaf : Word} {r : List Word} (h : leafAtW m mm leaf = some (r, m')) :
    MFr [] [] m m' := by
  simp only [leafAtW] at h
  cases h1 : stubM "get_app_fn_f" m [CWF, leaf] with
  | none => rw [h1] at h; cases h
  | some x =>
  obtain ⟨r1, m1⟩ := x
  simp only [h1] at h
  refine (MFr.ofStub h1).trans ?_
  have hm : m' = m1 := by
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
    · split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  rw [hm]; exact MFr.refl _ _ _

/-! ## Reading the fields' records -/

/-- An ordinary field's record: tag `0`. A recursive field's: tag `1`, its class and telescope
length. -/
theorem iwN_lt_size {m : Mem} {i v : Nat} (h : iwN m i = some v) : i < (m.arr64 IW).size := by
  simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, -⟩ := h
  exact (Array.getElem?_eq_some_iff.mp hx).1

theorem decCF_words {m : Mem} {q : Nat} {cf : ClassField} (h : decCF m q = some cf)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (cf = .ordinary ∧ rdW (m.arr64 IW) (UInt64.ofNat q) = 0) ∨
    (∃ t tl, cf = .recursive t tl ∧ rdW (m.arr64 IW) (UInt64.ofNat q) = 1 ∧
      rdW (m.arr64 IW) (UInt64.ofNat q + 1) = UInt64.ofNat t ∧ t < 2 ^ 64 ∧
      rdW (m.arr64 IW) (UInt64.ofNat q + 2) = UInt64.ofNat tl ∧ tl < 2 ^ 64) := by
  simp only [decCF, bind, Option.bind_eq_some_iff] at h
  obtain ⟨tg, htg, hcf⟩ := h
  have hq0 := iwN_lt_size htg
  have h0 := iwN_rdW htg (by omega)
  rcases tg with _ | _ | tg
  · left; simp only [pure, Option.some.injEq] at hcf; exact ⟨hcf.symm, by rw [h0.1]; rfl⟩
  · right
    simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at hcf
    obtain ⟨t, ht, tl, htl, rfl⟩ := hcf
    have hq2 := iwN_lt_size htl
    have e1 : UInt64.ofNat q + 1 = UInt64.ofNat (q + 1) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp <;> omega
    have e2 : UInt64.ofNat q + 2 = UInt64.ofNat (q + 2) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp <;> omega
    have h1 := iwN_rdW ht (by omega)
    have h2 := iwN_rdW htl (by omega)
    exact ⟨t, tl, rfl, by rw [h0.1]; rfl, by rw [e1, h1.1], h1.2, by rw [e2, h2.1], h2.2⟩
  · simp at hcf

/-- A class decoded below the tops lies below the top. -/
theorem decTM_lt_top {m : Mem} {q : Nat} {x : TargetMajor} (h : DecB (fun m => decTM m q) m x) :
    q < iwTop m := by
  have h' : decTM (truncM m) q = some x := h
  simp only [decTM, bind, Option.bind_eq_some_iff] at h'
  obtain ⟨i, hi, -⟩ := h'
  simp only [iwH, hd?, bind, Option.bind_eq_some_iff] at hi
  obtain ⟨w, hw, -⟩ := hi
  exact (truncM_iw_get hw).1

/-! ## The relational side -/

/-- The lookups of `class_fields_agree`. -/
structure CfaProg (p : Prog) : Prop extends CnaProg p where
  strip : StripProg p
  pw : p.lookup "pin_word" = some pinWordL
  mtm : p.lookup "mk_target_major" = some mkTargetMajor
  tmd : p.lookup "target_major_default" = some targetMajorDefault
  tma : p.lookup "target_major_at" = some targetMajorAt
  cla : p.lookup "class_leaf_at" = some classLeafAtL
  bf : p.lookup "bvar_find" = some bvarFind
  bp : p.lookup "bvar_push" = some bvarPush
  ib : p.lookup "intern_bvar" = some internBVar
  cfa : p.lookup "class_fields_agree" = some classFieldsAgreeL

section rel
variable {p : Prog} (P : CfaProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (vis q fto ftl mo ml fvo fvl eo el ko kl : Word) (bs : BlockShape) (formerTys : List EIdx)
  (ms : List TargetMajor) (fvs : List EIdx) (es : List NestCtorNf) (ks : List ClassField)
include P

/-- The datum variable `i`: `exprGetD`. -/
theorem cfaFv_ok {k : Nat} {m m0 : Mem} {a : AState} {i : Word} {r0 : List Word}
    (h : cfaFv p k m fvo fvl i = some (r0, m0)) (hS : StageR dn vis fe m a)
    (hfv : decHL m fvo.toNat fvl.toNat = some fvs) (hfvb : fvo.toNat + fvl.toNat < 2 ^ 64) (hP : RcMR m) :
    ∃ a0, (ConRon.Arena.exprGetD fvs i.toNat).run a = .ok (decI (r0.headD 0), a0) ∧ H (r0.headD 0) ∧
      StageR dn vis fe m0 a0 ∧ IWGrow m m0 ∧ RcMR m0 := by
  by_cases hi : i < fvl
  · rw [cfaFv_in (h := hi)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hit : i.toNat < fvl.toNat := UInt64.lt_iff_toNat_lt.mp hi
    obtain ⟨w, hw1, hw2, hw3⟩ := decHL_get' hfv i.toNat hit hfvb
    have hoi : fvo + i = UInt64.ofNat (fvo.toNat + i.toNat) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
    simp only [List.headD_cons]; rw [hoi, hw1]
    refine ⟨a, ?_, hw2, hS, IWGrow.refl m, hP⟩
    rw [← hw3]
    simp [ConRon.Arena.exprGetD, hit, decHL_length m hfv]; rfl
  · rw [cfaFv_out (h := hi)] at h
    obtain ⟨s0, hs0, -, hb⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (internBVar_spec p P.bf P.bp P.ib k _ 0) h
    simp only at hs0 hb; subst hs0
    obtain ⟨a', hrun, hS', hg⟩ := internBVar_stage hS 0 hb
    have hH := binternW_hw _ a hS.1.arena.1.bvar _ _ _ hb
    refine ⟨a', ?_, hH, hS', hg, hP.fr (MFr.of_frame (binternW_frame _ _ _ _ hb) (by simp [BREC, BSLOT]) (by simp))⟩
    have hge : fvl.toNat ≤ i.toNat := by
      have : ¬ i.toNat < fvl.toNat := fun h => hi (UInt64.lt_iff_toNat_lt.mpr h)
      omega
    have hn : fvs[i.toNat]? = none := by
      rw [List.getElem?_eq_none_iff, decHL_length m hfv]; exact hge
    simp only [ConRon.Arena.exprGetD, hn]
    exact hrun

/-- **`class_fields_agree`'s loop refines `classFieldsAgree`** on the fields from the cursor `j`
(field index `i`). -/
theorem cfaW_ok (k : Nat) : ∀ (m m' : Mem) (a : AState) (j i : Word),
    cfaW p k m vis q fto ftl mo ml fvo fvl eo el ko kl j i = some m' →
    StageR dn vis fe m a → BSOK m q.toNat bs → decHL m fto.toNat ftl.toNat = some formerTys →
    fto.toNat + ftl.toNat ≤ iwTop m → DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms →
    mo.toNat + ml.toNat < 2 ^ 64 →
    decHL m fvo.toNat fvl.toNat = some fvs → fvo.toNat + fvl.toNat ≤ iwTop m →
    PSlR decNCN es eo el m → SPL decCF m ko.toNat kl.toNat ks → j ≤ kl →
    i.toNat + (kl.toNat - j.toNat) < 2 ^ 64 → RcMR m →
    ∃ a', (ConRon.Arena.classFieldsAgree V fe bs formerTys ms fvs es i.toNat (ks.drop j.toNat)).run a =
      .ok ((), a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  induction k with
  | zero => intro m m' a j i h; simp [cfaW] at h
  | succ k ih =>
  intro m m' a j i h hS hbs hft hftb hms hmsb hfv hfvb hes hks hje hi hP
  have hsz := hS.2.2.2.1
  have hkl := hks.length
  have hjk : j.toNat ≤ kl.toNat := UInt64.le_iff_toNat_le.mp hje
  by_cases hj : j < kl
  rotate_left
  · rw [cfaW_exit (h := hj)] at h
    simp only [Option.some.injEq] at h; subst h
    have h1 : kl.toNat ≤ j.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hj
    have : ks.drop j.toNat = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]
    exact ⟨a, rfl, hS, IWGrow.refl _, hP⟩
  have hjl : j.toNat < kl.toNat := UInt64.lt_iff_toNat_lt.mp hj
  have := kl.toNat_lt
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  have hje1 : j + 1 ≤ kl := UInt64.le_iff_toNat_le.mpr (by omega)
  have hi' : (i + 1).toNat + (kl.toNat - (j + 1).toNat) < 2 ^ 64 := by omega
  have hdrop : ks.drop j.toNat = ks[j.toNat]'(by omega) :: ks.drop (j.toNat + 1) :=
    List.drop_eq_getElem_cons (by omega)
  rw [hdrop]
  -- the field's record
  obtain ⟨kq, hkq, hstab⟩ := hks.get j.toNat hjl
  have hkb : ko.toNat + kl.toNat ≤ iwTop m := hks.1
  have hkb64 := hS.lt64 hkb
  have hkw := iwN_rdW hkq (by omega)
  have hkoj : ko + j = UInt64.ofNat (ko.toNat + j.toNat) := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp <;> omega
  have hkf : rdW (m.arr64 IW) (ko + j) = UInt64.ofNat kq := by rw [hkoj, hkw.1]
  have hcf := hstab.get
  rcases decCF_words hcf hsz with ⟨hord, h0⟩ | ⟨t, tl, hrec, h1, ht, htb, htl, htlb⟩
  · -- an ordinary field
    rw [cfaW_ord (h := hj) (h1 := by rw [hkf, h0]; decide)] at h
    obtain ⟨a', run, hS', hg, hP'⟩ := ih m m' a (j + 1) (i + 1) h hS hbs hft hftb hms hmsb hfv hfvb hes hks
      hje1 hi' hP
    refine ⟨a', ?_, hS', hg, hP'⟩
    rw [hord, ConRon.Arena.classFieldsAgree]
    rw [hi1, hj1] at run; exact run
  -- a recursive field
  rw [cfaW_rec (h := hj) (h1 := by rw [hkf]; exact h1), hkf, ht, htl] at h
  have htT : (UInt64.ofNat t : Word).toNat = t := UInt64.toNat_ofNat_of_lt' htb
  have htlT : (UInt64.ofNat tl : Word).toNat = tl := UInt64.toNat_ofNat_of_lt' htlb
  have hfvb64 := hS.lt64 hfvb
  -- the datum variable
  cases c0 : cfaFv p k m fvo fvl i with
  | none => rw [c0] at h; simp [cfaK1] at h
  | some x0 =>
  obtain ⟨r0, m0⟩ := x0
  rw [c0, cfaK1_some] at h
  obtain ⟨a0, run0, hH0, hS0, hg0, hP0⟩ := cfaFv_ok P dn fe vis fvo fvl fvs c0 hS hfv hfvb64 hP
  -- `fvar_type_d`
  cases c1 : callW p k "fvar_type_d" [r0.headD 0] m0 with
  | none => rw [c1] at h; simp [cfaK2] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [c1, cfaK2_some] at h
  obtain ⟨s1, hs1, -, hw1⟩ := triple_of_callW (s₀ := ⟨m0, Locals.init []⟩)
    (stubM_spec p "fvar_type_d" k _ [r0.headD 0]) c1
  simp only at hs1 hw1; subst hs1
  obtain ⟨fty, a1, run1, hS1, hg1, hH1, hD1⟩ := fvarTypeD_spec dn vis fe (r0.headD 0) hH0 _ _ a0 r1 hw1 hS0
  have hP1 := hP0.fr (MFr.ofStub hw1)
  -- `strip_pis`
  cases c2 : callW p k "strip_pis" [UInt64.ofNat tl, r1.headD 0] s1.mem with
  | none => rw [c2] at h; simp [cfaK3] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [c2] at h
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, hd2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (stripPis_refines p P.strip dn vis fe (UInt64.ofNat tl) (r1.headD 0) hH1 k _ a1 hS1) c2
  obtain ⟨s2', hs2', -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (stripPis_specW p P.strip k _ (UInt64.ofNat tl) (r1.headD 0)) c2
  simp only at hs2 hS2 hg2 hd2 hs2' hw2; subst hs2
  rw [hs2'] at hw2
  have hP2 := hP1.fr (MFr.ofStripF (stripF_of_TW hw2))
  have run2 := AM.run_of_ok _ a1 hok2
  rw [htlT, hD1] at run2 hS2 hd2
  generalize hx2 : AM.res (stripPis tl fty) a1 = x2 at run2 hd2
  generalize ha2 : AM.st (stripPis tl fty) a1 = a2 at run2 hS2
  rcases x2 with _ | ⟨teleB, leafE⟩
  · have h0 : r2.headD 0 = 0 := hd2
    rw [cfaK3_bad (h := h0)] at h; cases h
  obtain ⟨h21, ⟨hdl, hbl⟩, hlwH, hlwD⟩ := hd2
  have h0 : ¬ r2.headD 0 = 0 := by rw [h21]; decide
  rw [cfaK3_ok (h := h0)] at h
  simp only [getD_one, show (1 + 1 : Nat) = 2 from rfl, getD_two] at hdl hbl
  have hl3 : (r2.drop 3).headD 0 = r2.tail.tail.tail.headD 0 := by
    rcases r2 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [hl3] at hlwH hlwD
  have hg02 := (hg0.trans hg1).trans hg2
  -- `target_major_at`
  cases c3 : callW p k "target_major_at" [mo, ml, UInt64.ofNat t] s2.mem with
  | none => rw [c3] at h; simp [cfaK4] at h
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [c3, cfaK4_some] at h
  obtain ⟨s3, hs3, -, hw3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (targetMajorAt_spec p P.ha P.pw P.mtm P.tmd P.tma k _ mo ml (UInt64.ofNat t)) c3
  simp only at hs3 hw3; subst hs3
  obtain ⟨tm, a3, run3, hS3, hg3, hTM⟩ := rec3TMA_sim dn vis fe k s2.mem a2 mo ml (UInt64.ofNat t) ms hS2
    (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg02) hmsb _ hw3
  have hP3 := hP2.fr (tmaW_mfr hw3)
  rw [htT] at run3
  -- `class_leaf_at`
  cases c4 : callW p k "class_leaf_at" [r3.headD 0, r2.tail.tail.tail.headD 0] s3.mem with
  | none => rw [c4] at h; simp [cfaK5] at h
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  rw [c4] at h
  cases k with
  | zero =>
    obtain ⟨_, _, hf⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩) (invoke_exec_zero p _ _ _) c4
    exact hf.elim
  | succ k' =>
  obtain ⟨s4, hs4, -, hok4, hS4, hg4, hb4, -⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (classLeafAt_refines p P.cla P.hv k' _ a3 dn vis fe (r3.headD 0) (r2.tail.tail.tail.headD 0) tm hS3 hlwH
      (hTM.get (decTM_mono _)) (decTM_lt_top hTM)) c4
  obtain ⟨s4', hs4', -, hw4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (leafAt_spec p P.cla P.hv k' _ (r3.headD 0) (r2.tail.tail.tail.headD 0)) c4
  simp only at hs4 hS4 hg4 hb4 hs4' hw4; subst hs4
  rw [hs4'] at hw4
  have hP4 := hP3.fr (leafAtW_mfr hw4)
  have run4 := AM.run_of_ok _ a3 hok4
  rw [hlwD] at run4 hS4 hb4
  generalize hx4 : AM.res (ConRon.Arena.classLeafAt tm leafE) a3 = b4 at run4 hb4
  generalize ha4 : AM.st (ConRon.Arena.classLeafAt tm leafE) a3 = a4 at run4 hS4
  by_cases hz : r4.headD 0 = 0
  · rw [cfaK5_bad (h := hz)] at h; cases h
  rw [cfaK5_ok (h := hz)] at h
  have hbt : b4 = true := by rw [← hb4]; simpa using hz
  subst hbt
  have hg04 := hg02.trans (hg3.trans hg4)
  -- `class_nodes_agree`
  cases c5 : callW p (k' + 1) "class_nodes_agree" [vis, q, fto, ftl, r3.headD 0, r2.tail.headD 0,
      r2.tail.tail.headD 0, r2.tail.tail.tail.headD 0, fvo, fvl, i, eo, el] s4.mem with
  | none => rw [c5] at h; simp [cfaK6] at h
  | some x5 =>
  obtain ⟨r5, m5⟩ := x5
  rw [c5, cfaK6_some] at h
  obtain ⟨s5, hs5, -, hok5, hS5, hg5, hP5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (classNodesAgree_refines P.toCnaProg (k' + 1) _ a4 dn fe vis q fto ftl (r3.headD 0) (r2.tail.headD 0)
      (r2.tail.tail.headD 0) (r2.tail.tail.tail.headD 0) fvo fvl i eo el bs formerTys tm teleB fvs es hS4
      (hbs.grow hg04) (by rw [decHL_grow hg04 hftb]; exact hft) (Nat.le_trans hftb hg04.1)
      (hTM.grow (decTM_mono _) hg4) (HSl0.of (by rw [decHL_grow (hg3.trans hg4) hbl]; exact hdl)
        (Nat.le_trans hbl (hg3.trans hg4).1)) hlwH
      (by rw [decHL_grow hg04 hfvb]; exact hfv) (Nat.le_trans hfvb hg04.1)
      (hes.grow (fun q => decNCN_mono q) hg04) hP4) c5
  simp only at hs5 hS5 hg5 hP5; subst hs5
  have run5 := AM.run_of_ok _ a4 hok5
  rw [decE_eq, hlwD] at run5
  have hg05 := hg04.trans hg5
  obtain ⟨a6, run6, hS6, hg6, hP6⟩ := ih s5.mem m' _ (j + 1) (i + 1) h hS5 (hbs.grow hg05)
    (by rw [decHL_grow hg05 hftb]; exact hft) (by have := hg05.1; omega)
    (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg05) hmsb
    (by rw [decHL_grow hg05 hfvb]; exact hfv) (by have := hg05.1; omega)
    (hes.grow (fun q => decNCN_mono q) hg05) (hks.grow hg05) hje1 hi' hP5
  refine ⟨a6, ?_, hS6, hg05.trans hg6, hP6⟩
  rw [hi1, hj1] at run6
  rw [hrec, ConRon.Arena.classFieldsAgree]
  simp only [StateT.run_bind, run0, except_ok_bind, run1, run2, run3, run4, if_true, run5]
  rw [decE_eq, hlwD] at run6
  exact run6

end rel

/-- **`class_fields_agree` refines `classFieldsAgree`** (through `target_k53`'s and `fvar_type_d`'s
contracts and stubs): the class's shape (`BSOK`), former types, the classes, the datum's variables,
the class's entries decoded below the tops, the field kinds a stable slice (as `class_fields_of`
returns them) with a word-sized field index, the walk memos well formed. -/
@[refines ConRon.Arena.classFieldsAgree]
theorem classFieldsAgree_refines {p : Prog} (P : CfaProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl mo ml fvo fvl eo el i0 ko kl : Word)
    (bs : BlockShape) (formerTys : List EIdx) (ms : List TargetMajor) (fvs : List EIdx)
    (es : List NestCtorNf) (ks : List ClassField) (hS : StageR dn vis fe s₀.mem a₀)
    (hbs : BSOK s₀.mem q.toNat bs) (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) s₀.mem ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hfv : decHL s₀.mem fvo.toNat fvl.toNat = some fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop s₀.mem)
    (hes : PSlR decNCN es eo el s₀.mem) (hks : SPL decCF s₀.mem ko.toNat kl.toNat ks)
    (hi : i0.toNat + kl.toNat < 2 ^ 64) (hP : RcMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fields_agree"
      [vis, q, fto, ftl, mo, ml, fvo, fvl, eo, el, i0, ko, kl]
    ⦃fun _ s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classFieldsAgree V fe bs formerTys ms fvs es i0.toNat ks) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classFieldsAgree V fe bs formerTys ms fvs es i0.toNat ks) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem; ⊤⦄ := by
  refine triple_post (cfa_spec p P.cfa n s₀ vis q fto ftl mo ml fvo fvl eo el i0 ko kl) ?_
  rintro r s' ⟨hl', hm⟩
  obtain ⟨a', run, hS', hg, hP'⟩ := cfaW_ok P dn fe vis q fto ftl mo ml fvo fvl eo el ko kl bs formerTys ms
    fvs es ks n _ _ a₀ 0 i0 hm hS hbs hft hftb hms hmsb hfv hfvb hes hks UInt64.zero_le
    (by simpa using hi) hP
  simp only [UInt64.toNat_zero, List.drop_zero] at run
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hst]; exact hS', hg, hP'⟩

end L.Ind
