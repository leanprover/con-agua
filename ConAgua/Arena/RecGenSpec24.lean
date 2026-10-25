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
      if b == 0 { fail R_GENERATED_RECURSOR_FIELD };
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
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
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
  obtain ⟨⟨ra, m1⟩, h1, h⟩ := of_K h rfl
  rw [tmdK1_some] at h
  refine (MFr.of_frame (naF_frame h1) (by simp [NAREC, NASLOT]) (by simp)).trans ?_
  obtain ⟨ls, hp, h⟩ := of_K h rfl
  rw [tmdK2_some] at h
  obtain ⟨⟨r3, m2⟩, hmk, h⟩ := of_K h rfl
  rw [tmdK3_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  simp only [mkTMW] at hmk
  rcases hal : allocW m1 13 with _ | qm
  · rw [hal] at hmk; simp at hmk
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
  rcases n with _ | n
  · simp [tmaW] at h
  by_cases hc : c < ml
  · rw [tmaW_hit n m mo ml c hc] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
  rw [tmaW_miss n m mo ml c hc] at h
  obtain ⟨⟨r0, m0⟩, ho, h⟩ := of_K h rfl
  rw [tmaK_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
  cases n with
  | zero => cases ho
  | succ n => simp only [fuelW_succ] at ho; exact tmdW_mfr ho

theorem leafAtW_mfr {m m' : Mem} {mm leaf : Word} {r : List Word} (h : leafAtW m mm leaf = some (r, m')) :
    MFr [] [] m m' := by
  simp only [leafAtW] at h
  rcases h1 : gafF m [CWF, leaf] with _ | x
  · rw [h1] at h; cases h
  obtain ⟨r1, m1⟩ := x
  simp only [h1] at h
  refine (MFr.ofGafF h1).trans ?_
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
  na : NaF p
  ad : AdF p

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
    obtain ⟨s0, rfl, -, hb⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (internBVar_spec p P.bf P.bp P.ib k _ 0) h
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

end rel

end L.Ind
