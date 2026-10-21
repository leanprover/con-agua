import ConAgua.Arena.IndPos
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.IndGrindAttr

/-!
# Refinements of `IndPos` (lane `induct`), round 2: the pure functions

`@[refines T]` theorems for the `IndPos` functions that touch neither `e_view` nor the store:
`NestFieldKind.flat`, `nestKindsFlat`, `NestCtx.hiAt`, `nestKeyMap`, `NestCtx.rootHoles`,
`nestHoleAt`. The statement shape follows `IndPartsSpec.lean`: the memory unchanged (or grown,
for the two that allocate), the result decoding the twin's value.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `NestFieldKind.flat` -/

theorem two_toNat : (2 : Word).toNat = 2 := by decide

theorem and7_eq_mod {w : Word} : (w &&& 7).toNat = w.toNat % 8 := by
  rw [UInt64.toNat_and]; simpa using Nat.and_two_pow_sub_one_eq_mod w.toNat 3

/-- The low 3 bits of a `NestFieldKind` word are its constructor tag (`decNFK`); flat iff `≤ 2`. -/
theorem decNFK_flat_iff {w : Word} {fk : NestFieldKind} (h : decNFK w = some fk) :
    w.toNat % 8 ≤ 2 ↔ fk.flat = true := by
  simp only [decNFK] at h
  split at h <;> (try split at h) <;> (try simp only [Option.some.injEq] at h) <;>
    (try subst h) <;> simp_all [NestFieldKind.flat]

/-- The word test `nest_field_kind_flat` makes, as an `Iff` with the twin's `flat`. -/
theorem decNFK_flat {w : Word} {fk : NestFieldKind} (h : decNFK w = some fk) :
    (w &&& 7 ≤ (2 : Word)) ↔ fk.flat = true := by
  rw [UInt64.le_iff_toNat_le, and7_eq_mod, two_toNat]
  exact decNFK_flat_iff h

/-- **`nest_field_kind_flat` is `NestFieldKind.flat`.** -/
@[refines ConRon.Arena.NestFieldKind.flat]
theorem nestFieldKindFlat_refines (p : Prog) (hp : p.lookup "nest_field_kind_flat" = some nestFieldKindFlat)
    (n : Nat) (s₀ : St) (w : Word) (fk : NestFieldKind) (h : decNFK w = some fk) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_field_kind_flat" [w]
    ⦃fun r s' => s' = s₀ ∧ (r.headD 0 != 0) = fk.flat; ⊤⦄ := by
  have key := decNFK_flat h
  rw [invoke_eq _ hp]
  simp only [callFn, nestFieldKindFlat]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;>
      finish

/-! ## `NestCtx.hiAt` -/

/-- A decoded `NestCtx`'s fields. -/
theorem decCtx_some {m : Mem} {p : Nat} {ctx : NestCtx} (h : decCtx m p = some ctx) :
    decAt m (decHL m) p = some ctx.names ∧ decAt m (decHL m) (p + 2) = some ctx.lps ∧
    iwN m (p + 4) = some ctx.nP ∧ decAt m (decNL m) (p + 5) = some ctx.nIdxs ∧
    decAt m (decHL m) (p + 7) = some ctx.params ∧ iwH m (p + 9) = some ctx.sort ∧
    iwH m (p + 10) = some ctx.lvls := by
  rw [decCtx] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, f, hf, g, hg, rfl⟩ := h
  exact ⟨ha, hb, hc, hd, he, hf, hg⟩

/-- **`nest_ctx_hi_at` is `NestCtx.hiAt`.** -/
@[refines ConRon.Arena.NestCtx.hiAt]
theorem nestCtxHiAt_refines (p : Prog) (hp : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt)
    (n : Nat) (s₀ : St) (q nf : Word) (ctx : NestCtx) (hq : decCtx s₀.mem q.toNat = some ctx)
    (hq4 : q.toNat + 4 < 2 ^ 64) (hq1 : q.toNat + 1 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctx_hi_at" [q, nf]
    ⦃fun r s' => s' = s₀ ∧ r.headD 0 = UInt64.ofNat (ctx.hiAt nf.toNat); ⊤⦄ := by
  obtain ⟨hnames, -, hnP, -, -, -, -⟩ := decCtx_some hq
  obtain ⟨onames, lnames, -, holnames, hgnames⟩ := decAt_some hnames
  have e4 : UInt64.ofNat (q.toNat + 4) = q + 4 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  have e1 : UInt64.ofNat (q.toNat + 1) = q + 1 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  have hv1 := (iwN_rdW hnP hq4).1
  have hv2 := (iwN_rdW holnames hq1).1
  rw [e4] at hv1
  rw [e1] at hv2
  have hlen : ctx.names.length = lnames := decHL_length s₀.mem hgnames
  have key : rdW (s₀.mem.arr64 IW) (q + 4) + rdW (s₀.mem.arr64 IW) (q + 1) + nf =
      UInt64.ofNat (ctx.hiAt nf.toNat) := by
    rw [hv1, hv2, NestCtx.hiAt, hlen, UInt64.ofNat_add, UInt64.ofNat_add, UInt64.ofNat_toNat]
  rw [invoke_eq _ hp]
  simp only [callFn, nestCtxHiAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish

/-! ## `nestKeyMap` -/

theorem decHL_get {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL m o l = some xs) (j : Nat) (hj : j < l) :
    iwH m (o + j) = some (xs[j]'(by rw [decHL_length m h]; exact hj)) := by
  have hl := decHL_length m h
  simp only [decHL, hslice?] at h
  have hget := mapM_opt_get (fun j => hd? (iwA m) (o + j)) (List.range l) xs h j (by simpa using hj)
  simpa [iwH] using hget

/-- **`nest_key_map` is `nestKeyMap`.** -/
@[refines ConRon.Arena.nestKeyMap]
theorem nestKeyMap_refines (p : Prog) (hp : p.lookup "nest_key_map" = some nestKeyMap)
    (n : Nat) (s₀ : St) (dsOff dsLen hoOff hoLen i : Word) (ds holes : List EIdx)
    (hds : decHL s₀.mem dsOff.toNat dsLen.toNat = some ds)
    (hho : decHL s₀.mem hoOff.toNat hoLen.toNat = some holes)
    (hdlen : dsOff.toNat + dsLen.toNat < 2 ^ 64) (hhlen : hoOff.toNat + hoLen.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_key_map" [dsOff, dsLen, hoOff, hoLen, i]
    ⦃fun r s' => s' = s₀ ∧ decOE s₀.mem r (ConRon.Arena.nestKeyMap ds holes i.toNat); ⊤⦄ := by
  have hdslen : ds.length = dsLen.toNat := decHL_length s₀.mem hds
  have hholen : holes.length = hoLen.toNat := decHL_length s₀.mem hho
  rw [invoke_eq _ hp]
  simp only [callFn, nestKeyMap]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    by_cases hc1 : i.toNat < dsLen.toNat
    · obtain ⟨w, hw, hwlt, hwd⟩ := iwH_rdW (decHL_get hds i.toNat hc1) (by omega)
      have e : UInt64.ofNat (dsOff.toNat + i.toNat) = dsOff + i := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
      rw [e] at hw
      have key : ConRon.Arena.nestKeyMap ds holes i.toNat = some (ds[i.toNat]'(by omega)) := by
        unfold ConRon.Arena.nestKeyMap
        rw [if_pos (by omega : i.toNat < ds.length)]
        exact List.getElem?_eq_getElem _
      sym only [lang_grind, arena_grind] =>
        vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
        finish [decOE, decW0E]
    · have key1 : ¬ (i.toNat < dsLen.toNat) := hc1
      by_cases hc2 : i.toNat - dsLen.toNat < hoLen.toNat
      · obtain ⟨w, hw, hwlt, hwd⟩ := iwH_rdW (decHL_get hho (i.toNat - dsLen.toNat) hc2) (by omega)
        have hidl : (i - dsLen).toNat = i.toNat - dsLen.toNat :=
          UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
        have e : UInt64.ofNat (hoOff.toNat + (i.toNat - dsLen.toNat)) = hoOff + (i - dsLen) := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_add, hidl]
          simp
        rw [e] at hw
        have key : ConRon.Arena.nestKeyMap ds holes i.toNat =
            some (holes[i.toNat - dsLen.toNat]'(by omega)) := by
          unfold ConRon.Arena.nestKeyMap
          rw [if_neg (by omega : ¬ i.toNat < ds.length), hdslen]
          exact List.getElem?_eq_getElem _
        sym only [lang_grind, arena_grind] =>
          vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
          finish [decOE, decW0E]
      · have key : ConRon.Arena.nestKeyMap ds holes i.toNat = none := by
          unfold ConRon.Arena.nestKeyMap
          rw [if_neg (by omega : ¬ i.toNat < ds.length), hdslen]
          exact List.getElem?_eq_none (by omega)
        sym only [lang_grind, arena_grind] =>
          vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
          finish [decOE]

/-! ## `nestKindsFlat` -/

/-- The word `nest_field_kind_flat` computes. -/
def kindFlatW (w : Word) : Word := if w &&& 7 ≤ 2 then 1 else 0

theorem nestFieldKindFlat_wordSpec (p : Prog)
    (hp : p.lookup "nest_field_kind_flat" = some nestFieldKindFlat) (n : Nat) (s₀ : St) (w : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_field_kind_flat" [w]
    ⦃fun r s' => s' = s₀ ∧ r.headD 0 = kindFlatW w; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nestFieldKindFlat]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;> finish [kindFlatW]

/-- The model of `nest_kinds_flat_inner`. -/
def kindsFlatInnerW : Nat → Mem → Word → Word → Option Word
  | 0, _, _, _ => none
  | n + 1, m, off, cnt =>
    if cnt = 0 then some 1
    else if kindFlatW (rdW (m.arr64 IW) off) = 0 then some 0
    else kindsFlatInnerW n m (off + 1) (cnt - 1)

section arms
variable (n : Nat) (m : Mem) (off cnt : Word)
theorem kindsFlatInnerW_nil (h : cnt = 0) : kindsFlatInnerW (n + 1) m off cnt = some 1 := by
  simp [kindsFlatInnerW, h]
theorem kindsFlatInnerW_miss (h : cnt ≠ 0) (hk : kindFlatW (rdW (m.arr64 IW) off) = 0) :
    kindsFlatInnerW (n + 1) m off cnt = some 0 := by simp [kindsFlatInnerW, h, hk]
theorem kindsFlatInnerW_next (h : cnt ≠ 0) (hk : kindFlatW (rdW (m.arr64 IW) off) ≠ 0) :
    kindsFlatInnerW (n + 1) m off cnt = kindsFlatInnerW n m (off + 1) (cnt - 1) := by
  simp [kindsFlatInnerW, h, hk]
end arms

grind_pattern [ind_grind] kindsFlatInnerW_nil => kindsFlatInnerW (n + 1) m off cnt
grind_pattern [ind_grind] kindsFlatInnerW_miss => kindsFlatInnerW (n + 1) m off cnt
grind_pattern [ind_grind] kindsFlatInnerW_next => kindsFlatInnerW (n + 1) m off cnt

section specs
variable (p : Prog) (hf : p.lookup "nest_field_kind_flat" = some nestFieldKindFlat)
include hf

theorem nestKindsFlatInner_spec (hp : p.lookup "nest_kinds_flat_inner" = some nestKindsFlatInner)
    (n : Nat) : ∀ (s₀ : St) (off cnt : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_kinds_flat_inner" [off, cnt]
    ⦃fun r s' => s' = s₀ ∧ kindsFlatInnerW n s₀.mem off cnt = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ off cnt
    rw [invoke_eq _ hp]; simp only [callFn, nestKindsFlatInner]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ off cnt
    rw [invoke_eq _ hp]
    simp only [callFn, nestKindsFlatInner]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestFieldKindFlat_wordSpec p hf n, ih] <;> finish (gen := 20)

end specs

/-- A decoded `List NestFieldKind` slice, head first. -/
theorem decKL_succ (m : Mem) (o n : Nat) :
    decKL m o (n + 1) = (do
      let w ← (iwA m)[o]?
      let x ← decNFK w
      let xs ← decKL m (o + 1) n
      pure (x :: xs)) := by
  simp only [decKL, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero]
  cases hw : (iwA m)[o]? with
  | none => simp only [hw, Option.bind_eq_bind, Option.bind_none]
  | some w =>
    simp only [hw, Option.bind_eq_bind, Option.bind_some]
    cases hx : decNFK w with
    | none => simp only [hx, Option.bind_eq_bind, Option.bind_none]
    | some x =>
      simp only [hx, Option.bind_eq_bind, Option.bind_some]
      congr 1
      apply congrArg (fun f => List.mapM f (List.range n))
      funext j
      simp only [Function.comp]
      congr 2
      omega

theorem kindsFlatInnerW_ok (n : Nat) : ∀ (m : Mem) (off cnt : Word) (ks : List NestFieldKind)
    (r : Word), off.toNat + cnt.toNat < 2 ^ 64 → decKL m off.toNat cnt.toNat = some ks →
    kindsFlatInnerW n m off cnt = some r → r = if ks.all NestFieldKind.flat then 1 else 0 := by
  induction n with
  | zero => intro m off cnt ks r _ _ h; simp [kindsFlatInnerW] at h
  | succ n ih =>
    intro m off cnt ks r hbound hdec h
    by_cases hc : cnt = 0
    · rw [kindsFlatInnerW_nil n m off cnt hc] at h
      have : ks = [] := by
        have : cnt.toNat = 0 := by rw [hc]; rfl
        rw [this] at hdec; simpa [decKL] using hdec
      simp [this] at h ⊢; simp [← h]
    · have hcnt1 : cnt.toNat = (cnt.toNat - 1) + 1 := by
        have : cnt.toNat ≠ 0 := fun hz => hc (by
          apply UInt64.toNat_inj.mp; simpa using hz)
        omega
      rw [hcnt1] at hdec
      rw [decKL_succ] at hdec
      cases hw : (iwA m)[off.toNat]? with
      | none => simp [hw, Option.bind_eq_bind, Option.bind_none] at hdec
      | some w =>
        simp only [hw, Option.bind_eq_bind, Option.bind_some] at hdec
        cases hnfk : decNFK w with
        | none => simp [hnfk, Option.bind_eq_bind, Option.bind_none] at hdec
        | some fk =>
          simp only [hnfk, Option.bind_eq_bind, Option.bind_some] at hdec
          cases hrest : decKL m (off.toNat + 1) (cnt.toNat - 1) with
          | none => simp [hrest, Option.bind_eq_bind, Option.bind_none] at hdec
          | some ks' =>
            simp only [hrest, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq] at hdec
            have hw' : (m.arr64 IW)[off.toNat]? = some w := hw
            have hwrd : rdW (m.arr64 IW) off = w := by
              simp only [rdW, hw', Option.getD_some]
            have h1 : (1 : Word).toNat = 1 := by decide
            have hUsize : UInt64.size = 2 ^ 64 := rfl
            have hub : cnt.toNat < 2 ^ 64 := by have := cnt.toNat_lt; omega
            have hoffub : off.toNat < 2 ^ 64 := by have := off.toNat_lt; omega
            by_cases hkf : kindFlatW (rdW (m.arr64 IW) off) = 0
            · rw [kindsFlatInnerW_miss n m off cnt hc hkf] at h
              rw [hwrd] at hkf
              have hcond : ¬ (w &&& 7 ≤ 2) := by
                intro hc'; rw [kindFlatW, if_pos hc'] at hkf; exact absurd hkf (by decide)
              have hfalse : fk.flat = false := by
                cases hb : fk.flat with
                | false => rfl
                | true => exact absurd ((decNFK_flat hnfk).mpr hb) hcond
              simp only [← hdec, List.all_cons, hfalse]
              simp at h; simp [← h]
            · rw [kindsFlatInnerW_next n m off cnt hc hkf] at h
              rw [hwrd] at hkf
              have hcond : w &&& 7 ≤ 2 := by
                by_cases hc' : w &&& 7 ≤ 2
                · exact hc'
                · exact absurd (by rw [kindFlatW, if_neg hc']) hkf
              have htrue : fk.flat = true := (decNFK_flat hnfk).mp hcond
              have e1 : (off + 1).toNat = off.toNat + 1 := by
                rw [UInt64.toNat_add, h1]; omega
              have e2 : (cnt - 1).toNat = cnt.toNat - 1 := by
                rw [UInt64.toNat_sub, h1]; omega
              have hdec' : decKL m (off + 1).toNat (cnt - 1).toNat = some ks' := by
                rw [e1, e2]; exact hrest
              have hbound' : (off + 1).toNat + (cnt - 1).toNat < 2 ^ 64 := by
                rw [e1, e2]; omega
              have hres := ih _ _ _ ks' _ hbound' hdec' h
              simp only [← hdec, List.all_cons, htrue, true_and]
              exact hres

end L.Ind
