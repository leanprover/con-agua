import ConAgua.Arena.IndPos
import ConAgua.Arena.IndLibSpec

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

end L.Ind
