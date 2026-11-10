module

public import ConAgua.Arena.IndPos
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.L.ModelGen
import ConAgua.Arena.Env
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndPos
import ConAgua.L.WordOff

@[expose] public section

/-!
# NestKeyMap: `ConRon.Arena.NestCtx.hiAt`, `ConRon.Arena.NestFieldKind.flat`, `ConRon.Arena.nestKeyMap`, `ConRon.Arena.nestKindsFlat`

The refinement theorems `nestFieldKindFlat_refines`, `nestCtxHiAt_refines`, `nestKeyMap_refines`, `nestKindsFlat_refines` and the lemmas only they use.
-/

noncomputable section

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
  simp only [invoke_eq _ hp, callFn, nestFieldKindFlat]
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
    iwH m (p + 10) = some ctx.lvls ∧ decAt m (decPL m (decCVp m)) (p + 11) = some ctx.formers := by
  simp only [decCtx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, f, hf, x, hx, g, hg, rfl⟩ := h
  exact ⟨ha, hb, hc, hd, he, hf, hg, hx⟩

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
  simp only [invoke_eq _ hp, callFn, nestCtxHiAt]
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
  simp only [invoke_eq _ hp, callFn, nestKeyMap]
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
        rw [ite_eq_left (by omega : i.toNat < ds.length)]
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
          rw [ite_eq_right (by omega : ¬ i.toNat < ds.length), hdslen]
          exact List.getElem?_eq_getElem _
        sym only [lang_grind, arena_grind] =>
          vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
          finish [decOE, decW0E]
      · have key : ConRon.Arena.nestKeyMap ds holes i.toNat = none := by
          unfold ConRon.Arena.nestKeyMap
          rw [ite_eq_right (by omega : ¬ i.toNat < ds.length), hdslen]
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
  simp only [invoke_eq _ hp, callFn, nestFieldKindFlat]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;> finish [kindFlatW]

l_model nestKindsFlatInner_spec (p : Prog) (hf : p.lookup "nest_field_kind_flat" = some nestFieldKindFlat)
    (hp : p.lookup "nest_kinds_flat_inner" = some nestKindsFlatInner)
  fns [hp ↦ kindsFlatInnerW ro]
  specs [nestFieldKindFlat_wordSpec p hf n]
  grind [arena_grind] fold [tierW, idxW, kindFlatW] finish [tierW, idxW]

/-- A decoded `List NestFieldKind` slice, head first. -/
theorem decKL_succ (m : Mem) (o n : Nat) :
    decKL m o (n + 1) = (do
      let w ← iwA m o
      let x ← decNFK w
      let xs ← decKL m (o + 1) n
      pure (x :: xs)) := by
  simp only [decKL, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero]
  rcases hw : iwA m o with _ | w; · simp only [Option.bind_eq_bind, Option.bind_none]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rcases hx : decNFK w with _ | x; · simp only [Option.bind_none]
  simp only [Option.bind_some]
  congr 1
  apply congrArg (fun f => List.mapM f (List.range n))
  funext j
  simp only [Function.comp]
  congr 2
  omega

theorem kindsFlatInnerW_ok (n : Nat) : ∀ (m : Mem) (off cnt : Word) (ks : List NestFieldKind)
    (r : Word), (m.arr64 IW).size < 2 ^ 64 → decKL m off.toNat cnt.toNat = some ks →
    kindsFlatInnerW n m off cnt = some r → r = if ks.all NestFieldKind.flat then 1 else 0 := by
  induction n with
  | zero => intro m off cnt ks r _ _ h; simp [kindsFlatInnerW.eq_1] at h
  | succ n ih =>
    intro m off cnt ks r hsz hdec h
    by_cases hc : cnt = 0
    · rw [kindsFlatInnerW.arm1 (hc1 := hc)] at h
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
      rcases hw : iwA m off.toNat with _ | w; · simp [hw, Option.bind_eq_bind, Option.bind_none] at hdec
      simp only [hw, Option.bind_eq_bind, Option.bind_some] at hdec
      rcases hnfk : decNFK w with _ | fk; · simp [hnfk, Option.bind_none] at hdec
      simp only [hnfk, Option.bind_some] at hdec
      cases hrest : decKL m (off.toNat + 1) (cnt.toNat - 1) with
      | none => simp [hrest, Option.bind_none] at hdec
      | some ks' =>
        simp only [hrest, Option.bind_some, Option.pure_def,
          Option.some.injEq] at hdec
        have hw' : (m.arr64 IW)[off.toNat]? = some w := by simpa [iwA, aread_apply] using hw
        have hwrd : rdW (m.arr64 IW) off = w := by
          simp only [rdW, hw', Option.getD_some]
        have h1 : (1 : Word).toNat = 1 := by decide
        have hUsize : UInt64.size = 2 ^ 64 := rfl
        have hub : cnt.toNat < 2 ^ 64 := by have := cnt.toNat_lt; omega
        have hoffub : off.toNat < 2 ^ 64 := by have := off.toNat_lt; omega
        have hbound : off.toNat + 1 < 2 ^ 64 := by
          have := (Array.getElem?_eq_some_iff.mp hw').1
          omega
        by_cases hkf : kindFlatW (rdW (m.arr64 IW) off) = 0
        · rw [kindsFlatInnerW.arm2 (hc1 := hc) (hc2 := hkf)] at h
          rw [hwrd] at hkf
          have hcond : ¬ (w &&& 7 ≤ 2) := by
            intro hc'; rw [kindFlatW, ite_eq_left hc'] at hkf; exact absurd hkf (by decide)
          have hfalse : fk.flat = false := by
            cases hb : fk.flat with
            | false => rfl
            | true => exact absurd ((decNFK_flat hnfk).mpr hb) hcond
          simp only [← hdec, List.all_cons, hfalse]
          simp at h; simp [← h]
        · rw [kindsFlatInnerW.arm3 (hc1 := hc) (hc2 := hkf)] at h
          rw [hwrd] at hkf
          have hcond : w &&& 7 ≤ 2 := by
            by_cases hc' : w &&& 7 ≤ 2
            · exact hc'
            · exact absurd (by rw [kindFlatW, ite_eq_right hc']) hkf
          have htrue : fk.flat = true := (decNFK_flat hnfk).mp hcond
          have e1 : (off + 1).toNat = off.toNat + 1 := by
            rw [UInt64.toNat_add, h1]; omega
          have e2 : (cnt - 1).toNat = cnt.toNat - 1 := by
            rw [UInt64.toNat_sub, h1]; omega
          have hdec' : decKL m (off + 1).toNat (cnt - 1).toNat = some ks' := by
            rw [e1, e2]; exact hrest
          have hres := ih _ _ _ ks' _ hsz hdec' h
          simp only [← hdec, List.all_cons, htrue]
          exact hres

/-! ## Reading decoded words without side conditions on the index -/

theorem iwN_idx {m : Mem} {i v : Nat} (h : iwN m i = some v) : i < (m.arr64 IW).size := by
  simp only [iwN, nat?, iwA, aread_apply, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, -⟩ := h
  exact (Array.getElem?_eq_some_iff.mp hw).1

theorem iwN_rd {m : Mem} {i v : Nat} (h : iwN m i = some v) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    rdW (m.arr64 IW) (UInt64.ofNat i) = UInt64.ofNat v ∧ v < 2 ^ 64 :=
  iwN_rdW h (Nat.lt_trans (iwN_idx h) hsz)

theorem iwN_rdw {m : Mem} {w : Word} {v : Nat} (h : iwN m w.toNat = some v) :
    rdW (m.arr64 IW) w = UInt64.ofNat v ∧ v < 2 ^ 64 := by
  have := iwN_rdW h w.toNat_lt
  rwa [UInt64.ofNat_toNat] at this

/-! ## `nest_kinds_flat_mid`, `nest_kinds_flat` -/

l_model nestKindsFlatMid_spec (p : Prog) (hf : p.lookup "nest_field_kind_flat" = some nestFieldKindFlat)
    (hi : p.lookup "nest_kinds_flat_inner" = some nestKindsFlatInner)
    (hp : p.lookup "nest_kinds_flat_mid" = some nestKindsFlatMid)
  fns [hp ↦ kindsFlatMidW ro]
  specs [nestKindsFlatInner_spec p hf hi n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

theorem ofNat_succ' (v : Nat) : UInt64.ofNat v + 1 = UInt64.ofNat (v + 1) := by
  rw [UInt64.ofNat_add]; rfl

/-- One step of a `decPL` walk over a word slice. -/
theorem decPL_step {m : Mem} {α : Type} {f : Nat → Option α} {off cnt : Word} {xs : List α}
    (hsz : (m.arr64 IW).size < 2 ^ 64)
    (h : decPL m f off.toNat cnt.toNat = some xs) (hc : cnt ≠ 0) :
    ∃ v y xs', iwN m off.toNat = some v ∧ f v = some y ∧
      decPL m f (off + 1).toNat (cnt - 1).toNat = some xs' ∧ xs = y :: xs' ∧
      rdW (m.arr64 IW) off = UInt64.ofNat v ∧ v < 2 ^ 64 := by
  have hc1 : cnt.toNat = (cnt.toNat - 1) + 1 := by have := L.toNat_ne_zero_of_ne _ hc; omega
  rw [hc1, decPL_succ] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨v, hv, y, hy, xs', hxs', rfl⟩ := h
  have hlt := iwN_idx hv
  rw [L.toNat_add_one_of_lt (by omega), L.toNat_sub_one_of_ne hc]
  exact ⟨v, y, xs', hv, hy, hxs', rfl, iwN_rdw hv⟩

/-- A header-and-slice record read twice. -/
theorem decLH_rd {m : Mem} {α : Type} {g : Nat → Nat → Option (List α)} {v : Nat} {y : List α}
    (hsz : (m.arr64 IW).size < 2 ^ 64) (h : decLH m g v = some y) :
    ∃ o l, rdW (m.arr64 IW) (UInt64.ofNat v) = UInt64.ofNat o ∧
      rdW (m.arr64 IW) (UInt64.ofNat v + 1) = UInt64.ofNat l ∧ o < 2 ^ 64 ∧ l < 2 ^ 64 ∧ g o l = some y := by
  obtain ⟨o, l, ho, hl, hg⟩ := decAt_some h
  refine ⟨o, l, (iwN_rd ho hsz).1, ?_, (iwN_rd ho hsz).2, (iwN_rd hl hsz).2, hg⟩
  rw [ofNat_succ']; exact (iwN_rd hl hsz).1

theorem kindsFlatMidW_ok (n : Nat) : ∀ (m : Mem) (off cnt : Word) (kss : List (List NestFieldKind)) (r : Word),
    (m.arr64 IW).size < 2 ^ 64 → decPL m (decLH m (decKL m)) off.toNat cnt.toNat = some kss →
    kindsFlatMidW n m off cnt = some r → r = if kss.all (·.all NestFieldKind.flat) then 1 else 0 := by
  induction n with
  | zero => intro m off cnt kss r _ _ h; simp [kindsFlatMidW.eq_1] at h
  | succ n ih =>
    intro m off cnt kss r hsz hdec h
    by_cases hc : cnt = 0
    · rw [kindsFlatMidW.arm1 (hc1 := hc)] at h
      have : kss = [] := by
        have : cnt.toNat = 0 := by rw [hc]; rfl
        rw [this] at hdec; simpa [decPL] using hdec.symm
      simp [this] at h ⊢; simp [← h]
    · obtain ⟨v, ks, kss', hv, hy, hrest, rfl, hrd, hv64⟩ := decPL_step hsz hdec hc
      obtain ⟨o, l, h1, h2, ho, hl, hk⟩ := decLH_rd hsz hy
      rw [kindsFlatMidW.arm2 (hc1 := hc), hrd, h1, h2] at h
      rcases hi : kindsFlatInnerW n m (UInt64.ofNat o) (UInt64.ofNat l) with _ | ok <;> rw [hi] at h; · rw [kindsFlatMidW.k_nest_kinds_flat_inner.none] at h; cases h
      have hoo : (UInt64.ofNat o).toNat = o := UInt64.toNat_ofNat_of_lt' ho
      have hll : (UInt64.ofNat l).toNat = l := UInt64.toNat_ofNat_of_lt' hl
      have hk' : decKL m (UInt64.ofNat o).toNat (UInt64.ofNat l).toNat = some ks := by rw [hoo, hll]; exact hk
      have hok := kindsFlatInnerW_ok n m _ _ ks ok hsz hk' hi
      by_cases hz : ok = 0
      · rw [kindsFlatMidW.k_nest_kinds_flat_inner.arm1 (hc1 := hz)] at h
        have hfalse : ks.all NestFieldKind.flat = false := by
          by_cases hb : ks.all NestFieldKind.flat = true
          · rw [hb] at hok; simp at hok; exact absurd hz (by rw [hok]; decide)
          · simpa using hb
        simp only [List.all_cons, hfalse]
        simp at h; simp [← h]
      · rw [kindsFlatMidW.k_nest_kinds_flat_inner.arm2 (hc1 := hz)] at h
        have htrue : ks.all NestFieldKind.flat = true := by
          by_cases hb : ks.all NestFieldKind.flat = true
          · exact hb
          · have : ks.all NestFieldKind.flat = false := by simpa using hb
            rw [this] at hok; simp at hok; exact absurd hok hz
        have := ih m _ _ kss' r hsz hrest h
        simp only [List.all_cons, htrue]
        exact this

/-! ### `nest_kinds_flat` -/

l_model nestKindsFlat_spec (p : Prog) (hf : p.lookup "nest_field_kind_flat" = some nestFieldKindFlat)
    (hi : p.lookup "nest_kinds_flat_inner" = some nestKindsFlatInner)
    (hm : p.lookup "nest_kinds_flat_mid" = some nestKindsFlatMid)
    (hp : p.lookup "nest_kinds_flat" = some nestKindsFlat)
  fns [hp ↦ kindsFlatOutW ro]
  specs [nestKindsFlatMid_spec p hf hi hm n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

theorem kindsFlatOutW_ok (n : Nat) : ∀ (m : Mem) (off cnt : Word) (kss : List (List (List NestFieldKind))) (r : Word),
    (m.arr64 IW).size < 2 ^ 64 →
    decPL m (decLH m (decPL m (decLH m (decKL m)))) off.toNat cnt.toNat = some kss →
    kindsFlatOutW n m off cnt = some r → r = if ConRon.Arena.nestKindsFlat kss then 1 else 0 := by
  induction n with
  | zero => intro m off cnt kss r _ _ h; simp [kindsFlatOutW.eq_1] at h
  | succ n ih =>
    intro m off cnt kss r hsz hdec h
    by_cases hc : cnt = 0
    · rw [kindsFlatOutW.arm1 (hc1 := hc)] at h
      have : kss = [] := by
        have : cnt.toNat = 0 := by rw [hc]; rfl
        rw [this] at hdec; simpa [decPL] using hdec.symm
      simp [this, ConRon.Arena.nestKindsFlat] at h ⊢; simp [← h]
    · obtain ⟨v, ks, kss', hv, hy, hrest, rfl, hrd, hv64⟩ := decPL_step hsz hdec hc
      obtain ⟨o, l, h1, h2, ho, hl, hk⟩ := decLH_rd hsz hy
      rw [kindsFlatOutW.arm2 (hc1 := hc), hrd, h1, h2] at h
      rcases hi : kindsFlatMidW n m (UInt64.ofNat o) (UInt64.ofNat l) with _ | ok <;> rw [hi] at h; · rw [kindsFlatOutW.k_nest_kinds_flat_mid.none] at h; cases h
      have hoo : (UInt64.ofNat o).toNat = o := UInt64.toNat_ofNat_of_lt' ho
      have hll : (UInt64.ofNat l).toNat = l := UInt64.toNat_ofNat_of_lt' hl
      have hk' : decPL m (decLH m (decKL m)) (UInt64.ofNat o).toNat (UInt64.ofNat l).toNat = some ks := by
        rw [hoo, hll]; exact hk
      have hok := kindsFlatMidW_ok n m _ _ ks ok hsz hk' hi
      by_cases hz : ok = 0
      · rw [kindsFlatOutW.k_nest_kinds_flat_mid.arm1 (hc1 := hz)] at h
        have hfalse : ks.all (·.all NestFieldKind.flat) = false := by
          by_cases hb : ks.all (·.all NestFieldKind.flat) = true
          · rw [hb] at hok; simp at hok; exact absurd hz (by rw [hok]; decide)
          · simpa using hb
        simp only [ConRon.Arena.nestKindsFlat, List.all_cons, hfalse] at h ⊢
        simp at h; simp [← h]
      · rw [kindsFlatOutW.k_nest_kinds_flat_mid.arm2 (hc1 := hz)] at h
        have htrue : ks.all (·.all NestFieldKind.flat) = true := by
          by_cases hb : ks.all (·.all NestFieldKind.flat) = true
          · exact hb
          · have : ks.all (·.all NestFieldKind.flat) = false := by simpa using hb
            rw [this] at hok; simp at hok; exact absurd hok hz
        have := ih m _ _ kss' r hsz hrest h
        simp only [ConRon.Arena.nestKindsFlat, List.all_cons, htrue] at this ⊢
        exact this

section census
variable (p : Prog) (hf : p.lookup "nest_field_kind_flat" = some nestFieldKindFlat)
  (hi : p.lookup "nest_kinds_flat_inner" = some nestKindsFlatInner)
  (hm : p.lookup "nest_kinds_flat_mid" = some nestKindsFlatMid)
  (hp : p.lookup "nest_kinds_flat" = some nestKindsFlat)
include hf hi hm hp

/-- **`nest_kinds_flat` is `nestKindsFlat`** (with `nest_kinds_flat_mid`, `nest_kinds_flat_inner`):
every field kind of every constructor of every member is flat. -/
@[refines ConRon.Arena.nestKindsFlat]
theorem nestKindsFlat_refines (n : Nat) (s₀ : St) (off cnt : Word)
    (kss : List (List (List NestFieldKind))) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64)
    (hdec : decPL s₀.mem (decLH s₀.mem (decPL s₀.mem (decLH s₀.mem (decKL s₀.mem)))) off.toNat cnt.toNat = some kss) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_kinds_flat" [off, cnt]
    ⦃fun r s' => s' = s₀ ∧ (r.headD 0 != 0) = ConRon.Arena.nestKindsFlat kss; ⊤⦄ := by
  refine triple_post (nestKindsFlat_spec p hf hi hm hp n s₀ off cnt) ?_
  rintro r s' ⟨hl, hmm, hm'⟩
  refine ⟨by cases s'; cases s₀; simp_all [LocEq], ?_⟩
  have := kindsFlatOutW_ok n _ _ _ kss _ hsz hdec hm'
  rw [this]
  by_cases hb : ConRon.Arena.nestKindsFlat kss = true <;> simp [hb]

end census

end L.Ind

end
