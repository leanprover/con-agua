import ConAgua.Arena.WhnfProjRefine2
import ConAgua.Arena.DeclLvlStage
import ConAgua.Arena.Knot

/-!
# `fire_ok` refines `IProjEntry.fireOk` under `CoreS` (lane `whnf3`, helper `whnf3-proj`)

The table's `structSort` against the pinned zero level by the cached `lvl_eq_c`; at `some true`
the field's guard level through `field_sort_zero` (`FieldSortZeroOK`, lane `defeq`'s stub
statement, a hypothesis here). `lvl_eq_c` needs both levels to read back: **`ProjSortDen`**, a
named hypothesis (as `CoreS.lvl_den`: an invariant of the twin's store that `CoreS` does not
carry). The record pool is unchanged across `lvl_eq_c` by its write set from the text
(`lvlText_closed`, lane `decls3`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-- **A projection table's sort level and the pinned zero level read back** (assumed; the twin's
store is well formed and the environment loader interned the table's levels). -/
def ProjSortDen : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb q : Word) (tbl : IProjTable), CoreS dn m a vis fe M eb →
    decTbl (m.arr64 EREC) q.toNat = some tbl →
    (∃ l, denoteL a.store.ls tbl.structSort = some l) ∧
      (∃ l, denoteL a.store.ls a.pins.zeroLevel = some l)

/-- The lookups `fire_ok` needs. -/
structure FireProg (p : Prog) : Prop where
  fireOk : p.lookup "fire_ok" = some fireOkL
  pinw : p.lookup "pin_word" = some pinWordL
  lvl : LvlCacheProg p
  lvlText : ∀ f ∈ lvlFns, p.lookup f = cvgProg.lookup f

/-! ## The word model -/

/-- The guard word of field `i` (`0`, the `default` handle, past the list). -/
def foFs (m : Mem) (q i : Word) : Word :=
  if i < rdW (m.arr64 EREC) (q + 12) then rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (q + 11) + i) else 0

/-- The model of `fire_ok`. -/
def foW (p : Prog) (n : Nat) (m : Mem) (q i us : Word) : Option (Word × Mem) :=
  match callW p n "pin_word" [53] m with
  | none => none
  | some (z, m₁) =>
    match callW p n "lvl_eq_c" [rdW (m₁.arr64 EREC) (q + 8), z.headD 0] m₁ with
    | none => none
    | some (o, m₂) =>
      if o.headD 0 < 2 then some (1, m₂)
      else match callW p n "field_sort_zero" [rdW (m₂.arr64 EREC) (q + 3),
          rdW (m₂.arr64 EREC) (q + 4), us, foFs m₂ q i] m₂ with
        | none => none
        | some (r, m₃) => some (r.headD 0, m₃)

theorem fireOk_spec (p : Prog) (hp : FireProg p) (n : Nat) (s₀ : St) (q i us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "fire_ok" [q, i, us]
    ⦃fun r s' => LocEq s' s₀ ∧ foW p n s₀.mem q i us = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.fireOk]
  simp only [callFn, fireOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_word", callW_spec p n "lvl_eq_c", callW_spec p n "field_sort_zero"] <;>
    finish [foW, foFs]

/-! ## The table record's parts -/

theorem decTbl_parts {a : Array Word} {q : Nat} {tbl : IProjTable} (h : decTbl a q = some tbl) :
    hd? a (q + 8) = some tbl.structSort ∧ hlist? a (q + 3) = some tbl.levelParams ∧
      hlist? a (q + 11) = some tbl.guards := by
  simp only [decTbl, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨_, _, _, _, l3, h3, _, _, _, _, _, _, s8, h8, _, _, g, hg, _, _, rfl⟩ := h
  exact ⟨h8, h3, hg⟩

theorem hlist?_slice' {k : IdxKind} {a : Array Word} {i : Nat} {l : List (Idx k)}
    (h : hlist? a i = some l) :
    ∃ o c : Word, a[i]? = some o ∧ a[i+1]? = some c ∧ hslice? a o.toNat c.toNat = some l := by
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, c, hc, hs⟩ := h
  simp only [nat?, Option.map_eq_some_iff] at ho hc
  obtain ⟨wo, hwo, rfl⟩ := ho
  obtain ⟨wc, hwc, rfl⟩ := hc
  exact ⟨wo, wc, hwo, hwc, hs⟩

theorem hslice?_at' {k : IdxKind} {a : Array Word} {o c : Nat} {l : List (Idx k)}
    (h : hslice? a o c = some l) (j : Nat) (hj : j < c) :
    ∃ w, a[o + j]? = some w ∧ w.toNat < 2 ^ 32 ∧ l[j]? = some (decI w) := by
  obtain ⟨hl, hg⟩ := mapM_option_get _ _ _ h
  have := hg j (by simpa using hj)
  simp only [List.getElem_range] at this
  obtain ⟨w, hw, hw32, hx⟩ := hd?_some (k := k) (x := l[j]'(by simp at hl; omega)) (by
    rw [this]; exact List.getElem?_eq_getElem _)
  exact ⟨w, hw, hw32, by rw [← hx]; exact List.getElem?_eq_getElem _⟩

theorem except_ok_bind' {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

/-! ## The twin's run -/

theorem fireOk_run (e : IProjEntry) (us : LsIdx) (a a₂ : AState) (z : LIdx) (o : Option Bool)
    (hz : zeroLevel.run a = .ok (z, a)) (hl : (lvlEq? e.structSort z).run a = .ok (o, a₂)) :
    (e.fireOk us).run a =
      if o = some true then (fieldSortZeroT e.levelParams us e.fieldSort).run a₂ else .ok (true, a₂) := by
  simp only [IProjEntry.fireOk, StateT.run_bind, hz, except_ok_bind', hl]
  by_cases ho : o = some true
  · subst ho; simp only [ite_true, fieldSortZeroT, StateT.run_bind]; rfl
  · simp only [ho, ite_false]
    have : (!(o == some true)) = true := by cases o with
      | none => rfl
      | some b => cases b <;> simp_all
    simp only [this, ite_true]; rfl

/-! ## The refinement -/

theorem rdW_of_get {a : Array Word} {x : Word} {k : Nat} {w : Word} (hk : x.toNat = k)
    (h : a[k]? = some w) : rdW a x = w := by simp [rdW, hk, h]

theorem toNat_add_small (x : Word) (c : Nat) (h : x.toNat + c < 2 ^ 64) :
    (x + UInt64.ofNat c).toNat = x.toNat + c := by
  rw [UInt64.toNat_add]
  have e : (UInt64.ofNat c).toNat = c := by simp; omega
  rw [e]; exact Nat.mod_eq_of_lt h

/-- **`fire_ok` refines `IProjEntry.fireOk`**, given lane `defeq`'s `field_sort_zero` and the
denotation of the table's sort and the zero level (`ProjSortDen`). -/
@[refines ConRon.Arena.IProjEntry.fireOk]
theorem fireOk_refines (p : Prog) (hp : FireProg p) (hfz : FieldSortZeroOK p)
    (hden : ProjSortDen) : FireOkOK p := by
  intro n s₀ a₀ dn vis fe M eb q i us tbl hS hus htbl
  cases n with
  | zero => exact CoreSpec.zeroW hp.fireOk _ _ _ _ _ _ _ _ _ _ _
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (fireOk_spec p hp n s₀ q i us)
  subst hs0
  refine ⟨hloc, ?_⟩
  unfold foW at hW
  cases c1 : callW p n "pin_word" [53] s.mem with
  | none => rw [c1] at hW; cases hW
  | some q1 =>
  obtain ⟨r₁, m₁⟩ := q1
  rw [c1] at hW
  simp only at hW
  obtain ⟨t1, ht1, -, hpw⟩ := triple_of_callW
    (pinWord_specM p hp.pinw n ⟨s.mem, Locals.init []⟩ 53) c1
  have hpw' : pinWordM s.mem 53 = some (r₁, m₁) := by simpa [ht1] using hpw
  simp only [pinWordM] at hpw'
  split at hpw' <;> try (cases hpw'; done)
  simp only [Option.some.injEq, Prod.mk.injEq] at hpw'
  obtain ⟨hr1, rfl⟩ := hpw'
  have hP := hS.pins
  have hz : r₁.headD 0 = pinW s.mem 53 := by rw [← hr1]; simp [rdW, pinW]
  have hEsz := hS.erec
  obtain ⟨hss, hlp, hgd⟩ := decTbl_parts htbl
  obtain ⟨w8, h8, h8lt, hss'⟩ := hd?_some hss
  have hq8 : q.toNat + 8 < (s.mem.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp h8).1
  have hrd8 : rdW (s.mem.arr64 EREC) (q + 8) = w8 :=
    rdW_of_get (toNat_add_small q 8 (by omega)) h8
  rw [hrd8] at hW
  rcases Nat.lt_or_ge n 2 with hsm | hbig
  · rw [lvlEqC_small p hp.lvl.c n hsm] at hW; cases hW
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  cases c2 : callW p (n' + 2) "lvl_eq_c" [w8, r₁.headD 0] s.mem with
  | none => rw [c2] at hW; cases hW
  | some q2 =>
  obtain ⟨o, m₂⟩ := q2
  rw [c2] at hW
  simp only at hW
  obtain ⟨⟨lu, hdu⟩, ⟨lz, hdz⟩⟩ := hden dn s.mem a₀ vis fe M eb q tbl hS htbl
  rw [hss'] at hdu
  have hzl : a₀.pins.zeroLevel = decI (r₁.headD 0) := by rw [hP.zeroLevel, hz]
  rw [hzl] at hdz
  have hz32 : HW (r₁.headD 0) := by rw [hz]; exact hP.lv_lt.2.1
  obtain ⟨ok2, ⟨M2, hS2, hK2, hSt2⟩, res2, hr2⟩ := CoreSpec.of_callW
    (lvlEqC_refines p hp.lvl n' ⟨s.mem, Locals.init []⟩ a₀ dn vis fe M eb hS w8 (r₁.headD 0)
      h8lt hz32 lu lz hdu hdz) c2
  obtain ⟨s'', hs'', hf, -⟩ := triple_of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
    (invoke_memFrame (closedW_of_agree lvlText_closed hp.lvlText) (n' + 2)
      (f := "lvl_eq_c") (by decide) [w8, r₁.headD 0] ⟨s.mem, Locals.init []⟩) c2
  rw [hs''] at hf
  have hE2 : m₂.arr64 EREC = s.mem.arr64 EREC := hf.1 _ lvlA_erec (by decide)
  have hrunZ : zeroLevel.run a₀ = .ok (decI (r₁.headD 0), a₀) := by rw [hz]; exact pinZeroLevel_run hP
  have hrunL := AM.run_of_ok _ _ ok2
  rw [res2] at hrunL
  have hrunL' : (lvlEq? (tbl.entry i.toNat).structSort (decI (r₁.headD 0))).run a₀ =
      .ok (decO (o.headD 0), AM.st (lvlEq? (decI w8) (decI (r₁.headD 0))) a₀) := by
    simp only [IProjTable.entry, hss']; exact hrunL
  have hT := fireOk_run (tbl.entry i.toNat) (decI us) a₀ _ _ _ hrunZ hrunL'
  by_cases b : o.headD 0 < 2
  · rw [if_pos b] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hm⟩ := hW
    have hno : ¬ decO (o.headD 0) = some true := by
      unfold decO; split
      · simp
      · split
        · simp
        · rename_i h0 h1; exfalso
          have := UInt64.lt_iff_toNat_lt.mp b
          have : (o.headD 0).toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e))
          have : (o.headD 0).toNat ≠ 1 := fun e => h1 (UInt64.toNat_inj.mp (by simpa using e))
          simp at *; omega
    rw [if_neg hno] at hT
    obtain ⟨okT, stT, resT⟩ := AM.of_run_ok _ _ _ _ hT
    refine ⟨okT, ⟨M2, by rw [stT, ← hm]; exact hS2, hK2, by rw [← hm]; exact hSt2⟩, ?_, ?_⟩
    · rw [resT]; simp only [decBool, ← hr0]; decide
    · unfold ResH HW; rw [← hr0]; decide
  rw [if_neg b] at hW
  have hyes : decO (o.headD 0) = some true := by
    unfold decO
    have := mt UInt64.lt_iff_toNat_lt.mpr b
    have e2 : (2 : Word).toNat = 2 := rfl
    rw [e2] at this
    have h0 : o.headD 0 ≠ 0 := fun e => by rw [e] at this; simp at this
    have h1 : o.headD 0 ≠ 1 := fun e => by rw [e] at this; simp at this
    rw [if_neg h0, if_neg h1]
  rw [if_pos hyes] at hT
  -- the words `field_sort_zero` reads, in the record pool of `m₂` (= the caller's)
  obtain ⟨w3, w4, h3, h4, hsl3⟩ := hlist?_slice' hlp
  obtain ⟨w11, w12, h11, h12, hsl11⟩ := hlist?_slice' hgd
  have hq12 : q.toNat + 12 < (s.mem.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp (by
    rw [show q.toNat + 12 = q.toNat + 11 + 1 by omega]; exact h12)).1
  have hrd3 : rdW (m₂.arr64 EREC) (q + 3) = w3 := by
    rw [hE2]; exact rdW_of_get (toNat_add_small q 3 (by omega)) h3
  have hrd4 : rdW (m₂.arr64 EREC) (q + 4) = w4 := by
    rw [hE2]; exact rdW_of_get (toNat_add_small q 4 (by omega)) (by
      rw [show q.toNat + 4 = q.toNat + 3 + 1 by omega]; exact h4)
  have hrd11 : rdW (m₂.arr64 EREC) (q + 11) = w11 := by
    rw [hE2]; exact rdW_of_get (toNat_add_small q 11 (by omega)) h11
  have hrd12 : rdW (m₂.arr64 EREC) (q + 12) = w12 := by
    rw [hE2]; exact rdW_of_get (toNat_add_small q 12 (by omega)) (by
      rw [show q.toNat + 12 = q.toNat + 11 + 1 by omega]; exact h12)
  -- the guard word
  have hfs : HW (foFs m₂ q i) ∧ decI (foFs m₂ q i) = tbl.guards.getD i.toNat default := by
    have hlen := hslice?_length hsl11
    simp only [foFs, hrd11, hrd12]
    by_cases hi : i < w12
    · rw [if_pos hi]
      have hi' := UInt64.lt_iff_toNat_lt.mp hi
      obtain ⟨w, hw, hw32, hgw⟩ := hslice?_at' hsl11 i.toNat (by rw [← hlen] at *; omega)
      have hb := (Array.getElem?_eq_some_iff.mp hw).1
      have hrd : rdW (s.mem.arr64 EREC) (w11 + i) = w := by
        refine rdW_of_get ?_ hw
        rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      rw [hE2, hrd]
      refine ⟨hw32, ?_⟩
      rw [List.getD_eq_getElem?_getD, hgw]; rfl
    · rw [if_neg hi]
      have hi' := mt UInt64.lt_iff_toNat_lt.mpr hi
      refine ⟨by unfold HW; decide, ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  have hlps : hslice? (m₂.arr64 EREC) w3.toNat w4.toNat = some tbl.levelParams := by
    rw [hE2]; exact hsl3
  cases c3 : callW p (n' + 2) "field_sort_zero" [rdW (m₂.arr64 EREC) (q + 3),
      rdW (m₂.arr64 EREC) (q + 4), us, foFs m₂ q i] m₂ with
  | none => rw [c3] at hW; cases hW
  | some q3 =>
  obtain ⟨r₃, m₃⟩ := q3
  rw [c3] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hm⟩ := hW
  rw [hrd3, hrd4] at c3
  obtain ⟨ok3, ⟨M3, hS3, hK3, hSt3⟩, res3, hr3⟩ := CoreSpec.of_callW
    (hfz (n' + 2) ⟨m₂, Locals.init []⟩ (AM.st (lvlEq? (decI w8) (decI (r₁.headD 0))) a₀) dn vis fe
      M2 eb w3 w4 us (foFs m₂ q i) tbl.levelParams hS2 hus hfs.1 hlps) c3
  have hrun3 := AM.run_of_ok _ _ ok3
  have hT' : ((tbl.entry i.toNat).fireOk (decI us)).run a₀ =
      .ok (AM.res (fieldSortZeroT tbl.levelParams (decI us) (decI (foFs m₂ q i)))
          (AM.st (lvlEq? (decI w8) (decI (r₁.headD 0))) a₀),
        AM.st (fieldSortZeroT tbl.levelParams (decI us) (decI (foFs m₂ q i)))
          (AM.st (lvlEq? (decI w8) (decI (r₁.headD 0))) a₀)) := by
    rw [hT]
    simp only [IProjTable.entry, hfs.2] at hrun3 ⊢
    exact hrun3
  obtain ⟨okT, stT, resT⟩ := AM.of_run_ok _ _ _ _ hT'
  refine ⟨okT, ⟨M3, by rw [stT, ← hm]; exact hS3, hK2.trans hK3,
    by rw [← hm]; exact hSt2.trans hSt3⟩, ?_, ?_⟩
  · rw [resT, res3]; simp only [decBool, hr0]
  · unfold ResH; rw [← hr0]; exact hr3

end L.Arena
