import ConAgua.Arena.WhnfProjRefine2
import ConAgua.Arena.DeclLvlStage
import ConAgua.Arena.Knot
import ConAgua.Arena.InferProj

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

namespace L.Arena

/-- **An environment projection table's sort level and the pinned zero level read back**
(`StoreDen.proj`, `StoreDen.zero`). -/
def ProjSortDen : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word) (c : NIdx) (tbl : IProjTable), CoreS dn m a vis fe M eb →
    fe.findTable? c = some tbl →
    (∃ l, denoteL a.store.ls tbl.structSort = some l) ∧
      (∃ l, denoteL a.store.ls a.pins.zeroLevel = some l)

/-- **A projection table's readbacks for `field_sort_zero`** (named hypothesis, as
`ProjSortDen`; `StoreDen.proj` and `readN` give it): the name readback cache holds readbacks, an
environment table's level parameters and the field guards below
`numFields` read back (`fire_ok` is asked only there, `FireOkOK`). -/
def FireDen : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word) (c : NIdx) (tbl : IProjTable), CoreS dn m a vis fe M eb →
    fe.findTable? c = some tbl →
    ReadNCOK a ∧ (∃ ks, tbl.levelParams.mapM (denoteN a.store.ns) = some ks) ∧
      ∀ i, i < tbl.numFields → ∃ l, denoteL a.store.ls (tbl.guards.getD i default) = some l

/-- `FireOkOK` at universe arguments `us` that read back (what `field_sort_zero` needs; the
callers' `us` is a stored `const` node's list, `StoreDen.constLs`). -/
def FireOkOKD (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb q i us : Word) (tbl : IProjTable), CoreS dn s₀.mem a₀ vis fe M eb →
    HW us → decTbl (s₀.mem.arr64 EREC) q.toNat = some tbl →
    (∃ c, fe.findTable? c = some tbl) → i.toNat < tbl.numFields →
    (∃ ls, denoteLs a₀.store.lss (decI us) = some ls) →
    CoreSpec p n "fire_ok" [q, i, us] ((tbl.entry i.toNat).fireOk (decI us)) decBool s₀ a₀ dn vis
      fe M eb

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
  obtain ⟨_, _, l3, h3, _, _, _, _, _, _, s8, h8, _, _, g, hg, rfl⟩ := h
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

theorem fo_toNat_add_small (x : Word) (c : Nat) (h : x.toNat + c < 2 ^ 64) :
    (x + UInt64.ofNat c).toNat = x.toNat + c := by
  rw [UInt64.toNat_add]
  have e : (UInt64.ofNat c).toNat = c := by simp; omega
  rw [e]; exact Nat.mod_eq_of_lt h

/-- **`fire_ok` refines `IProjEntry.fireOk`**, given lane `defeq`'s `field_sort_zero` and the
denotation of the table's sort and the zero level (`ProjSortDen`). -/
@[refines ConRon.Arena.IProjEntry.fireOk]
theorem fireOk_refines (p : Prog) (hp : FireProg p) (hfz : FieldSortZeroOK p)
    (hden : ProjSortDen) (hden2 : FireDen) : FireOkOKD p := by
  intro n s₀ a₀ dn vis fe M eb q i us tbl hS hus htbl ⟨cT, hfe⟩ hlt husd
  cases n with
  | zero => exact CoreSpec.zeroW hp.fireOk _ _ _ _ _ _ _ _ _ _ _
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (fireOk_spec p hp n s₀ q i us)
  subst hs0
  refine ⟨hloc, ?_⟩
  unfold foW at hW
  rcases c1 : callW p n "pin_word" [53] s.mem with _ | ⟨r₁, m₁⟩ <;>
    simp only [c1, reduceCtorEq] at hW
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
    rdW_of_get (fo_toNat_add_small q 8 (by omega)) h8
  rw [hrd8] at hW
  rcases Nat.lt_or_ge n 2 with hsm | hbig
  · rw [lvlEqC_small p hp.lvl.c n hsm] at hW; cases hW
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  rcases c2 : callW p (n' + 2) "lvl_eq_c" [w8, r₁.headD 0] s.mem with _ | ⟨o, m₂⟩ <;>
    simp only [c2, reduceCtorEq] at hW
  obtain ⟨⟨lu, hdu⟩, ⟨lz, hdz⟩⟩ := hden dn s.mem a₀ vis fe M eb cT tbl hS hfe
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
  · rw [ite_eq_left b] at hW
    obtain ⟨hr0, hm⟩ := Prod.mk.inj (Option.some.inj hW)
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
    rw [ite_eq_right hno] at hT
    obtain ⟨okT, stT, resT⟩ := AM.of_run_ok _ _ _ _ hT
    refine ⟨okT, ⟨M2, by rw [stT, ← hm]; exact hS2, hK2, by rw [← hm]; exact hSt2⟩, ?_, ?_⟩
    · rw [resT]; simp only [decBool, ← hr0]; decide
    · unfold ResH HW; rw [← hr0]; decide
  rw [ite_eq_right b] at hW
  have hyes : decO (o.headD 0) = some true := by
    unfold decO
    have := mt UInt64.lt_iff_toNat_lt.mpr b
    have e2 : (2 : Word).toNat = 2 := rfl
    rw [e2] at this
    have h0 : o.headD 0 ≠ 0 := fun e => by rw [e] at this; simp at this
    have h1 : o.headD 0 ≠ 1 := fun e => by rw [e] at this; simp at this
    rw [ite_eq_right h0, ite_eq_right h1]
  rw [ite_eq_left hyes] at hT
  -- the words `field_sort_zero` reads, in the record pool of `m₂` (= the caller's)
  obtain ⟨w3, w4, h3, h4, hsl3⟩ := hlist?_slice' hlp
  obtain ⟨w11, w12, h11, h12, hsl11⟩ := hlist?_slice' hgd
  have hq12 : q.toNat + 12 < (s.mem.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp (by
    rw [show q.toNat + 12 = q.toNat + 11 + 1 by omega]; exact h12)).1
  have hrd3 : rdW (m₂.arr64 EREC) (q + 3) = w3 := by
    rw [hE2]; exact rdW_of_get (fo_toNat_add_small q 3 (by omega)) h3
  have hrd4 : rdW (m₂.arr64 EREC) (q + 4) = w4 := by
    rw [hE2]; exact rdW_of_get (fo_toNat_add_small q 4 (by omega)) (by
      rw [show q.toNat + 4 = q.toNat + 3 + 1 by omega]; exact h4)
  have hrd11 : rdW (m₂.arr64 EREC) (q + 11) = w11 := by
    rw [hE2]; exact rdW_of_get (fo_toNat_add_small q 11 (by omega)) h11
  have hrd12 : rdW (m₂.arr64 EREC) (q + 12) = w12 := by
    rw [hE2]; exact rdW_of_get (fo_toNat_add_small q 12 (by omega)) (by
      rw [show q.toNat + 12 = q.toNat + 11 + 1 by omega]; exact h12)
  -- the guard word
  have hfs : HW (foFs m₂ q i) ∧ decI (foFs m₂ q i) = tbl.guards.getD i.toNat default := by
    have hlen := hslice?_length hsl11
    simp only [foFs, hrd11, hrd12]
    by_cases hi : i < w12
    · rw [ite_eq_left hi]
      have hi' := UInt64.lt_iff_toNat_lt.mp hi
      obtain ⟨w, hw, hw32, hgw⟩ := hslice?_at' hsl11 i.toNat (by rw [← hlen] at *; omega)
      have hb := (Array.getElem?_eq_some_iff.mp hw).1
      have hrd : rdW (s.mem.arr64 EREC) (w11 + i) = w := by
        refine rdW_of_get ?_ hw
        rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      rw [hE2, hrd]
      refine ⟨hw32, ?_⟩
      rw [List.getD_eq_getElem?_getD, hgw]; rfl
    · rw [ite_eq_right hi]
      have hi' := mt UInt64.lt_iff_toNat_lt.mpr hi
      refine ⟨by unfold HW; decide, ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  obtain ⟨hRN, hks, hgd'⟩ := hden2 dn m₂ _ vis fe M2 eb cT tbl hS2 hfe
  have hstL : (AM.st (lvlEq? (decI w8) (decI (r₁.headD 0))) a₀).store = a₀.store :=
    lvlEq?_store _ _ _ _ _ lu lz hdu hdz hS.readL hrunL
  have hlps : hslice? (m₂.arr64 EREC) w3.toNat w4.toNat = some tbl.levelParams := by
    rw [hE2]; exact hsl3
  rcases c3 : callW p (n' + 2) "field_sort_zero" [rdW (m₂.arr64 EREC) (q + 3),
      rdW (m₂.arr64 EREC) (q + 4), us, foFs m₂ q i] m₂ with _ | ⟨r₃, m₃⟩ <;>
    simp only [c3, reduceCtorEq] at hW
  obtain ⟨hr0, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  rw [hrd3, hrd4] at c3
  obtain ⟨ok3, ⟨M3, hS3, hK3, hSt3⟩, res3, hr3⟩ := CoreSpec.of_callW
    (hfz (n' + 2) ⟨m₂, Locals.init []⟩ (AM.st (lvlEq? (decI w8) (decI (r₁.headD 0))) a₀) dn vis fe
      M2 eb w3 w4 us (foFs m₂ q i) tbl.levelParams hS2 hus hfs.1 hlps hRN hks
      (by rw [hstL]; exact husd) (by rw [hfs.2]; exact hgd' i.toNat hlt)) c3
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

/-! ## Under `CoreDen` (helper `whnf4-leaves`) -/

/-- `ProjSortDen` is `StoreDen.proj`'s sort and `StoreDen.zero`. -/
theorem projSortDen_of (hden : CoreDen) : ProjSortDen :=
  fun dn m a vis fe M eb _c _tbl hS hfe =>
    ⟨((hden dn m a vis fe M eb hS).proj _ _ hfe).1, (hden dn m a vis fe M eb hS).zero⟩

/-- `FireDen` is `StoreDen.readN` and `StoreDen.proj`'s guards and level parameters. -/
theorem fireDen_of (hden : CoreDen) : FireDen :=
  fun dn m a vis fe M eb _c _tbl hS hfe =>
    have hd := hden dn m a vis fe M eb hS
    ⟨hd.readN, (hd.proj _ _ hfe).2.2, (hd.proj _ _ hfe).2.1⟩

/-- **`fire_ok` refines `IProjEntry.fireOk` under `CoreS`**, `CoreDen` and lane `defeq`'s
`field_sort_zero`: the universe arguments are a stored `const` node's list, so they read back
(`StoreDen.constLs`). -/
theorem fireOk_core (p : Prog) (hp : FireProg p) (hfz : FieldSortZeroOK p) (hden : CoreDen) :
    FireOkOK p := by
  intro n s₀ a₀ dn vis fe M eb q i us tbl hS hus htbl hfe hlt ⟨h, c, hv⟩
  exact fireOk_refines p hp hfz (projSortDen_of hden) (fireDen_of hden) n s₀ a₀ dn vis fe M eb q i
    us tbl hS hus htbl hfe hlt ((hden dn s₀.mem a₀ vis fe M eb hS).constLs h c _ hv)

/-- **`tower_slots_all` refines `towerSlotsAll`**, on the real `find_proj`. -/
@[refines ConRon.Arena.towerSlotsAll]
theorem towerSlotsAll_refines (p : Prog) (hp : IotaProg' p) (hq : ProjProg p) :
    TowerSlotsAllOK p :=
  towerSlotsAll_refines' p hp (findProj_refines p hq) (projFound p hq)

end L.Arena
