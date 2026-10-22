import ConAgua.Arena.PromoteCIInfra

/-!
# `pn_at`, `pl_at`, `ps_at` and the stores, as relations

The handle promotions applied to a handle stored in the record pool: `pn_at(f, a)`
(`promoteN` of the name at `EREC[a]`), `pl_at`, `ps_at(k, f, a)` (a promoted slice of the
slice stored at `EREC[a], EREC[a + 1]`). The stores `erec_wrK` and `caps_wr`, `proj_wr`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- **What a promotion of one stored handle gives**: the twin's run succeeds with `dec r`,
the relations hold after, `r` is persistent, and the record pool is untouched. -/
def AtOk {α : Type} (op : AM (PMemo × α)) (dec : Word → α) (m : Mem) (a : AState) (r : Word)
    (m' : Mem) : Prop :=
  ∃ a' pm', op.run a = .ok ((pm', dec r), a') ∧ ArenaD m' a' ∧ PMemoR m' pm' ∧ PW r ∧
    cp a' = cp a ∧ MemFrame eArrs eCtl m m'

theorem eFrame_erec {m m' : Mem} (h : MemFrame eArrs eCtl m m') :
    m'.arr64 EREC = m.arr64 EREC ∧ erecTop m' = erecTop m := by
  refine ⟨h.1 EREC (by decide) (by decide), ?_⟩
  simp only [erecTop]; rw [h.2.1 129 (by decide)]

/-- **What a promoted stored slice gives**: a fresh slice at the old top. -/
def SlOk {k : IdxKind} (op : AM (PMemo × List (Idx k))) (m : Mem) (a : AState) (r : Word)
    (wl : Word) (m' : Mem) : Prop :=
  ∃ a' pm' us', op.run a = .ok ((pm', us'), a') ∧ ArenaD m' a' ∧ PMemoR m' pm' ∧
    cp a' = cp a ∧ MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ r.toNat = erecTop m ∧
    ErecGrow m m' ∧ erecTop m' = erecTop m + wl.toNat ∧ erecTop m' ≤ (m'.arr64 EREC).size ∧
    hslice? (erecP m') (erecTop m) wl.toNat = some us'

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem pnAt_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f addr : Word) (u : NIdx)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hu : hd? (erecP m) addr.toNat = some u) (hc : callW p n "pn_at" [f, addr] m = some (r, m')) :
    AtOk (promoteN pm f.toNat u) decI m a (r.headD 0) m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (pnAt_spec p hp n ⟨m, Locals.init []⟩ f addr) hc
  simp only at hW
  rw [hs'] at hW
  obtain ⟨w, hw, hwl, rfl⟩ := hd?_some hu
  have hw' := erecP_get hw
  simp only [pnAtW] at hW
  cases hca : callW p n "erec_rd1" [addr] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₁⟩ := x
  rw [hca] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨hm1, hr1, -⟩ := rd1_call p hp hca
  rw [rd1W_of hsz (by simpa using hw')] at hr1
  subst hr1
  obtain rfl := hm1.symm
  cases hcb : callW p n "promote_n" [f, g0 [w]] m with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₂⟩ := x
  rw [hcb] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have key : PNOk (promoteN pm f.toNat (decI w)) m a pm (r₂.headD 0) m₂ :=
    (pn_rel p hp n).1 m a pm f w r₂ m₂ hD hP hwl hcb
  obtain ⟨a', pm', hrun, hD', hP', hpw, hcp, hfr, -⟩ := key
  rw [← hr]
  exact ⟨a', pm', hrun, hD', hP', hpw, hcp, hfr.mono (by simp) (by simp)⟩

theorem plAt_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f addr : Word) (u : LIdx)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hu : hd? (erecP m) addr.toNat = some u) (hc : callW p n "pl_at" [f, addr] m = some (r, m')) :
    AtOk (promoteL pm f.toNat u) decI m a (r.headD 0) m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (plAt_spec p hp n ⟨m, Locals.init []⟩ f addr) hc
  simp only at hW
  rw [hs'] at hW
  obtain ⟨w, hw, hwl, rfl⟩ := hd?_some hu
  have hw' := erecP_get hw
  simp only [plAtW] at hW
  cases hca : callW p n "erec_rd1" [addr] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₁⟩ := x
  rw [hca] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨hm1, hr1, -⟩ := rd1_call p hp hca
  rw [rd1W_of hsz (by simpa using hw')] at hr1
  subst hr1
  obtain rfl := hm1.symm
  cases hcb : callW p n "promote_l" [f, g0 [w]] m with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₂⟩ := x
  rw [hcb] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have key : PLOk (promoteL pm f.toNat (decI w)) decI m a pm (r₂.headD 0) m₂ :=
    (pl_rel p hp n).1 m a pm f w r₂ m₂ hD hP hwl hcb
  obtain ⟨a', pm', hrun, hD', hP', hpw, hcp, hfr, -⟩ := key
  rw [← hr]
  exact ⟨a', pm', hrun, hD', hP', hpw, hcp, hfr.mono (by simp) (by simp)⟩

theorem psAt0_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f addr : Word) (us : List NIdx)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hu : hlist? (erecP m) addr.toNat = some us)
    (hc : callW p n "ps_at" [0, f, addr] m = some (r, m')) :
    ∃ wo wl : Word, nat? (erecP m) addr.toNat = some wo.toNat ∧
      nat? (erecP m) (addr.toNat + 1) = some wl.toNat ∧
      hslice? (erecP m) wo.toNat wl.toNat = some us ∧
      SlOk (promoteNList pm f.toNat us) m a (r.headD 0) wl m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (psAt_spec p hp n ⟨m, Locals.init []⟩ 0 f addr) hc
  simp only at hW
  rw [hs'] at hW
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hu
  obtain ⟨wo', ho, wl', hl, hsl⟩ := hu
  simp only [nat?, Option.map_eq_some_iff] at ho hl
  obtain ⟨wo, hwo, rfl⟩ := ho
  obtain ⟨wl, hwl, rfl⟩ := hl
  have hwo' := erecP_get hwo
  have hwl' := erecP_get hwl
  simp only [psAtW] at hW
  cases hca : callW p n "erec_rd2" [addr] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₁⟩ := x
  rw [hca] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨hm1, hr1, -⟩ := rd2_call p hp hca
  rw [rd2W_of hsz (by simpa using hwo') (by simpa using hwl')] at hr1
  subst hr1
  obtain rfl := hm1.symm
  cases hcb : callW p n "promote_slice" [0, f, g0 [wo, wl], g1 [wo, wl]] m with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₂⟩ := x
  rw [hcb] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have hslr : hslice? (m.arr64 EREC) wo.toNat wl.toNat = some us :=
    (erecP_ext m).hslice? hsl
  have hot : wo.toNat + wl.toNat ≤ erecTop m ∨ wl = 0 := by
    rcases hslice?_bound hsl with h0 | h0
    · right; exact UInt64.toNat_inj.mp (by simpa using h0)
    · left; have := erecP_size_le m; omega
  obtain ⟨hq, ht, hts, a', pm', us', hrun, hD', hP', hsl', hag, hsz', hcp, hfr⟩ :=
    sliceN_rel p hp n m a pm f wo wl us r₂ m₂ hD hP hslr hot hsz hcb
  have hqv : (r₂.headD 0).toNat = erecTop m := by rw [hq]; rfl
  refine ⟨wo, wl, by simp [nat?, hwo], by simp [nat?, hwl], hsl, a', pm', us', hrun, hD', hP', hcp, hfr, by rw [← hr]; exact hqv, ?_, ht, hts, ?_⟩
  · exact ⟨by omega, fun i hi => hag i hi, hsz'⟩
  · rw [hslice?_erecP hts (by omega)]
    exact hsl'

theorem psAt1_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f addr : Word) (us : List LIdx)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hu : hlist? (erecP m) addr.toNat = some us)
    (hc : callW p n "ps_at" [1, f, addr] m = some (r, m')) :
    ∃ wo wl : Word, nat? (erecP m) addr.toNat = some wo.toNat ∧
      nat? (erecP m) (addr.toNat + 1) = some wl.toNat ∧
      hslice? (erecP m) wo.toNat wl.toNat = some us ∧
      SlOk (promoteLList pm f.toNat us) m a (r.headD 0) wl m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (psAt_spec p hp n ⟨m, Locals.init []⟩ 1 f addr) hc
  simp only at hW
  rw [hs'] at hW
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hu
  obtain ⟨wo', ho, wl', hl, hsl⟩ := hu
  simp only [nat?, Option.map_eq_some_iff] at ho hl
  obtain ⟨wo, hwo, rfl⟩ := ho
  obtain ⟨wl, hwl, rfl⟩ := hl
  have hwo' := erecP_get hwo
  have hwl' := erecP_get hwl
  simp only [psAtW] at hW
  cases hca : callW p n "erec_rd2" [addr] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₁⟩ := x
  rw [hca] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨hm1, hr1, -⟩ := rd2_call p hp hca
  rw [rd2W_of hsz (by simpa using hwo') (by simpa using hwl')] at hr1
  subst hr1
  obtain rfl := hm1.symm
  cases hcb : callW p n "promote_slice" [1, f, g0 [wo, wl], g1 [wo, wl]] m with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₂⟩ := x
  rw [hcb] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have hslr : hslice? (m.arr64 EREC) wo.toNat wl.toNat = some us :=
    (erecP_ext m).hslice? hsl
  have hot : wo.toNat + wl.toNat ≤ erecTop m ∨ wl = 0 := by
    rcases hslice?_bound hsl with h0 | h0
    · right; exact UInt64.toNat_inj.mp (by simpa using h0)
    · left; have := erecP_size_le m; omega
  obtain ⟨hq, ht, hts, a', pm', us', hrun, hD', hP', hsl', hag, hsz', hcp, hfr⟩ :=
    sliceL_rel p hp n m a pm f wo wl us r₂ m₂ hD hP hslr hot hsz hcb
  have hqv : (r₂.headD 0).toNat = erecTop m := by rw [hq]; rfl
  refine ⟨wo, wl, by simp [nat?, hwo], by simp [nat?, hwl], hsl, a', pm', us', hrun, hD', hP', hcp, hfr, by rw [← hr]; exact hqv, ?_, ht, hts, ?_⟩
  · exact ⟨by omega, fun i hi => hag i hi, hsz'⟩
  · rw [hslice?_erecP hts (by omega)]
    exact hsl'

theorem psAt2_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f addr : Word) (us : List EIdx)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hu : hlist? (erecP m) addr.toNat = some us)
    (hc : callW p n "ps_at" [2, f, addr] m = some (r, m')) :
    ∃ wo wl : Word, nat? (erecP m) addr.toNat = some wo.toNat ∧
      nat? (erecP m) (addr.toNat + 1) = some wl.toNat ∧
      hslice? (erecP m) wo.toNat wl.toNat = some us ∧
      SlOk (promoteEList pm f.toNat us) m a (r.headD 0) wl m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (psAt_spec p hp n ⟨m, Locals.init []⟩ 2 f addr) hc
  simp only at hW
  rw [hs'] at hW
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hu
  obtain ⟨wo', ho, wl', hl, hsl⟩ := hu
  simp only [nat?, Option.map_eq_some_iff] at ho hl
  obtain ⟨wo, hwo, rfl⟩ := ho
  obtain ⟨wl, hwl, rfl⟩ := hl
  have hwo' := erecP_get hwo
  have hwl' := erecP_get hwl
  simp only [psAtW] at hW
  cases hca : callW p n "erec_rd2" [addr] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₁⟩ := x
  rw [hca] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨hm1, hr1, -⟩ := rd2_call p hp hca
  rw [rd2W_of hsz (by simpa using hwo') (by simpa using hwl')] at hr1
  subst hr1
  obtain rfl := hm1.symm
  cases hcb : callW p n "promote_slice" [2, f, g0 [wo, wl], g1 [wo, wl]] m with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₂⟩ := x
  rw [hcb] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have hslr : hslice? (m.arr64 EREC) wo.toNat wl.toNat = some us :=
    (erecP_ext m).hslice? hsl
  have hot : wo.toNat + wl.toNat ≤ erecTop m ∨ wl = 0 := by
    rcases hslice?_bound hsl with h0 | h0
    · right; exact UInt64.toNat_inj.mp (by simpa using h0)
    · left; have := erecP_size_le m; omega
  obtain ⟨hq, ht, hts, a', pm', us', hrun, hD', hP', hsl', hag, hsz', hcp, hfr⟩ :=
    sliceE_rel p hp n m a pm f wo wl us r₂ m₂ hD hP hslr hot hsz hcb
  have hqv : (r₂.headD 0).toNat = erecTop m := by rw [hq]; rfl
  refine ⟨wo, wl, by simp [nat?, hwo], by simp [nat?, hwl], hsl, a', pm', us', hrun, hD', hP', hcp, hfr, by rw [← hr]; exact hqv, ?_, ht, hts, ?_⟩
  · exact ⟨by omega, fun i hi => hag i hi, hsz'⟩
  · rw [hslice?_erecP hts (by omega)]
    exact hsl'

end rel

end L.Arena
