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


namespace L.Arena

/-- **What a promotion of one stored handle gives**: the twin's run succeeds with `dec r`,
the relations hold after, `r` is persistent, and the record pool is untouched. -/
def AtOk {α : Type} (op : AM (PMemo × α)) (dec : Word → α) (m : Mem) (a : AState) (r : Word)
    (m' : Mem) : Prop :=
  ∃ a' pm', op.run a = .ok ((pm', dec r), a') ∧ ArenaD m' a' ∧ PMemoR m' pm' ∧ PW r ∧
    cp a' = cp a ∧ MemFrame eArrs eCtl m m' ∧ TierKeep m m'

theorem eFrame_erec {m m' : Mem} (h : MemFrame eArrs eCtl m m') :
    m'.arr64 EREC = m.arr64 EREC ∧ erecTop m' = erecTop m := by
  refine ⟨h.1 EREC (by decide) (by decide), ?_⟩
  simp only [erecTop]; rw [h.2.1 129 (by decide)]

/-- A promotion's frame inside the record pool's (by membership: `simp` over the long array
lists runs out of recursion depth). -/
theorem eFrame_cons {m m' : Mem} (h : MemFrame eArrs eCtl m m') :
    MemFrame (EREC :: eArrs) (129 :: eCtl) m m' :=
  h.mono (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => List.mem_cons_of_mem _ h)

/-- **What a promoted stored slice gives**: a fresh slice at the old top. -/
def SlOk {k : IdxKind} (op : AM (PMemo × List (Idx k))) (m : Mem) (a : AState) (r : Word)
    (wl : Word) (m' : Mem) : Prop :=
  ∃ a' pm' us', op.run a = .ok ((pm', us'), a') ∧ ArenaD m' a' ∧ PMemoR m' pm' ∧
    cp a' = cp a ∧ MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ r.toNat = erecTop m ∧
    ErecGrow m m' ∧ erecTop m' = erecTop m + wl.toNat ∧ erecTop m' ≤ (m'.arr64 EREC).size ∧
    hslice? (erecP m') (erecTop m) wl.toNat = some us' ∧ TierKeep m m'

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`pn_at`, `pl_at`**: the stored handle read (`erec_rd1`), promoted by `g` (its relation
`hrel`). -/
theorem at_gen {k : IdxKind} {fa g : FnName} {W : Prog → Nat → Mem → Word → Word → Option (Word × Mem)}
    {T : PMemo → Nat → Idx k → AM (PMemo × Idx k)}
    (hs : ∀ n s₀ f addr, ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) fa [f, addr]
      ⦃fun r s' => LocEq s' s₀ ∧ W p n s₀.mem f addr = some (r.headD 0, s'.mem); ⊤⦄)
    (hW₀ : ∀ n m f addr, W p n m f addr = (callW p n "erec_rd1" [addr] m).bind fun r =>
      (callW p n g [f, g0 r.1] r.2).bind fun x => some (g0 x.1, x.2))
    (hrel : ∀ n m a pm f w r m', ArenaD m a → PMemoR m pm → w.toNat < 2 ^ 32 →
      callW p n g [f, w] m = some (r, m') → AtOk (T pm f.toNat (decI w)) decI m a (r.headD 0) m')
    (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f addr : Word) (u : Idx k)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hu : hd? (erecP m) addr.toNat = some u) (hc : callW p n fa [f, addr] m = some (r, m')) :
    AtOk (T pm f.toNat u) decI m a (r.headD 0) m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (hs n ⟨m, Locals.init []⟩ f addr) hc
  simp only at hW
  rw [hs'] at hW
  obtain ⟨w, hw, hwl, rfl⟩ := hd?_some hu
  have hw' := erecP_get hw
  simp only [hW₀] at hW
  obtain ⟨⟨r₁, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm1, hr1, -⟩ := rd1_call p hp hca
  rw [rd1W_of hsz (by simpa using hw')] at hr1
  subst hr1
  obtain rfl := hm1.symm
  obtain ⟨⟨r₂, m₂⟩, hcb, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  rw [← hr]
  exact hrel n m a pm f w r₂ m₂ hD hP hwl hcb


theorem pnAt_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f addr : Word) (u : NIdx)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hu : hd? (erecP m) addr.toNat = some u) (hc : callW p n "pn_at" [f, addr] m = some (r, m')) :
    AtOk (promoteN pm f.toNat u) decI m a (r.headD 0) m' :=
  at_gen p hp (pnAt_spec p hp) (fun _ _ _ _ => rfl) (fun n m a pm f w r m' hD hP hw hc => by
    obtain ⟨a', pm', hrun, hD', hP', hpw, hcp, hfr, -⟩ := (pn_rel p hp n).1 m a pm f w r m' hD hP hw hc
    exact ⟨a', pm', hrun, hD', hP', hpw, hcp, hfr.mono (by simp) (by simp), TierKeep.of_frame hfr (by decide)⟩) n m a pm f addr u r m' hD hP hsz hu hc

theorem plAt_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f addr : Word) (u : LIdx)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hu : hd? (erecP m) addr.toNat = some u) (hc : callW p n "pl_at" [f, addr] m = some (r, m')) :
    AtOk (promoteL pm f.toNat u) decI m a (r.headD 0) m' :=
  at_gen p hp (plAt_spec p hp) (fun _ _ _ _ => rfl) (fun n m a pm f w r m' hD hP hw hc => by
    obtain ⟨a', pm', hrun, hD', hP', hpw, hcp, hfr, -⟩ := (pl_rel p hp n).1 m a pm f w r m' hD hP hw hc
    exact ⟨a', pm', hrun, hD', hP', hpw, hcp, hfr.mono (by simp) (by simp), TierKeep.of_frame hfr (by decide)⟩) n m a pm f addr u r m' hD hP hsz hu hc

/-- **`ps_at(k, f, a)`**: the stored slice read (`erec_rd2`), promoted by `promote_slice(k, …)`
(the kind's list promotion `gl`, its relation `hlist`). -/
theorem psAt_gen {k : IdxKind} (kw : Word) (gl : FnName)
    (TL : PMemo → Nat → List (Idx k) → AM (PMemo × List (Idx k)))
    (hk : ∀ n f o l r m₁, sliceK p n kw f o l (some (r, m₁)) =
      offK (r.headD 0) (callW p n gl [f, o, l, r.headD 0] m₁))
    (hlist : PListRel p gl TL)
    (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f addr : Word) (us : List (Idx k))
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hu : hlist? (erecP m) addr.toNat = some us)
    (hc : callW p n "ps_at" [kw, f, addr] m = some (r, m')) :
    ∃ wo wl : Word, nat? (erecP m) addr.toNat = some wo.toNat ∧
      nat? (erecP m) (addr.toNat + 1) = some wl.toNat ∧
      hslice? (erecP m) wo.toNat wl.toNat = some us ∧
      SlOk (TL pm f.toNat us) m a (r.headD 0) wl m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (psAt_spec p hp n ⟨m, Locals.init []⟩ kw f addr) hc
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
  obtain ⟨⟨r₁, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm1, hr1, -⟩ := rd2_call p hp hca
  rw [rd2W_of hsz (by simpa using hwo') (by simpa using hwl')] at hr1
  subst hr1
  obtain rfl := hm1.symm
  obtain ⟨⟨r₂, m₂⟩, hcb, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have hslr : hslice? (m.arr64 EREC) wo.toNat wl.toNat = some us :=
    (erecP_ext m).hslice? hsl
  have hot : wo.toNat + wl.toNat ≤ erecTop m ∨ wl = 0 := by
    rcases hslice?_bound hsl with h0 | h0
    · right; exact UInt64.toNat_inj.mp (by simpa using h0)
    · left; have := erecP_size_le m; omega
  obtain ⟨hq, ht, hts, a', pm', us', hrun, hD', hP', hsl', hag, hsz', hcp, hfr, htk⟩ :=
    slice_gen p hp kw gl TL hk hlist n m a pm f wo wl us r₂ m₂ hD hP hslr hot hsz hcb
  have hqv : (r₂.headD 0).toNat = erecTop m := by rw [hq]; rfl
  refine ⟨wo, wl, by simp [nat?, hwo], by simp [nat?, hwl], hsl, a', pm', us', hrun, hD', hP', hcp, hfr, by rw [← hr]; exact hqv, ?_, ht, hts, ?_⟩
  · exact ⟨by omega, fun i hi => hag i hi, hsz'⟩
  · rw [hslice?_erecP hts (by omega)]
    exact ⟨hsl', htk⟩


theorem psAt0_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f addr : Word) (us : List NIdx)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hu : hlist? (erecP m) addr.toNat = some us)
    (hc : callW p n "ps_at" [0, f, addr] m = some (r, m')) :
    ∃ wo wl : Word, nat? (erecP m) addr.toNat = some wo.toNat ∧
      nat? (erecP m) (addr.toNat + 1) = some wl.toNat ∧
      hslice? (erecP m) wo.toNat wl.toNat = some us ∧
      SlOk (promoteNList pm f.toNat us) m a (r.headD 0) wl m' :=
  psAt_gen p hp 0 "promote_n_list" promoteNList (fun _ _ _ _ _ _ => by simp [sliceK]) (nlist_rel p hp) n m a pm f addr us r m'
    hD hP hsz hu hc

theorem psAt1_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f addr : Word) (us : List LIdx)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hu : hlist? (erecP m) addr.toNat = some us)
    (hc : callW p n "ps_at" [1, f, addr] m = some (r, m')) :
    ∃ wo wl : Word, nat? (erecP m) addr.toNat = some wo.toNat ∧
      nat? (erecP m) (addr.toNat + 1) = some wl.toNat ∧
      hslice? (erecP m) wo.toNat wl.toNat = some us ∧
      SlOk (promoteLList pm f.toNat us) m a (r.headD 0) wl m' :=
  psAt_gen p hp 1 "promote_l_list" promoteLList (fun _ _ _ _ _ _ => by simp [sliceK]) (llist_rel p hp) n m a pm f addr us r m'
    hD hP hsz hu hc

theorem psAt2_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f addr : Word) (us : List EIdx)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hu : hlist? (erecP m) addr.toNat = some us)
    (hc : callW p n "ps_at" [2, f, addr] m = some (r, m')) :
    ∃ wo wl : Word, nat? (erecP m) addr.toNat = some wo.toNat ∧
      nat? (erecP m) (addr.toNat + 1) = some wl.toNat ∧
      hslice? (erecP m) wo.toNat wl.toNat = some us ∧
      SlOk (promoteEList pm f.toNat us) m a (r.headD 0) wl m' :=
  psAt_gen p hp 2 "promote_e_list" promoteEList (fun _ _ _ _ _ _ => by simp [sliceK]) (elist_rel p hp) n m a pm f addr us r m'
    hD hP hsz hu hc

end rel

end L.Arena
