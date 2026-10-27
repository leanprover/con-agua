import ConAgua.Arena.PromoteCIRef.Alloc
import ConAgua.Arena.PromoteCIRef.HlistUnfold
import ConAgua.Arena.PromoteCIRef.Hslice
import ConAgua.Arena.PromoteCIRef.NatMove
import ConAgua.Arena.PromoteCIRef.PreECongr
import ConAgua.Arena.PromoteCIRef.PmDecRuleWords
import ConRon.Bridge.Grind

/-!
# Proj

`AtOk`, `eFrame_erec`, `eFrame_cons`, `SlOk`, `at_gen`, `pnAt_rel` and the lemmas only they use.
-/

section

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

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem projWr_call {n : Nat} {d sn lp c ss bs gs : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "proj_wr" [d, sn, lp, c, ss, bs, gs] m = some (r, m')) :
    stP d m [((2 : Word), sn), ((3 : Word), lp), ((6 : Word), c),
      ((8 : Word), ss), ((9 : Word), bs), ((11 : Word), gs)] = some m' := by
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (projWr_spec p hp n ⟨m, Locals.init []⟩ d sn lp c ss bs gs) hc; exact hW

end rel

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem projWr_rel' {n : Nat} {d sn lp c ss bs gs : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 12 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "proj_wr" [d, sn, lp, c, ss, bs, gs] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, i ≠ d.toNat + 2 → i ≠ d.toNat + 3 → i ≠ d.toNat + 6 →
      i ≠ d.toNat + 8 → i ≠ d.toNat + 9 → i ≠ d.toNat + 11 →
      (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 2]? = some sn ∧
    (m'.arr64 EREC)[d.toNat + 3]? = some lp ∧ (m'.arr64 EREC)[d.toNat + 6]? = some c ∧
    (m'.arr64 EREC)[d.toNat + 8]? = some ss ∧ (m'.arr64 EREC)[d.toNat + 9]? = some bs ∧
    (m'.arr64 EREC)[d.toNat + 11]? = some gs := by
  have h := projWr_call p hp hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := stP_nat d _ (by simp; omega) (by simp) h
  refine ⟨h1, h2, fun i hi2 hi3 hi4 hi5 hi6 hi7 => h3 i ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      show (((2 : Word)).toNat = 2) from rfl,
      show (((3 : Word)).toNat = 3) from rfl, show (((6 : Word)).toNat = 6) from rfl,
      show (((8 : Word)).toNat = 8) from rfl, show (((9 : Word)).toNat = 9) from rfl,
      show (((11 : Word)).toNat = 11) from rfl]
    omega
  · simpa using h5

end rel

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem decTbl_move {a b : Array Word} {q d : Nat} {tbl : IProjTable} {sn c : NIdx} {ss : LIdx}
    {lp : List NIdx} {gs : List LIdx} {bs : List EIdx}
    (hA : decTbl a q = some tbl)
    (hw5 : b[d + 5]? = a[q + 5]?) (hw7 : b[d + 7]? = a[q + 7]?)
    (hsn : hd? b (d + 2) = some sn)
    (hlp : hlist? b (d + 3) = some lp) (hc : hd? b (d + 6) = some c)
    (hss : hd? b (d + 8) = some ss) (hbs : hlist? b (d + 9) = some bs)
    (hgs : hlist? b (d + 11) = some gs) :
    decTbl b d = some ⟨sn, lp, tbl.numParams, c, tbl.numFields, ss, bs.toArray, gs⟩ := by
  unfold decTbl at hA ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hA ⊢
  obtain ⟨e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, e8, h8, e9, h9, rfl⟩ := hA
  exact ⟨sn, hsn, lp, hlp, e4, nat?_move hw5 h4, c, hc, e6, nat?_move hw7 h6, ss, hss,
    bs, hbs, gs, hgs, rfl⟩

theorem pmDecTbl_words {a : Array Word} {q : Nat} {tbl : IProjTable} (h : decTbl a q = some tbl) :
    hd? a (q + 2) = some tbl.structName ∧
    hlist? a (q + 3) = some tbl.levelParams ∧ hd? a (q + 6) = some tbl.ctor ∧
    hd? a (q + 8) = some tbl.structSort ∧ hlist? a (q + 9) = some tbl.bodies.toList ∧
    hlist? a (q + 11) = some tbl.guards := by
  unfold decTbl at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, e8, h8, e9, h9, rfl⟩ := h
  exact ⟨h2, h3, h5, h7, by simpa using h8, h9⟩

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem projA_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (sn : NIdx)
    (lps : List NIdx) (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hqb : q.toNat + 13 ≤ (m.arr64 EREC).size)
    (hsn : hd? (erecP m) (q.toNat + 2) = some sn)
    (hlp : hlist? (erecP m) (q.toNat + 3) = some lps)
    (hc : callW p n "proj_a" [f, q] m = some (r, m')) :
    ∃ (a1 : AState) (pm1 : PMemo) (a3 : AState) (pm3 : PMemo)
      (sn' : NIdx) (lps' : List NIdx) (wl : Word),
      (promoteN pm f.toNat sn).run a = .ok ((pm1, sn'), a1) ∧
      (promoteNList pm1 f.toNat lps).run a1 = .ok ((pm3, lps'), a3) ∧
      ArenaD m' a3 ∧ PMemoR m' pm3 ∧ cp a3 = cp a ∧
      MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' ∧ ErecGrow m m' ∧
      erecTop m' ≤ (m'.arr64 EREC).size ∧
      PW (g0 r) ∧ decI (g0 r) = sn' ∧
      nat? (erecP m) (q.toNat + 3 + 1) = some wl.toNat ∧ (g1 r).toNat = erecTop m ∧
      erecTop m' = erecTop m + wl.toNat ∧ hslice? (erecP m') (erecTop m) wl.toNat = some lps' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (projA_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [projAW] at hW
  have e2 : (q + 2).toNat = q.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : (q + 3).toNat = q.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨⟨c6, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, hrun1, hD1, hP1, hpw1, hcp1, hfr1, htk1⟩ :=
    pnAt_rel p hp n m a pm f (q + 2) sn c6 m₁ hD hP hsz (by rw [e2]; exact hsn) hca
  obtain ⟨hE1, hT1⟩ := eFrame_erec hfr1
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hE1]; exact hsz
  have hP1' : erecP m₁ = erecP m := by
    rw [erecP_eq_preE, erecP_eq_preE, hT1]; exact preE_congr hE1 _
  obtain ⟨⟨c8, m₃⟩, hcc, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨wo, wl, hn1, hn1', hsl1, a3, pm3, lps', hrun3, hD3, hP3, hcp3, hfr3, hq3, hg3, hT3, hts3,
    hsl3, htk3⟩ := psAt0_rel p hp n m₁ a1 pm1 f (q + 3) lps c8 m₃ hD1 hP1 hsz1
      (by rw [hP1', e3]; exact hlp) hcc
  obtain ⟨hlist, hm3⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm3
  obtain ⟨h0, hrest⟩ := List.cons.inj hlist
  obtain ⟨h1, -⟩ := List.cons.inj hrest
  have hg03 : ErecGrow m m₃ :=
    ⟨by rw [← hT1]; exact hg3.1, fun i hi => by
      rw [hg3.2.1 i (by rw [hT1]; exact hi), hE1], by rw [hg3.2.2, hE1]⟩
  refine ⟨a1, pm1, a3, pm3, decI (c6.headD 0), lps', wl, hrun1,
    hrun3, hD3, hP3, hcp3.trans hcp1,
    (eFrame_cons hfr1).trans hfr3, htk1.trans htk3, hg03, hts3,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h0]; exact hpw1
  · rw [← h0]
  · rw [← e3, hP1'] at *; exact hn1'
  · rw [← h1, hq3, hT1]
  · rw [hT3, hT1]
  · rw [hT1] at hsl3; exact hsl3

end rel

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem projB_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (ct : NIdx)
    (ss : LIdx) (bodies : List EIdx) (guards : List LIdx) (r : List Word) (m' : Mem)
    (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hqb : q.toNat + 13 ≤ (m.arr64 EREC).size)
    (hct : hd? (erecP m) (q.toNat + 6) = some ct) (hss : hd? (erecP m) (q.toNat + 8) = some ss)
    (hbs : hlist? (erecP m) (q.toNat + 9) = some bodies)
    (hgs : hlist? (erecP m) (q.toNat + 11) = some guards)
    (hc : callW p n "proj_b" [f, q] m = some (r, m')) :
    ∃ (a1 : AState) (pm1 : PMemo) (a2 : AState) (pm2 : PMemo) (a3 : AState) (pm3 : PMemo)
      (a4 : AState) (pm4 : PMemo) (c' : NIdx) (ss' : LIdx) (bs' : List EIdx) (gs' : List LIdx)
      (wlb wlg : Word),
      (promoteN pm f.toNat ct).run a = .ok ((pm1, c'), a1) ∧
      (promoteL pm1 f.toNat ss).run a1 = .ok ((pm2, ss'), a2) ∧
      (promoteEList pm2 f.toNat bodies).run a2 = .ok ((pm3, bs'), a3) ∧
      (promoteLList pm3 f.toNat guards).run a3 = .ok ((pm4, gs'), a4) ∧
      ArenaD m' a4 ∧ PMemoR m' pm4 ∧ cp a4 = cp a ∧
      MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' ∧ ErecGrow m m' ∧
      erecTop m' ≤ (m'.arr64 EREC).size ∧
      PW (g0 r) ∧ decI (g0 r) = c' ∧ PW (g1 r) ∧ decI (g1 r) = ss' ∧
      nat? (erecP m) (q.toNat + 9 + 1) = some wlb.toNat ∧
      nat? (erecP m) (q.toNat + 11 + 1) = some wlg.toNat ∧
      (g2 r).toNat = erecTop m ∧ (g3 r).toNat = erecTop m + wlb.toNat ∧
      erecTop m' = erecTop m + wlb.toNat + wlg.toNat ∧
      hslice? (erecP m') (erecTop m) wlb.toNat = some bs' ∧
      hslice? (erecP m') (erecTop m + wlb.toNat) wlg.toNat = some gs' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (projB_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [projBW] at hW
  have e6 : (q + 6).toNat = q.toNat + 6 := by rw [UInt64.toNat_add]; simp; omega
  have e8 : (q + 8).toNat = q.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have e9 : (q + 9).toNat = q.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have e11 : (q + 11).toNat = q.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨⟨c9, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, hrun1, hD1, hP1, hpw1, hcp1, hfr1, htk1⟩ :=
    pnAt_rel p hp n m a pm f (q + 6) ct c9 m₁ hD hP hsz (by rw [e6]; exact hct) hca
  obtain ⟨hE1, hT1⟩ := eFrame_erec hfr1
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hE1]; exact hsz
  have hP1' : erecP m₁ = erecP m := by
    rw [erecP_eq_preE, erecP_eq_preE, hT1]; exact preE_congr hE1 _
  obtain ⟨⟨c10, m₂⟩, hcb, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a2, pm2, hrun2, hD2, hP2, hpw2, hcp2, hfr2, htk2⟩ :=
    plAt_rel p hp n m₁ a1 pm1 f (q + 8) ss c10 m₂ hD1 hP1 hsz1 (by rw [hP1', e8]; exact hss) hcb
  obtain ⟨hE2, hT2⟩ := eFrame_erec hfr2
  have hsz2 : (m₂.arr64 EREC).size < 2 ^ 64 := by rw [hE2]; exact hsz1
  have hP2' : erecP m₂ = erecP m₁ := by
    rw [erecP_eq_preE, erecP_eq_preE, hT2]; exact preE_congr hE2 _
  obtain ⟨⟨c11, m₃⟩, hcc, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨wo3, wl3, hn3, hn3', hsl3, a3, pm3, bs', hrun3, hD3, hP3, hcp3, hfr3, hq3, hg3, hT3, hts3,
    hsl3', htk3⟩ := psAt2_rel p hp n m₂ a2 pm2 f (q + 9) bodies c11 m₃ hD2 hP2 hsz2
      (by rw [hP2', hP1', e9]; exact hbs) hcc
  have hsz3 : (m₃.arr64 EREC).size < 2 ^ 64 := by rw [hg3.2.2]; exact hsz2
  obtain ⟨⟨c12, m₄⟩, hcd, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨wo4, wl4, hn4, hn4', hsl4, a4, pm4, gs', hrun4, hD4, hP4, hcp4, hfr4, hq4, hg4, hT4, hts4,
    hsl4', htk4⟩ := psAt1_rel p hp n m₃ a3 pm3 f (q + 11) guards c12 m₄ hD3 hP3 hsz3
      (by rw [e11]; exact hg3.ext.hlist? (by rw [hP2', hP1']; exact hgs)) hcd
  obtain ⟨hlist, hm4⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm4
  -- the length word of the guards, read in the original pool
  obtain ⟨og, cg, hog, hcg, -⟩ := hlist?_unfold hgs
  have hcg3 : nat? (erecP m₃) (q.toNat + 11 + 1) = some cg := hg3.ext.nat? (by rw [hP2', hP1']; exact hcg)
  rw [e11] at hn4'
  have hcgw : cg = wl4.toNat := Option.some.inj (hcg3.symm.trans hn4')
  have hg04 : ErecGrow m m₄ :=
    ⟨by rw [← hT1, ← hT2]; exact Nat.le_trans hg3.1 hg4.1, fun i hi => by
      rw [hg4.2.1 i (by rw [hT3, hT2, hT1]; omega), hg3.2.1 i (by rw [hT2, hT1]; exact hi), hE2, hE1],
      by rw [hg4.2.2, hg3.2.2, hE2, hE1]⟩
  refine ⟨a1, pm1, a2, pm2, a3, pm3, a4, pm4, decI (c9.headD 0), decI (c10.headD 0), bs', gs',
    wl3, wl4, hrun1, hrun2, hrun3, hrun4, hD4, hP4, hcp4.trans (hcp3.trans (hcp2.trans hcp1)),
    (((eFrame_cons hfr1).trans (eFrame_cons hfr2)).trans hfr3).trans hfr4,
    htk1.trans (htk2.trans (htk3.trans htk4)),
    hg04, hts4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hlist]; exact hpw1
  · rw [← hlist] <;> rfl
  · rw [← hlist]; exact hpw2
  · rw [← hlist] <;> rfl
  · rw [e9, hP2', hP1'] at hn3'; exact hn3'
  · rw [← hcgw]; exact hcg
  · rw [← hlist]; simp only [g2, List.headD_cons, List.tail_cons]; rw [hq3, hT2, hT1]
  · rw [← hlist]; simp only [g3, List.headD_cons, List.tail_cons]; rw [hq4, hT3, hT2, hT1]
  · rw [hT4, hT3, hT2, hT1]
  · rw [hT2, hT1] at hsl3'; exact hg4.ext.hslice? hsl3'
  · rw [hT3, hT2, hT1] at hsl4'; exact hsl4'

end rel

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem arenaD_ctl129 {m m' : Mem} {a : AState} {pm : PMemo} (hD : ArenaD m a) (hP : PMemoR m pm)
    (hf : MemFrame [] [129] m m') : ArenaD m' a ∧ PMemoR m' pm :=
  ⟨⟨ArenaR.frame_ext _ _ (by simp) (by simp) m _ hf a hD.1,
    DerR.frameM _ _ m _ hf (by simp) a hD.2⟩, hP.frame (by simp) (by simp) hf⟩

theorem ErecGrow.of_alloc {m m' : Mem} {k : Nat} (hE : m'.arr64 EREC = m.arr64 EREC)
    (hT : erecTop m' = erecTop m + k) : ErecGrow m m' :=
  ⟨by omega, fun i _ => by rw [hE], by rw [hE]⟩

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem proj_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (D : Nat)
    (tbl : IProjTable) (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hts : erecTop m ≤ (m.arr64 EREC).size)
    (htbl : decTbl (preE m D) q.toNat = some tbl)
    (hqD : q.toNat + 13 ≤ D) (hDt : D ≤ erecTop m)
    (hc : callW p n "promote_proj_table" [f, q] m = some (r, m')) :
    ∃ a' pm' tbl', (promoteProjTable pm f.toNat tbl).run a = .ok ((pm', tbl'), a') ∧
      ArenaD m' a' ∧ PMemoR m' pm' ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' ∧ ErecGrow m m' ∧
      erecTop m' ≤ (m'.arr64 EREC).size ∧ (r.headD 0).toNat = erecTop m ∧
      (r.headD 0).toNat + 13 ≤ erecTop m' ∧
      decTbl (erecP m') (r.headD 0).toNat = some tbl' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteProj_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [projW] at hW
  cases n with
  | zero => simp only [callW_zero', Option.bind_none] at hW; cases hW
  | succ n =>
  obtain ⟨hsn, hlp, hct, hss, hbs, hgs⟩ := pmDecTbl_words htbl
  have hqb : q.toNat + 13 ≤ (m.arr64 EREC).size := by omega
  -- the allocation
  obtain ⟨⟨r5, ma⟩, hal, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hd5, hTa, hroom, hfa, hEa⟩ := alloc_rel p hp hal
  have hTa' : erecTop ma = erecTop m + 13 := by rw [hTa]; rfl
  have hga : ErecGrow m ma := ErecGrow.of_alloc hEa hTa'
  obtain ⟨hDa, hPa⟩ := arenaD_ctl129 hD hP hfa
  have hsza : (ma.arr64 EREC).size < 2 ^ 64 := by rw [hEa]; exact hsz
  have htsa : erecTop ma ≤ (ma.arr64 EREC).size := by
    rw [hEa, hTa']; have h := hroom; simp only [show ((13 : Word)).toNat = 13 from rfl] at h; exact h
  have hlift : ∀ {α : Type} (g : Array Word → Option α) (x : α),
      (∀ {a b : Array Word} (h : ArrExt a b) (y : α), g a = some y → g b = some y) →
      g (erecP m) = some x → g (erecP ma) = some x := fun g x hg h => hg hga.ext x h
  have h4 : ∀ {k : IdxKind} (i : Nat) (x : Idx k), hd? (preE m D) i = some x →
      hd? (erecP ma) i = some x := fun i x h =>
    hga.ext.hd? ((preE_mono m hDt).hd? h)
  have h4l : ∀ {k : IdxKind} (i : Nat) (x : List (Idx k)), hlist? (preE m D) i = some x →
      hlist? (erecP ma) i = some x := fun i x h =>
    hga.ext.hlist? ((preE_mono m hDt).hlist? h)
  -- proj_a
  obtain ⟨⟨ra, mb⟩, hpa, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, a3, pm3, sn', lps', wl, hrun1, hrun3, hDb, hPb, hcpb, hfb, htkb,
    hgb, htsb, hpws, hds, hwl, hptr, hTb, hslb⟩ :=
    projA_rel p hp (n + 1) ma a pm f q tbl.structName tbl.levelParams ra mb hDa hPa
      hsza (by rw [hEa]; exact hqb) (h4 _ _ hsn) (h4l _ _ hlp) hpa
  have hszb : (mb.arr64 EREC).size < 2 ^ 64 := by rw [hgb.2.2]; exact hsza
  -- proj_b
  obtain ⟨⟨rb, mc⟩, hpb, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  have hg0b : ErecGrow m mb := hga.trans hgb
  obtain ⟨b1, qm1, b2, qm2, b3, qm3, b4, qm4, c', ss', bs', gs', wlb, wlg, hrunc, hruns, hrunb, hrung,
    hDc, hPc, hcpc, hfc, htkc, hgc, htsc, hpwc, hdc, hpwss, hdss, hwlb, hwlg, hptrb, hptrg, hTc, hslbs,
    hslgs⟩ :=
    projB_rel p hp (n + 1) mb a3 pm3 f q tbl.ctor tbl.structSort tbl.bodies.toList tbl.guards rb mc
      hDb hPb hszb (by rw [hgb.2.2, hEa]; exact hqb)
      (hgb.ext.hd? (h4 _ _ hct)) (hgb.ext.hd? (h4 _ _ hss)) (hgb.ext.hlist? (h4l _ _ hbs))
      (hgb.ext.hlist? (h4l _ _ hgs)) hpb
  have hgc0 : ErecGrow m mc := hg0b.trans hgc
  have hdv : (r5.headD 0).toNat = erecTop m := hd5
  have hszc : (mc.arr64 EREC).size = (m.arr64 EREC).size := by
    rw [hgc0.2.2]
  have keyc : ∀ i < erecTop m, (mc.arr64 EREC)[i]? = (m.arr64 EREC)[i]? := hgc0.2.1
  -- the copy
  obtain ⟨⟨z, md⟩, hcp, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨k1, k2, k3, k4⟩ := cp_rel p hp (n + 1) mc (r5.headD 0) q 13 z md
    (by simp only [show ((13 : Word)).toNat = 13 from rfl]; omega)
    (by simp only [show ((13 : Word)).toNat = 13 from rfl]; omega) (by rw [hszc]; exact hsz) hcp
  simp only [show ((13 : Word)).toNat = 13 from rfl] at k3 k4
  obtain ⟨⟨z2, me⟩, hwr, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hr, hme⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hme
  obtain ⟨w1, w2, w3, w5, w6, w7, w8, w9, w10⟩ := projWr_rel' p hp (d := r5.headD 0)
    (by rw [k1, hszc]; omega) (by rw [k1, hszc]; exact hsz) hwr
  have hTc' : erecTop mc = erecTop m + 13 + wl.toNat + wlb.toNat + wlg.toNat := by
    rw [hTc, hTb, hTa'] <;> omega
  have hTd : erecTop md = erecTop mc := by simp only [erecTop]; rw [k2.2.1 129 (by simp)]
  have hTe : erecTop me = erecTop mc := by
    simp only [erecTop]; rw [w2.2.1 129 (by simp), k2.2.1 129 (by simp)]
  have hsze : (me.arr64 EREC).size = (mc.arr64 EREC).size := by rw [w1, k1]
  have hgrs : SlotGrow mc me (r5.headD 0).toNat ((r5.headD 0).toNat + 13) :=
    ⟨by rw [hTe]; exact Nat.le_refl _, fun i hi hout => by
      rw [w3 i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        k3 i (by omega)], hsze⟩
  have htse : erecTop me ≤ (me.arr64 EREC).size := by rw [hTe, hsze]; exact htsc
  have hgm : SlotGrow m me (r5.headD 0).toNat ((r5.headD 0).toNat + 13) :=
    (SlotGrow.of_grow hgc0 _ _).trans hgrs (Nat.le_refl _) (Nat.le_refl _)
  have hgme : ErecGrow m me := hgm.toGrow (by omega)
  obtain ⟨hDf, hPf⟩ := arenaD_erecFrame hDc hPc (k2.trans w2)
  have W : ∀ i, i < 13 → i ≠ 2 → i ≠ 3 → i ≠ 6 → i ≠ 8 → i ≠ 9 → i ≠ 11 →
      (me.arr64 EREC)[(r5.headD 0).toNat + i]? = (m.arr64 EREC)[q.toNat + i]? := by
    intro i hi h2 h3 h6 h8 h9 h11
    rw [w3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      k4 i hi, keyc _ (by omega)]
  have PE : ∀ {i : Nat} {w : Word}, i < erecTop me → (me.arr64 EREC)[i]? = some w →
      (erecP me)[i]? = some w := fun hi h => preE_of_get hi h
  have hq5 : (m.arr64 EREC)[q.toNat + 5]? = (preE m D)[q.toNat + 5]? := by
    rw [preE_get, ite_eq_left (by omega)]
  have hdn : (r5.headD 0).toNat = erecTop m := hdv
  have WP : ∀ i, i < 13 → i ≠ 2 → i ≠ 3 → i ≠ 6 → i ≠ 8 → i ≠ 9 → i ≠ 11 →
      (erecP me)[(r5.headD 0).toNat + i]? = (preE m D)[q.toNat + i]? := by
    intro i hi h2 h3 h6 h8 h9 h11
    rw [erecP_getElem me _ (by omega) htse, W i hi h2 h3 h6 h8 h9 h11, preE_get,
      ite_eq_left (by omega)]
  have hq4 : (m.arr64 EREC)[q.toNat + 4]? = some wl := by
    obtain ⟨w, hw, hwl'⟩ := nat?_get hwl
    have h1 := erecP_get hw
    rw [hEa] at h1
    exact (UInt64.toNat_inj.mp hwl') ▸ h1
  have hq10 : (m.arr64 EREC)[q.toNat + 10]? = some wlb := by
    obtain ⟨w, hw, hwl'⟩ := nat?_get hwlb
    have h1 := erecP_get hw
    rw [hg0b.2.1 _ (by omega)] at h1
    exact (UInt64.toNat_inj.mp hwl') ▸ h1
  have hq12 : (m.arr64 EREC)[q.toNat + 12]? = some wlg := by
    obtain ⟨w, hw, hwl'⟩ := nat?_get hwlg
    have h1 := erecP_get hw
    rw [hg0b.2.1 _ (by omega)] at h1
    exact (UInt64.toNat_inj.mp hwl') ▸ h1
  have hsn' : (hd? (erecP me) ((r5.headD 0).toNat + 2) : Option NIdx) = some sn' := by
    rw [← hds, erecP_eq_preE]; exact hd?_of_pre (by omega) w5 hpws.1
  have hc' : (hd? (erecP me) ((r5.headD 0).toNat + 6) : Option NIdx) = some c' := by
    rw [← hdc, erecP_eq_preE]; exact hd?_of_pre (by omega) w7 hpwc.1
  have hss'' : (hd? (erecP me) ((r5.headD 0).toNat + 8) : Option LIdx) = some ss' := by
    rw [← hdss, erecP_eq_preE]; exact hd?_of_pre (by omega) w8 hpwss.1
  have hlp' : (hlist? (erecP me) ((r5.headD 0).toNat + 3) : Option (List NIdx)) = some lps' := by
    simp only [L.Arena.hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨(ra.tail.headD 0).toNat, ?_, wl.toNat, ?_, ?_⟩
    · rw [erecP_eq_preE]; exact nat?_of_pre (by omega) w6
    · rw [erecP_eq_preE]
      refine nat?_of_pre (m := me) (T := erecTop me) (w := wl) (by omega) ?_
      rw [show (r5.headD 0).toNat + 3 + 1 = (r5.headD 0).toNat + 4 from rfl,
        W 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hq4
    · have h := hgc.ext.hslice? hslb
      have h2 := hgrs.hslice? htsc htse h (Or.inr (Or.inl (by omega)))
      exact (show (ra.tail.headD 0).toNat = erecTop ma from hptr) ▸ h2
  have hbs' : (hlist? (erecP me) ((r5.headD 0).toNat + 9) : Option (List EIdx)) = some bs' := by
    simp only [L.Arena.hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨(rb.tail.tail.headD 0).toNat, ?_, wlb.toNat, ?_, ?_⟩
    · rw [erecP_eq_preE]; exact nat?_of_pre (by omega) w9
    · rw [erecP_eq_preE]
      refine nat?_of_pre (m := me) (T := erecTop me) (w := wlb) (by omega) ?_
      rw [show (r5.headD 0).toNat + 9 + 1 = (r5.headD 0).toNat + 10 from rfl,
        W 10 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hq10
    · have h2 := hgrs.hslice? htsc htse hslbs (Or.inr (Or.inl (by omega)))
      exact (show (rb.tail.tail.headD 0).toNat = erecTop mb from hptrb) ▸ h2
  have hgs' : (hlist? (erecP me) ((r5.headD 0).toNat + 11) : Option (List LIdx)) = some gs' := by
    simp only [L.Arena.hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨(rb.tail.tail.tail.headD 0).toNat, ?_, wlg.toNat, ?_, ?_⟩
    · rw [erecP_eq_preE]; exact nat?_of_pre (by omega) w10
    · rw [erecP_eq_preE]
      refine nat?_of_pre (m := me) (T := erecTop me) (w := wlg) (by omega) ?_
      rw [show (r5.headD 0).toNat + 11 + 1 = (r5.headD 0).toNat + 12 from rfl,
        W 12 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hq12
    · have h2 := hgrs.hslice? htsc htse hslgs (Or.inr (Or.inl (by omega)))
      exact (show (rb.tail.tail.tail.headD 0).toNat = erecTop mb + wlb.toNat from hptrg) ▸ h2
  refine ⟨b4, qm4, ⟨sn', lps', tbl.numParams, c', tbl.numFields, ss', bs'.toArray, gs'⟩, ?_, hDf, hPf, hcpc.trans hcpb, ?_,
    (TierKeep.of_frame hfa (by simp)).trans (htkb.trans (htkc.trans (TierKeep.of_frame (k2.trans w2) (by simp)))),
    hgme, htse, ?_, ?_, ?_⟩
  · rw [promoteProjTable, run_bind_ok hrun1]
    simp only
    rw [run_bind_ok hrun3]
    simp only
    rw [run_bind_ok hrunc]
    simp only
    rw [run_bind_ok hruns]
    simp only
    rw [run_bind_ok hrunb]
    simp only
    rw [run_bind_ok hrung]; rfl
  · exact ((((hfa.mono (by simp) (by simp)).trans (hfb)).trans hfc)).trans
      ((k2.trans w2).mono (by simp) (by simp))
  · rw [← hr]; exact hdv
  · rw [← hr]; show (r5.headD 0).toNat + 13 ≤ erecTop me; omega
  · rw [← hr]
    exact decTbl_move htbl
      (by have := WP 5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega); exact this)
      (by have := WP 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega); exact this)
      hsn' hlp' hc' hss'' hbs' hgs'

end rel

end L.Arena

end
