module

public import ConAgua.Checker.FrontReset
public import ConAgua.Checker.PrepProgHoist
public import ConAgua.Checker.HoistRefBase
public import ConAgua.Checker.CompareEntry
public import ConAgua.Front.ApplyDeclRefine
public import ConAgua.Arena.FreezeSpec
import all ConAgua.Checker.CompareEntry
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `cmp_stash()` and `cmp_restore()` (lane compare)

The compared run's plumbing between its two parses (`Checker/CompareEntry.lean`):

* `cmp_stash()` copies `DECL`'s count word and records to `CDECL`, cuts `DECL` back to the
  prelude's `CTL[240]` records and empties the id tables (`front_reset`): `stashM`
  (`cmpStash_spec`).
* `cmp_restore()` copies `CDECL`'s count word and records back to `DECL`: `restoreM`
  (`cmpRestore_spec`).

The records' relation `DeclsF` survives a copy of the words it reads (`DeclsF.congr`) and a cut
to a prefix of the records (`DeclsF.prefix`).
-/

namespace L.Checker

open L L.Arena L.Front
open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-! ## The records' relation across copies and cuts -/

/-- **`DeclsF` at other arrays that agree on the words it reads**: `D'` holds the count word and
the records' words of `D`, `P'` the pool's words up to `P`'s top (and a top at least `P`'s). -/
theorem _root_.L.Front.DeclsF.congr {D P D' P' : Array Word} {ds : Array IDeclaration}
    (h : DeclsF D P ds) (hDs : D'.size < 2 ^ 63) (hroom : 1 + 8 * ds.size ≤ D'.size)
    (hPs : P'.size = P.size)
    (hD : ∀ j, j < 1 + 8 * ds.size → D'[j]? = D[j]?)
    (hP : ∀ j, 0 < j → j < 1 + (P[0]?.getD 0).toNat → P'[j]? = P[j]?)
    (htop : (P[0]?.getD 0).toNat ≤ (P'[0]?.getD 0).toNat)
    (htop' : (P'[0]?.getD 0).toNat + 1 ≤ P'.size) : DeclsF D' P' ds := by
  have hc := h.count
  have hr := h.room
  refine ⟨hDs, by rw [hPs]; exact h.psize, by rw [hD 0 (by omega)]; exact hc, hroom, htop',
    fun i hi => ?_, h.npb⟩
  exact DeclAtF_mono D D' P P' i _ (fun j _ hj => hD j (by omega)) hP htop hPs (h.recs i hi)

/-- **`DeclsF` of a prefix of the records**: the count word set to the prefix's length. -/
theorem _root_.L.Front.DeclsF.prefix {D P : Array Word} {ds es : Array IDeclaration}
    (h : DeclsF D P (ds ++ es)) :
    DeclsF (D.set! 0 (UInt64.ofNat ds.size)) P ds := by
  have hc := h.count
  have hr := h.room
  have hs := h.dsize
  simp only [Array.size_append] at hc hr
  have hsz : (D.set! 0 (UInt64.ofNat ds.size)).size = D.size := by simp
  have hw : ∀ j, 0 < j → (D.set! 0 (UInt64.ofNat ds.size))[j]? = D[j]? := fun j hj => by
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; split <;> first | omega | rfl
  refine ⟨by rw [hsz]; exact hs, h.psize, ?_, by rw [hsz]; omega, h.ptop, fun i hi => ?_,
    fun i hi b nP e => h.npb i (by simp; omega) b nP (by rw [Array.getElem_append_left hi]; exact e)⟩
  · have h0 : 0 < D.size := by omega
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, h0, ite_true, Option.getD_some]
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  · have hx := h.recs i (by simp; omega)
    rw [Array.getElem_append_left hi] at hx
    exact DeclAtF_mono D _ P P i _ (fun j hj _ => hw j hj) (fun _ _ _ => rfl) (Nat.le_refl _) rfl hx

/-- `RecOK` at another records' array that agrees on record `r`'s words. -/
theorem recOK_congrW {D D' P : Array Word} {r : Nat} (h : RecOK D P r)
    (hD : ∀ j, 0 < j → j < 1 + 8 * r + 8 → D'[j]? = D[j]?) : RecOK D' P r := by
  have hw : ∀ k, k < 8 → dw D' r k = dw D r k := fun k hk => by
    simp only [dw]; rw [hD _ (by omega) (by omega)]
  simp only [RecOK, hw 0 (by omega), hw 1 (by omega), hw 2 (by omega), hw 3 (by omega),
    hw 4 (by omega), hw 5 (by omega)] at h ⊢
  exact h

/-! ## The copy -/

/-- A copy of the first `n` words of `s` over the first `n` of `d`. -/
theorem get?_copy64 {d s : ArrId} (hds : d ≠ s) (m : Mem) (n : Nat) (hn : n < 2 ^ 63)
    (hd : n ≤ (m.arr64 d).size) (hs : n ≤ (m.arr64 s).size) (j : Nat) (hj : j < n) :
    ((m.copy64 d 0 s 0 n).arr64 d)[j]? = (m.arr64 s)[j]? := by
  have hsz := size_copy64 m d 0 s 0 n d
  have h1 := getD_copy64 hds n m 0 0 (by simp; omega) (by simp; omega) j
  simp only [UInt64.toNat_zero, Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and] at h1
  rw [if_pos ⟨hj, by omega⟩] at h1
  rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega)]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (show j < (m.arr64 s).size by omega),
    Array.getElem?_eq_getElem (show j < ((m.copy64 d 0 s 0 n).arr64 d).size by omega),
    Option.getD_some] at h1
  rw [h1]

/-! ## `cmp_stash()` -/

/-- The number of words `cmp_stash` copies: the count word and the records. -/
def stashN (m : Mem) : Word := 1 + 8 * rdW (m.arr64 DECL) 0

/-- `cmp_stash`'s copy and cut, before `front_reset`. -/
def stashM0 (m : Mem) : Mem :=
  (m.copy64 CDECL 0 DECL 0 (stashN m).toNat).set64 DECL 0 (rdW (m.arr64 CTL) 240)

/-- **The memory after `cmp_stash()`**. -/
def stashM (m : Mem) : Mem := resetM (stashM0 m)

/-- What a returning `cmp_stash` has checked. -/
def StashOK (m : Mem) : Prop :=
  (rdW (m.arr64 DECL) 0).toNat < 2 ^ 59 ∧ (stashN m).toNat ≤ (m.arr64 CDECL).size ∧
    (stashN m).toNat ≤ (m.arr64 DECL).size ∧ ResetOK (stashM0 m)

theorem stash_eqs (m : Mem) (hD0 : 0 < (m.arr64 DECL).size) (h240 : 240 < (m.arr64 CTL).size) :
    stashN m = (1 : Word) + (8 : Word) * (m.arr64 DECL)[0] ∧ ∀ h : 240 < ((m.copy64 CDECL 0 DECL 0
      ((1 : Word) + (8 : Word) * (m.arr64 DECL)[0]).toNat).arr64 CTL).size,
    stashM0 m = (m.copy64 CDECL 0 DECL 0 ((1 : Word) + (8 : Word) * (m.arr64 DECL)[0]).toNat).set64 DECL 0
      (getElem ((m.copy64 CDECL 0 DECL 0 ((1 : Word) + (8 : Word) * (m.arr64 DECL)[0]).toNat).arr64 CTL) 240 h) := by
  have eN : stashN m = (1 : Word) + (8 : Word) * (m.arr64 DECL)[0] := by
    simp only [stashN, rdW_eq _ 0 0 rfl hD0]
  refine ⟨eN, fun h => ?_⟩
  have e240 : (m.copy64 CDECL 0 DECL 0 ((1 : Word) + (8 : Word) * (m.arr64 DECL)[0]).toNat).arr64 CTL =
      m.arr64 CTL := arr64_copy64_ne _ _ _ _ _ _ (by decide)
  simp only [stashM0, eN, rdW_eq _ 240 240 rfl h240]
  congr 1
  simp only [e240]

theorem cmpStash_spec (p : Prog) (hp : p.lookup "cmp_stash" = some cmpStashL) (hpp : PrepProg p)
    (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cmp_stash" []
    ⦃fun _ s' => LocEq s' s₀ ∧ StashOK s₀.mem ∧ s'.mem = stashM s₀.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, cmpStashL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, warr,
      (frontReset_spec p hpp n ·)]
    all_goals (try simp only [Sig.retVal, Sig.retOr, L.St.setLoc_mem, List.headD_cons,
      St.setLocs_cons, St.setLocs_nil, St.setLoc_loc, Cmp.eval, BinOp.eval] at *)
    case vc1 => grind [lang_grind]
    all_goals rename_i _ hD0 hlt _ h240 _ _ _ hb _ hpost
    all_goals simp only [ite_true] at hb hpost
    all_goals obtain ⟨-, hok, hm⟩ := hpost
    all_goals obtain ⟨eN, eM⟩ := stash_eqs s₀.mem (by simpa using hD0) (by simpa [L.St.setLoc_mem] using h240)
    case vc2 =>
      have hD0' : 0 < (s₀.mem.arr64 DECL).size := by simpa using hD0
      have hb1 := hb.1
      have hb2 := hb.2
      simp only [UInt64.toNat_zero, Nat.zero_add] at hb1 hb2
      refine ⟨by rw [rdW_eq _ 0 0 rfl hD0']; simp at hlt; exact UInt64.lt_iff_toNat_lt.mp hlt,
        by rw [eN]; exact hb1, by rw [eN]; exact hb2, by rw [eM (by simpa [L.St.setLoc_mem] using h240)]; exact hok⟩
    case vc3 => rw [hm, stashM, eM (by simpa [L.St.setLoc_mem] using h240)]; rfl

/-! ## `cmp_restore()` -/

/-- The number of words `cmp_restore` copies back. -/
def restoreN (m : Mem) : Word := 1 + 8 * rdW (m.arr64 CDECL) 0

/-- **The memory after `cmp_restore()`**. -/
def restoreM (m : Mem) : Mem := m.copy64 DECL 0 CDECL 0 (restoreN m).toNat

/-- What a returning `cmp_restore` has checked. -/
def RestoreOK (m : Mem) : Prop :=
  (rdW (m.arr64 CDECL) 0).toNat < 2 ^ 59 ∧ (restoreN m).toNat ≤ (m.arr64 DECL).size ∧
    (restoreN m).toNat ≤ (m.arr64 CDECL).size

theorem restoreN_eq (m : Mem) (hD0 : 0 < (m.arr64 CDECL).size) :
    restoreN m = (1 : Word) + (8 : Word) * (m.arr64 CDECL)[0] := by
  simp only [restoreN, rdW_eq _ 0 0 rfl hD0]

theorem cmpRestore_spec (p : Prog) (hp : p.lookup "cmp_restore" = some cmpRestoreL) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cmp_restore" []
    ⦃fun _ s' => LocEq s' s₀ ∧ RestoreOK s₀.mem ∧ s'.mem = restoreM s₀.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, cmpRestoreL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, warr]
    all_goals (try simp only [L.St.setLoc_mem, St.setLoc_loc, Cmp.eval, BinOp.eval] at *)
    case vc1 => grind [lang_grind]
    all_goals rename_i hD0 hlt _ _ _ hb
    all_goals simp only [ite_true, UInt64.toNat_zero, Nat.zero_add] at hb
    all_goals have hD0' : 0 < (s₀.mem.arr64 CDECL).size := by simpa using hD0
    all_goals have eN := restoreN_eq s₀.mem hD0'
    case vc2 =>
      refine ⟨by rw [rdW_eq _ 0 0 rfl hD0']; simp at hlt; exact UInt64.lt_iff_toNat_lt.mp hlt,
        by rw [eN]; exact hb.1, by rw [eN]; exact hb.2⟩
    case vc3 => rw [restoreM, eN]; rfl

end L.Checker
