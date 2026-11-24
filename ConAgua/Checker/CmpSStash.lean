module

public import ConAgua.Checker.CompareStash
import all ConAgua.Checker.CompareEntry
import all ConAgua.Arena.FreezeCmp
import all ConAgua.Checker.CmpSeqEntry
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The solution's stash (lane compare, design (i))

`cmp_sstash()` (`Checker/CompareEntry.lean`), the first step of modes `6` and `7`, keeps what the
solution's jobs read and the challenge's preparation overwrites: `sstashM m`, the solution's
records `DECL[0‥1+8·DECL[0])` in `SDECL`, its index firsts `FIRSTS[0‥DECL[0])` in `SFIRSTS`, its
declaration pool `DLP[0‥1+DLP[0])` in `SDLP`, `CTL[0‥256)` in `SCTL`.
-/

namespace L.Checker

open L L.Arena L.Front
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-- The words of `SDECL`, `SFIRSTS`, `SDLP` the stash copies. -/
def sstN1 (m : Mem) : Word := 1 + 8 * rdW (m.arr64 DECL) 0
def sstN2 (m : Mem) : Word := rdW (m.arr64 DECL) 0
def sstN3 (m : Mem) : Word := 1 + rdW (m.arr64 DLP) 0

/-- **The memory after `cmp_sstash()`**. -/
def sstashM (m : Mem) : Mem :=
  (((m.copy64 SDECL 0 DECL 0 (sstN1 m).toNat).copy64 SFIRSTS 0 FIRSTS 0 (sstN2 m).toNat).copy64
    SDLP 0 DLP 0 (sstN3 m).toNat).copy64 SCTL 0 CTL 0 256

/-- What a returning `cmp_sstash` has checked: the counts and every copy in bounds. -/
def SStashOK (m : Mem) : Prop :=
  (rdW (m.arr64 DECL) 0).toNat < 2 ^ 59 ∧
    (sstN1 m).toNat ≤ (m.arr64 SDECL).size ∧ (sstN1 m).toNat ≤ (m.arr64 DECL).size ∧
    (sstN2 m).toNat ≤ (m.arr64 SFIRSTS).size ∧ (sstN2 m).toNat ≤ (m.arr64 FIRSTS).size ∧
    (sstN3 m).toNat ≤ (m.arr64 SDLP).size ∧ (sstN3 m).toNat ≤ (m.arr64 DLP).size ∧
    256 ≤ (m.arr64 SCTL).size ∧ 256 ≤ (m.arr64 CTL).size

theorem cmpSStash_spec (p : Prog) (hp : p.lookup "cmp_sstash" = some cmpSStashL) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cmp_sstash" []
    ⦃fun _ s' => LocEq s' s₀ ∧ SStashOK s₀.mem ∧ s'.mem = sstashM s₀.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, cmpSStashL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, warr]
    all_goals simp only [L.St.setLoc_mem, St.setLoc_loc, Cmp.eval, BinOp.eval, UInt64.toNat_zero,
      Locals.init, ite_true, ite_false, Nat.reduceEqDiff, Nat.zero_add, size_copy64] at *
    case vc1 => grind [lang_grind]
    all_goals rename_i hD0 _ _ hL0 hlt h1 h2 h3 h4
    all_goals have hD0' : 0 < (s₀.mem.arr64 DECL).size := by simpa using hD0
    all_goals have hL0' : 0 < (s₀.mem.arr64 DLP).size := by simpa [L.St.setLoc_mem] using hL0
    all_goals have e1 : sstN1 s₀.mem = (1 : Word) + (8 : Word) * (s₀.mem.arr64 DECL)[0] := by
                simp only [sstN1, rdW_eq _ 0 0 rfl hD0']
    all_goals have e2 : sstN2 s₀.mem = (s₀.mem.arr64 DECL)[0] := by simp only [sstN2, rdW_eq _ 0 0 rfl hD0']
    all_goals have e3 : sstN3 s₀.mem = (1 : Word) + (s₀.mem.arr64 DLP)[0] := by
                simp only [sstN3, rdW_eq _ 0 0 rfl hL0']
    case vc2 =>
      refine ⟨by rw [rdW_eq _ 0 0 rfl hD0']; simp at hlt; exact UInt64.lt_iff_toNat_lt.mp hlt,
        by rw [e1]; exact h1.1, by rw [e1]; exact h1.2, by rw [e2]; exact h2.1, by rw [e2]; exact h2.2,
        by rw [e3]; exact h3.1, by rw [e3]; exact h3.2, by simpa using h4.1, by simpa using h4.2⟩
    case vc3 => rw [sstashM, e1, e2, e3]; rfl

end L.Checker
