import ConAgua.Compiler.Main
import ConAgua.Scan.Link
import ConAgua.Scan.ValidatorLink
import ConAgua.Arena.LitRefine
import ConAgua.Arena.WalkRefine

/-!
# The capstone: the first end-to-end theorems

Composes the whole proof chain (`PLAN.md`) for two functions: `skipBraced_x64` (x64 ⊑ con-leche's
scanner, through L and the `Nat`/`Array UInt8` model) and `natAddLit_x64` (x64 ⊑ the arena's
`Nat.add`, through L and the limb pool). See `DESIGN.md`, "The capstone", for the statements, the
trusted assumptions and the mismatches the composition found.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L

/-! ## A generic error-postcondition for `M`

`⦃P⦄ prog ⦃Q; ⊤⦄`-style specs (every existing spec in `ConAgua.L`/`ConAgua.Arena`) say nothing
about *which* error a failing run raises. Composing with `compile_correct` needs to know the
failing runs reachable from the given preconditions are exactly `outOfFuel` (so that the
machine's only non-`rdx = 0` outcome is `rdx = 1`, "exhausted"), so this file adds that fact
where it can be gotten cheaply (`skip_braced`/`str_close`: the same `vcgen`/`finish` scripts as
the existing specs close the `oob` branches too, because the loop invariants that already
discharge the bound for the success continuation discharge it for the error continuation just as
well). -/

/-- A spec of a named block at fuel `n + 1` is a spec of its first step at fuel `n`, for any
error postcondition (`Logic.lean`'s `Triple.step_exec` is this specialised to `⊤`). -/
theorem Triple.step_exec' {p : Prog} {n : Nat} {s : Stmt} {P : St → Prop} {Q : Sig → St → Prop}
    {E : Err → Prop} (h : ⦃P⦄ exec p (n + 1) s ⦃Q; E⦄) : ⦃P⦄ step p (exec p n) s ⦃Q; E⦄ := h

/-- From a triple to what a failing run raises (the error-side analogue of `M.of_run`). -/
theorem M.of_run_err {α : Type} {prog : M α} {s : St} {e : Err} {P : St → Prop}
    {Q : α → St → Prop} {E : Err → Prop} (hp : P s) (h : prog.run s = .error e)
    (hwp : ⦃fun s => P s⦄ prog ⦃fun r s'' => Q r s''; E⦄) : E e := by
  have hs := hwp.le_wp s hp
  rw [Std.WP.StateT.wp_apply_eq, h] at hs
  exact hs

end L

namespace L.Examples

open L

/-! ## `skip_braced`/`str_close` never abort

`str_close`/`skip_braced` only ever read `IN`, bounds-checked by the same loop invariants
(`hi`/`hj`) that the existing `…_spec` theorems already use to prove the success continuation;
this file reruns those exact `vcgen`/`finish` scripts with the error postcondition tightened from
`⊤` to `(· = .outOfFuel)`, which the same context closes (an `oob` branch would need
`¬ i.toNat < b.size` together with the invariant `i.toNat < b.size` from the guarding `if`/`while`
condition, i.e. `False`, which discharges *any* goal, not just `⊤`). -/

section scan
variable (p : Prog) (hp1 : p.lookup "str_close" = some strClose)
    (hp2 : p.lookup "skip_braced" = some skipBraced)
    (b : Array UInt8) (hb : b.size < 2 ^ 64)
include hb

theorem strCloseLoop_noErr (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hj : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    exec p n strCloseLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [UInt64.ofNat (strCloseN b (s₀.loc 0).toNat)]; fun e => e = .outOfFuel⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := strCloseLoop) rfl]
    sym only [lang_grind] => vcgen [step, evalE, evalC, evalArgs, setLoc, ld8, ih] <;> finish

theorem strCloseLoop_step_noErr (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hj : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) strCloseLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [UInt64.ofNat (strCloseN b (s₀.loc 0).toNat)]; fun e => e = .outOfFuel⦄ :=
  Triple.step_exec' (strCloseLoop_noErr p b hb (n + 1) s₀ hm hj)

include hp1 in
theorem strClose_noErr (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (j : Word)
    (hj : j.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "str_close" [j]
    ⦃fun r s' => s' = s₀ ∧ r = [UInt64.ofNat (strCloseN b j.toNat)]; fun e => e = .outOfFuel⦄ := by
  rw [invoke_eq _ hp1]
  simp only [callFn, strClose]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalArgs, strCloseLoop_step_noErr p b hb n] <;> finish

include hp1 in
theorem skipBracedLoop_noErr (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat ≤ b.size) (hd : (s₀.loc 1).toNat + (b.size - (s₀.loc 0).toNat) < 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    exec p n skipBracedLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [UInt64.ofNat (skipBracedN b (s₀.loc 0).toNat (s₀.loc 1).toNat)];
      fun e => e = .outOfFuel⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := skipBracedLoop) rfl]
    sym only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih, strClose_noErr p hp1 b hb n] <;>
      finish

include hp1 in
theorem skipBracedLoop_step_noErr (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat ≤ b.size) (hd : (s₀.loc 1).toNat + (b.size - (s₀.loc 0).toNat) < 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) skipBracedLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [UInt64.ofNat (skipBracedN b (s₀.loc 0).toNat (s₀.loc 1).toNat)];
      fun e => e = .outOfFuel⦄ :=
  Triple.step_exec' (skipBracedLoop_noErr p hp1 b hb (n + 1) s₀ hm hi hd)

include hp1 hp2 in
/-- `skip_braced` only ever raises `outOfFuel`: under the bounds `str_close`/`skip_braced`'s own
specs already need, every `IN.u8[_]` read the compiled loop makes is in range, so the only way
`run` fails is running out of fuel. -/
theorem skipBraced_noErr (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i d : Word)
    (hi : i.toNat ≤ b.size) (hd : d.toNat + (b.size - i.toNat) < 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "skip_braced" [i, d]
    ⦃fun r s' => s' = s₀ ∧ r = [UInt64.ofNat (skipBracedN b i.toNat d.toNat)];
      fun e => e = .outOfFuel⦄ := by
  rw [invoke_eq _ hp2]
  simp only [callFn, skipBraced]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalArgs, skipBracedLoop_step_noErr p hp1 b hb n] <;> finish

end scan

/-- `run scanProg fuel "skip_braced" [i, d] {bytes := #[b]}` never raises anything but
`outOfFuel`: either it returns con-leche's `skipBracedN`, unchanged memory, or the fuel ran out.
This is the fact `skipBraced_run` (partial correctness alone) does not give: it is silent about
which error a failing run raises. -/
theorem skipBraced_total (b : Array UInt8) (hb : b.size < 2 ^ 64) (fuel : Nat) (i d : Word)
    (hi : i.toNat ≤ b.size) (hd : d.toNat + (b.size - i.toNat) < 2 ^ 64) :
    run scanProg fuel "skip_braced" [i, d] { bytes := #[b] } =
        .ok ([UInt64.ofNat (skipBracedN b i.toNat d.toNat)], { bytes := #[b] }) ∨
      run scanProg fuel "skip_braced" [i, d] { bytes := #[b] } = .error .outOfFuel := by
  simp only [run]
  cases hr : (invoke scanProg (exec scanProg fuel) "skip_braced" [i, d]).run
      { mem := { bytes := #[b] }, loc := Locals.init [] } with
  | error e =>
    have he := M.of_run_err (P := fun s => s = { mem := { bytes := #[b] }, loc := Locals.init [] })
      rfl hr (skipBraced_noErr scanProg rfl rfl b hb fuel _ rfl i d hi hd)
    subst he
    simp [Except.map]
  | ok rs =>
    obtain ⟨r, m'⟩ := rs
    have := M.of_run (P := fun s => s = { mem := { bytes := #[b] }, loc := Locals.init [] }) rfl hr
      (skipBraced_spec scanProg rfl rfl b hb fuel _ rfl i d hi hd)
    obtain ⟨rfl, rfl⟩ := this
    simp [Except.map]

end L.Examples

namespace L.Compiler

open L L.Examples ConAgua.Scan

/-- **The first end-to-end theorem.** For a Kraken host holding the compiled `scanProg`, run
from `ca_enter` on a state whose input region holds con-leche's byte buffer `b` at position `i`
with recursion-depth counter `depth`, with `N` units of fuel: the run returns to the caller with
the callee-saved registers restored, and either reports exhausted (`rdx = 1`, fuel or stack) or
reports `rdx = 0` with `rax` the x64 encoding of con-leche's own `skipBraced b i depth`
(`ConLeche.Frontend.Scan.Fast`), the real `USize`-over-`ByteArray` function, not the `Nat`-position
model `skipBracedN` that the L-level specs are stated against. No `L` notion appears in the
conclusion; `MemRel`, the layout relation, is unavoidable (it is how "the input region holds `b`"
is stated for an x64 state). -/
theorem skipBraced_x64 [Host] (G : Layout) (hG : G.Ok) (hwf : Prog.wf G.tab scanProg = true)
    (hnres : 1 ≤ G.tab.nres) (k0 : Nat) (hcode : Code (compileProg G.tab scanProg "skip_braced") k0)
    (b : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 64)
    (i : USize) (depth : Nat) (hi : i.toNat ≤ b.size)
    (hd : depth + (b.size - i.toNat) < 2 ^ 64) (hnargs : G.nargs = 2)
    (N : Nat) (dm : MachineData) (ra : Word)
    (hT : dm.regs.rdi.toNat = G.T) (hN : dm.regs.rsi.toNat = N)
    (hmem : MemRel G { bytes := #[b.data] } dm.dmem) (hroom : G.lo + 8 ≤ G.hi)
    (htop : rdW dm.dmem (A G.T) = some (UInt64.ofNat G.hi))
    (hargv : ∀ j (h : j < 2), rdW dm.dmem (A (G.T + G.tab.args.toNat + 8 * j)) =
      some ([i.toUInt64, UInt64.ofNat depth] : List Word)[j])
    (hra : rdW dm.dmem (A dm.regs.rsp.toNat) = some ra)
    (hcs : ∀ x, dm.regs.rsp.toNat - 24 ≤ x → x < dm.regs.rsp.toNat + 8 →
      (dm.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧ ¬ G.InArr x ∧ ¬ G.InTab x)
    (hcs24 : 24 ≤ dm.regs.rsp.toNat) (hcs8 : dm.regs.rsp.toNat + 8 < 2 ^ 64) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = dm.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = dm.regs.rbp ∧ st.data.regs.r14 = dm.regs.r14 ∧ st.data.regs.r15 = dm.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨
          (st.data.regs.rdx = 0 ∧
            st.data.regs.rax = (ConLeche.Frontend.skipBraced b i depth).toUInt64 ∧
            MemRel G { bytes := #[b.data] } st.data.dmem)))
      dm (label enterL) := by
  have hargs : ([i.toUInt64, UInt64.ofNat depth] : List Word).length = skipBraced.nparams := rfl
  have hentry : scanProg.lookup "skip_braced" = some skipBraced := rfl
  refine eventually_weaken _ _ _ _ ?_
    (compile_correct scanProg "skip_braced" G hG hwf k0 hcode skipBraced hentry
      [i.toUInt64, UInt64.ofNat depth] hargs hnargs { bytes := #[b.data] } N dm ra
      hT hN hmem hroom htop hargv hra hcs hcs24 hcs8)
  intro st hst
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  rcases h6 with h6 | h6
  · exact Or.inl h6
  · right
    have hdepth : depth < 2 ^ 64 := by omega
    have hiN : i.toUInt64.toNat ≤ b.data.size := by simpa using hi
    have hdN : (UInt64.ofNat depth).toNat + (b.data.size - i.toUInt64.toNat) < 2 ^ 64 := by
      rw [UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using hdepth)]
      simpa using hd
    rcases skipBraced_total b.data hb N i.toUInt64 (UInt64.ofNat depth) hiN hdN with hok | herr
    · rw [hok] at h6
      obtain ⟨hrdx, hres, hm'⟩ := h6
      have hrax : st.data.regs.rax = UInt64.ofNat (skipBracedN b.data i.toUInt64.toNat (UInt64.ofNat depth).toNat) :=
        hres 0 (by omega)
      refine ⟨hrdx, ?_, hm'⟩
      rw [hrax, UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using hdepth)]
      simp only [USize.toNat_toUInt64]
      rw [← skipBraced_toNat_eq b h64 hb i depth]
      simp
    · rw [herr] at h6
      exact absurd h6 (by simp [OutcomeRel])

/-- Shared step of `validate_x64`/`validate_x64_parseBytes`: from a Kraken host holding the
compiled `valProg`, run from `ca_enter` on a state whose input region holds `b` with `N` units of
fuel, the run returns to the caller with the callee-saved registers restored, and either reports
exhausted (`rdx = 1`), reports an `L` error other than fuel (`rdx = 2`: Stage B has no `_noErr`
theorem for `validate` the way `skip_braced`/`str_close` have one above, so unlike `skipBraced_x64`
this is a real, open third outcome, not yet ruled out — see `DESIGN.md`), or reports `rdx = 0`
together with the raw `L` run `validate` made, for the two theorems below to read off. -/
theorem validate_x64_core [Host] (G : Layout) (hG : G.Ok)
    (hwf : Prog.wf G.tab L.Scan.Validator.valProg = true) (hnres : 1 ≤ G.tab.nres)
    (k0 : Nat) (hcode : Code (compileProg G.tab L.Scan.Validator.valProg "validate") k0)
    (b : ByteArray) (hnargs : G.nargs = 0)
    (N : Nat) (dm : MachineData) (ra : Word)
    (hT : dm.regs.rdi.toNat = G.T) (hN : dm.regs.rsi.toNat = N)
    (hmem : MemRel G { bytes := #[b.data] } dm.dmem) (hroom : G.lo + 8 ≤ G.hi)
    (htop : rdW dm.dmem (A G.T) = some (UInt64.ofNat G.hi))
    (hargv : ∀ j (h : j < 0), rdW dm.dmem (A (G.T + G.tab.args.toNat + 8 * j)) =
      some ([] : List Word)[j])
    (hra : rdW dm.dmem (A dm.regs.rsp.toNat) = some ra)
    (hcs : ∀ x, dm.regs.rsp.toNat - 24 ≤ x → x < dm.regs.rsp.toNat + 8 →
      (dm.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧ ¬ G.InArr x ∧ ¬ G.InTab x)
    (hcs24 : 24 ≤ dm.regs.rsp.toNat) (hcs8 : dm.regs.rsp.toNat + 8 < 2 ^ 64) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = dm.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = dm.regs.rbp ∧ st.data.regs.r14 = dm.regs.r14 ∧ st.data.regs.r15 = dm.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨ st.data.regs.rdx = 2 ∨
          (st.data.regs.rdx = 0 ∧ ∃ r m', run L.Scan.Validator.valProg N "validate" []
            { bytes := #[b.data] } = .ok (r, m') ∧ st.data.regs.rax = r.headD 0 ∧
            MemRel G m' st.data.dmem)))
      dm (label enterL) := by
  have hargs : ([] : List Word).length = L.Scan.Line.validate.nparams := rfl
  have hentry : L.Scan.Validator.valProg.lookup "validate" = some L.Scan.Line.validate := rfl
  refine eventually_weaken _ _ _ _ ?_
    (compile_correct L.Scan.Validator.valProg "validate" G hG hwf k0 hcode L.Scan.Line.validate
      hentry [] hargs hnargs { bytes := #[b.data] } N dm ra hT hN hmem hroom htop hargv hra hcs hcs24 hcs8)
  intro st hst
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  rcases h6 with h6 | h6
  · exact Or.inl h6
  · rcases hrun : run L.Scan.Validator.valProg N "validate" [] { bytes := #[b.data] } with e | ⟨r, m'⟩
    · rw [hrun] at h6
      rcases e with _ | _ | _ | _ <;> simp_all [OutcomeRel]
    · rw [hrun] at h6
      obtain ⟨hrdx, hres, hm'⟩ := h6
      have hrax : st.data.regs.rax = r.headD 0 := by
        have := hres 0 (by omega); simp only [rres] at this; rwa [show r.getD 0 0 = r.headD 0 by
          cases r <;> rfl] at this
      refine Or.inr (Or.inr ⟨hrdx, r, m', ?_, ?_, ?_⟩)
      · rfl
      · exact hrax
      · exact hm'

/-- **The fourth end-to-end theorem: Stage B's validator.** From a Kraken host holding the
compiled `valProg`, run from `ca_enter` on a state whose input region holds a buffer `b` with `N`
units of fuel: the run returns to the caller with the callee-saved registers restored, and either
reports exhausted (`rdx = 1`), reports an `L` error other than fuel (`rdx = 2`, not yet ruled
out, see `validate_x64_core`), or reports `rdx = 0` with `rax` the line number `scanLineFwd`'s own
driver (`ConAgua.Scan.LineLink.scanDriver`, built directly from con-leche's
`ConLeche.Frontend.scanLineFwd` over `b`'s real `ByteArray`/`USize` positions, with no `Nat`-model
layer in between) reports: `0` if every line of `b` scans, else the number of the first line that
does not; the input region is unchanged. -/
theorem validate_x64 [Host] (G : Layout) (hG : G.Ok) (hwf : Prog.wf G.tab L.Scan.Validator.valProg = true)
    (hnres : 1 ≤ G.tab.nres) (k0 : Nat) (hcode : Code (compileProg G.tab L.Scan.Validator.valProg "validate") k0)
    (b : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63) (hnargs : G.nargs = 0)
    (N : Nat) (dm : MachineData) (ra : Word)
    (hT : dm.regs.rdi.toNat = G.T) (hN : dm.regs.rsi.toNat = N)
    (hmem : MemRel G { bytes := #[b.data] } dm.dmem) (hroom : G.lo + 8 ≤ G.hi)
    (htop : rdW dm.dmem (A G.T) = some (UInt64.ofNat G.hi))
    (hargv : ∀ j (h : j < 0), rdW dm.dmem (A (G.T + G.tab.args.toNat + 8 * j)) =
      some ([] : List Word)[j])
    (hra : rdW dm.dmem (A dm.regs.rsp.toNat) = some ra)
    (hcs : ∀ x, dm.regs.rsp.toNat - 24 ≤ x → x < dm.regs.rsp.toNat + 8 →
      (dm.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧ ¬ G.InArr x ∧ ¬ G.InTab x)
    (hcs24 : 24 ≤ dm.regs.rsp.toNat) (hcs8 : dm.regs.rsp.toNat + 8 < 2 ^ 64) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = dm.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = dm.regs.rbp ∧ st.data.regs.r14 = dm.regs.r14 ∧ st.data.regs.r15 = dm.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨ st.data.regs.rdx = 2 ∨
          (st.data.regs.rdx = 0 ∧
            st.data.regs.rax = UInt64.ofNat (ConAgua.Scan.LineLink.scanDriver b 0 0) ∧
            MemRel G { bytes := #[b.data] } st.data.dmem)))
      dm (label enterL) := by
  refine eventually_weaken _ _ _ _ ?_
    (validate_x64_core G hG hwf hnres k0 hcode b hnargs N dm ra hT hN hmem hroom htop hargv hra hcs hcs24 hcs8)
  intro st hst
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  rcases h6 with h6 | h6 | ⟨hrdx, r, m', hrun, hrax, hm'⟩
  · exact Or.inl h6
  · exact Or.inr (Or.inl h6)
  · obtain ⟨hr, hm2⟩ := L.Scan.Validator.validate_run b.data hb N r m' hrun
    refine Or.inr (Or.inr ⟨hrdx, ?_, ?_⟩)
    · rw [hrax, hr]; exact ConAgua.Scan.DriverLink.validN_zero b h64 hb
    · rwa [hm2] at hm'

/-- **Corollary, pushed down to con-leche's own parser.** `ConLeche.Frontend.parseBytes`
(`vendor/con-leche/ConLeche/Frontend/ExportC.lean`) is the highest-level notion in this project's
proof chain (`PLAN.md`): it scans every line *and* builds the records `scanLineFwd` leaves out.
If it parses `b`, a normally-returning run of the compiled validator necessarily finds `rax = 0`
(`ConAgua.Scan.ValidatorLink.validate_accepts`); if instead it finds `rax ≠ 0`, con-leche's parser
fails, at that line or before (`validate_rejects`) — unconditionally, since a line `scanLineFwd`
rejects can only make `parseBytes` fail too, at it or earlier. -/
theorem validate_x64_parseBytes [Host] (G : Layout) (hG : G.Ok)
    (hwf : Prog.wf G.tab L.Scan.Validator.valProg = true) (hnres : 1 ≤ G.tab.nres)
    (k0 : Nat) (hcode : Code (compileProg G.tab L.Scan.Validator.valProg "validate") k0)
    (b : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63) (hnargs : G.nargs = 0)
    (N : Nat) (dm : MachineData) (ra : Word)
    (hT : dm.regs.rdi.toNat = G.T) (hN : dm.regs.rsi.toNat = N)
    (hmem : MemRel G { bytes := #[b.data] } dm.dmem) (hroom : G.lo + 8 ≤ G.hi)
    (htop : rdW dm.dmem (A G.T) = some (UInt64.ofNat G.hi))
    (hargv : ∀ j (h : j < 0), rdW dm.dmem (A (G.T + G.tab.args.toNat + 8 * j)) =
      some ([] : List Word)[j])
    (hra : rdW dm.dmem (A dm.regs.rsp.toNat) = some ra)
    (hcs : ∀ x, dm.regs.rsp.toNat - 24 ≤ x → x < dm.regs.rsp.toNat + 8 →
      (dm.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧ ¬ G.InArr x ∧ ¬ G.InTab x)
    (hcs24 : 24 ≤ dm.regs.rsp.toNat) (hcs8 : dm.regs.rsp.toNat + 8 < 2 ^ 64) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = dm.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = dm.regs.rbp ∧ st.data.regs.r14 = dm.regs.r14 ∧ st.data.regs.r15 = dm.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨ st.data.regs.rdx = 2 ∨
          (st.data.regs.rdx = 0 ∧
            (∀ res, ConLeche.Frontend.parseBytes b = .ok res → st.data.regs.rax = 0) ∧
            (st.data.regs.rax ≠ 0 → ∃ c k, ConLeche.Frontend.parseBytes b = .error (c, k) ∧
              k ≤ st.data.regs.rax.toNat) ∧
            MemRel G { bytes := #[b.data] } st.data.dmem)))
      dm (label enterL) := by
  refine eventually_weaken _ _ _ _ ?_
    (validate_x64_core G hG hwf hnres k0 hcode b hnargs N dm ra hT hN hmem hroom htop hargv hra hcs hcs24 hcs8)
  intro st hst
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  rcases h6 with h6 | h6 | ⟨hrdx, r, m', hrun, hrax, hm'⟩
  · exact Or.inl h6
  · exact Or.inr (Or.inl h6)
  · obtain ⟨hr, hm2⟩ := L.Scan.Validator.validate_run b.data hb N r m' hrun
    have hraxv : st.data.regs.rax = L.Scan.Line.validN b.data 0 0 := by rw [hrax, hr]; rfl
    have hrsingle : r = [st.data.regs.rax] := by rw [hr, hraxv]
    have hrun' : run L.Scan.Validator.valProg N "validate" [] { bytes := #[b.data] } =
        .ok ([st.data.regs.rax], m') := by rw [← hrsingle]; exact hrun
    refine Or.inr (Or.inr ⟨hrdx, ?_, ?_, ?_⟩)
    · exact fun res hp => by
        have hr0 := ConAgua.Scan.ValidatorLink.validate_accepts b h64 hb N r m' hrun res hp
        have heq : ([L.Scan.Line.validN b.data 0 0] : List Word) = [0] := by rw [← hr]; exact hr0
        injection heq with hval
        rw [hraxv, hval]
    · exact fun hne => ConAgua.Scan.ValidatorLink.validate_rejects b h64 hb N st.data.regs.rax m' hrun' hne
    · rwa [hm2] at hm'

end L.Compiler

namespace L.Arena

open L ConRon.Arena
open L.Compiler hiding rdW

/-- **The second end-to-end theorem.** For a Kraken host holding the compiled `storeProg`, run
from `ca_enter` on a state related (via the layout `G` and `LitR`) to an arena state `a₀`: the run
returns to the caller with the callee-saved registers restored, and either reports exhausted
(`rdx = 1`, fuel or stack), reports that the limb pool or the `lit` store had no room for the
result (`rdx = 2`: `nat_add`'s or `intern_lit`'s own `abort`, a genuine, distinct outcome of this
arena, not fuel exhaustion — see `DESIGN.md`, "mismatches"), or reports `rdx = 0` with the result
register the handle the arena's `Nat.add` arm of `natOpResult` (`natAddArm`, `Refine.lean`)
returns when run on `a₀`, and the final memory related to that arm's final arena state. No `L`
notion but the layout relation (`MemRel`) and the arena relation (`LitR`) appears in the
conclusion. -/
theorem natAddLit_x64 [Host] (G : L.Compiler.Layout) (hG : G.Ok)
    (hwf : Prog.wf G.tab storeProg = true)
    (hnres : 1 ≤ G.tab.nres) (k0 : Nat) (hcode : Code (compileProg G.tab storeProg "nat_add_lit") k0)
    (m : Mem) (a₀ : AState) (hR : LitR m a₀)
    (oa la ob lb : Word) (ha : SliceOK m oa la) (hb : SliceOK m ob lb) (hnargs : G.nargs = 4)
    (N : Nat) (dm : MachineData) (ra : Word)
    (hT : dm.regs.rdi.toNat = G.T) (hN : dm.regs.rsi.toNat = N)
    (hmem : MemRel G m dm.dmem) (hroom : G.lo + 8 ≤ G.hi)
    (htop : L.Compiler.rdW dm.dmem (A G.T) = some (UInt64.ofNat G.hi))
    (hargv : ∀ j (h : j < 4), L.Compiler.rdW dm.dmem (A (G.T + G.tab.args.toNat + 8 * j)) =
      some ([oa, la, ob, lb] : List Word)[j])
    (hra : L.Compiler.rdW dm.dmem (A dm.regs.rsp.toNat) = some ra)
    (hcs : ∀ x, dm.regs.rsp.toNat - 24 ≤ x → x < dm.regs.rsp.toNat + 8 →
      (dm.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧ ¬ G.InArr x ∧ ¬ G.InTab x)
    (hcs24 : 24 ≤ dm.regs.rsp.toNat) (hcs8 : dm.regs.rsp.toNat + 8 < 2 ^ 64) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = dm.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = dm.regs.rbp ∧ st.data.regs.r14 = dm.regs.r14 ∧ st.data.regs.r15 = dm.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨ st.data.regs.rdx = 2 ∨
          (st.data.regs.rdx = 0 ∧ ∃ m' a',
            (natAddArm (pv (m.arr64 POOL) oa.toNat la.toNat) (pv (m.arr64 POOL) ob.toNat lb.toNat)).run a₀
              = .ok (some (decE st.data.regs.rax), a') ∧
            MemRel G m' st.data.dmem ∧ LitR m' a')))
      dm (label enterL) := by
  have hargs : ([oa, la, ob, lb] : List Word).length = natAddLit.nparams := rfl
  have hentry : storeProg.lookup "nat_add_lit" = some natAddLit := rfl
  refine eventually_weaken _ _ _ _ ?_
    (compile_correct storeProg "nat_add_lit" G hG hwf k0 hcode natAddLit hentry
      [oa, la, ob, lb] hargs hnargs m N dm ra hT hN hmem hroom htop hargv hra hcs hcs24 hcs8)
  intro st hst
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  rcases h6 with h6 | h6
  · exact Or.inl h6
  · rcases hrun : run storeProg N "nat_add_lit" [oa, la, ob, lb] m with e | ⟨r, m'⟩
    · rw [hrun] at h6
      rcases e with _ | _ | _ | _ <;> simp_all [OutcomeRel]
    · rw [hrun] at h6
      obtain ⟨hrdx, hres, hm'⟩ := h6
      have hrax : st.data.regs.rax = r.headD 0 := by
        have := hres 0 (by omega); simp only [rres] at this; rwa [show r.getD 0 0 = r.headD 0 by
          cases r <;> rfl] at this
      obtain ⟨a', ha', hLitR⟩ := natAddLit_run_store N m a₀ hR oa la ob lb ha hb r m' hrun
      refine Or.inr (Or.inr ⟨hrdx, m', a', ?_, hm', hLitR⟩)
      rw [hrax]; exact ha'

/-- **The third end-to-end theorem: the first recursive walk.** For a Kraken host holding the
compiled `walkProg`, run from `ca_enter` with handle `h` on a state related (via the layout `G`
and the whole arena relation `ArenaR`) to an arena state `a₀`, with machine fuel `N` at most the
arena fuel `F`: the run returns to the caller, and reports exhausted (`rdx = 1`: fuel, or the
stack, which the walk uses one frame pair per level), or an `abort` (`rdx = 2`: a node kind not
represented in L, a dangling handle, a full memo), or `rdx = 0` with `rax` the bound the arena's
`bvarBoundMemo F (decE h)` returns on `a₀`, in a final state related to the final memory. -/
theorem bbMemo_x64 [Host] (G : L.Compiler.Layout) (hG : G.Ok)
    (hwf : Prog.wf G.tab walkProg = true)
    (hnres : 1 ≤ G.tab.nres) (k0 : Nat) (hcode : Code (compileProg G.tab walkProg "bb_memo") k0)
    (m : Mem) (a₀ : AState) (hR : ArenaR m a₀) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hnargs : G.nargs = 1) (N F : Nat) (hF : N ≤ F) (dm : MachineData) (ra : Word)
    (hT : dm.regs.rdi.toNat = G.T) (hN : dm.regs.rsi.toNat = N)
    (hmem : MemRel G m dm.dmem) (hroom : G.lo + 8 ≤ G.hi)
    (htop : L.Compiler.rdW dm.dmem (A G.T) = some (UInt64.ofNat G.hi))
    (hargv : ∀ j (h' : j < 1), L.Compiler.rdW dm.dmem (A (G.T + G.tab.args.toNat + 8 * j)) =
      some ([h] : List Word)[j])
    (hra : L.Compiler.rdW dm.dmem (A dm.regs.rsp.toNat) = some ra)
    (hcs : ∀ x, dm.regs.rsp.toNat - 24 ≤ x → x < dm.regs.rsp.toNat + 8 →
      (dm.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧ ¬ G.InArr x ∧ ¬ G.InTab x)
    (hcs24 : 24 ≤ dm.regs.rsp.toNat) (hcs8 : dm.regs.rsp.toNat + 8 < 2 ^ 64) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = dm.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = dm.regs.rbp ∧ st.data.regs.r14 = dm.regs.r14 ∧ st.data.regs.r15 = dm.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨ st.data.regs.rdx = 2 ∨
          (st.data.regs.rdx = 0 ∧ ∃ m' a',
            (bvarBoundMemo F (decE h)).run a₀ = .ok (st.data.regs.rax.toNat, a') ∧
            MemRel G m' st.data.dmem ∧ ArenaR m' a')))
      dm (label enterL) := by
  have hargs : ([h] : List Word).length = bbMemo.nparams := rfl
  have hentry : walkProg.lookup "bb_memo" = some bbMemo := rfl
  refine eventually_weaken _ _ _ _ ?_
    (compile_correct walkProg "bb_memo" G hG hwf k0 hcode bbMemo hentry
      [h] hargs hnargs m N dm ra hT hN hmem hroom htop hargv hra hcs hcs24 hcs8)
  intro st hst
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  rcases h6 with h6 | h6
  · exact Or.inl h6
  · rcases hrun : run walkProg N "bb_memo" [h] m with e | ⟨r, m'⟩
    · rw [hrun] at h6
      rcases e with _ | _ | _ | _ <;> simp_all [OutcomeRel]
    · rw [hrun] at h6
      obtain ⟨hrdx, hres, hm'⟩ := h6
      have hrax : st.data.regs.rax = r.headD 0 := by
        have := hres 0 (by omega); simp only [rres] at this; rwa [show r.getD 0 0 = r.headD 0 by
          cases r <;> rfl] at this
      obtain ⟨a', ha', hA⟩ := bbMemo_run N F hF m a₀ hR h hh r m' hrun
      refine Or.inr (Or.inr ⟨hrdx, m', a', ?_, hm', hA⟩)
      rw [hrax]; exact ha'

end L.Arena
