module

public import ConAguaX86.Compiler.Main

@[expose] public section

/-!
# The compiler theorem for a program that refines another

`compile_correct_frame_ref`: `compile_correct_frame` for `q`, with the outcome of `p`'s run.
-/

namespace L.Compiler

open L

/-- The outcome of `q`'s run is the outcome of `p`'s. -/
theorem Refines.outcome {q p : Prog} (hq : Refines q p) {G : Layout} {N : Nat} {f : FnName} {vs : List Word}
    {m : Mem} {s : MachineData} (h : OutcomeRel G (L.run q N f vs m) s) : OutcomeRel G (L.run p (N + abiInl) f vs m) s := by
  rcases e : L.run q N f vs m with err | r
  · cases err with
    | outOfFuel => rw [e] at h; exact h.elim
    | _ => rw [hq.run N f vs m _ e (by simp), ← e]; exact h
  · rw [hq.run N f vs m _ e (by simp), ← e]; exact h

/-- **`compile_correct_frame` for a program `q` that refines `p`**: `q` is compiled, the outcome is
`p`'s run with `abiInl` more units of fuel. -/
theorem compile_correct_frame_ref [Host] (q p : Prog) (hq : Refines q p) (entry : FnName) (G : Layout) (hG : G.Ok)
    (X : AsmTab) (hX : AsmOk q G X)
    (hwf : Prog.wf G.tab q = true) (k0 : Nat) (hcode : Code (compileProgX X G.tab q entry) k0)
    (fd : FunDecl) (hentry : p.lookup entry = some fd)
    (args : List Word) (hargs : args.length = fd.nparams) (hnargs : G.nargs = args.length)
    (m : Mem) (N : Nat) (d : MachineData) (ra : Word)
    (hT : d.regs.rdi.toNat = G.T) (hN : d.regs.rsi.toNat = N)
    (hmem : MemRel G m d.dmem) (hroom : G.lo + 8 ≤ G.hi)
    (htop : rdW d.dmem (A G.T) = some (UInt64.ofNat G.hi))
    (hargv : ∀ i (h : i < args.length), rdW d.dmem (A (G.T + G.tab.args.toNat + 8 * i)) = some args[i])
    (hra : rdW d.dmem (A d.regs.rsp.toNat) = some ra)
    (hcs : ∀ x, d.regs.rsp.toNat - 24 ≤ x → x < d.regs.rsp.toNat + 8 →
      (d.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧ ¬ G.InArr x ∧ ¬ G.InTab x)
    (hcs24 : 24 ≤ d.regs.rsp.toNat) (hcs8 : d.regs.rsp.toNat + 8 < 2 ^ 64)
    (hsv : ∀ x, G.tabEnd ≤ x → x < G.tabEnd + 32 → (d.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧
      ¬ G.InArr x ∧ (x < d.regs.rsp.toNat - 24 ∨ d.regs.rsp.toNat + 8 ≤ x))
    (hsv64 : G.tabEnd + 32 < 2 ^ 64) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = d.regs.r15 ∧
        CalleeKept d.regs st.data.regs ∧ MemFrame G d.regs.rsp.toNat d.dmem st.data.dmem ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (L.run p (N + abiInl) entry args m) st.data))
      d (label enterL) := by
  obtain ⟨fd', hl', hnp⟩ := hq.lookup entry fd hentry
  exact eventually_weaken _ _ _ _ (fun _ ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8.imp_right hq.outcome⟩)
    (compile_correct_frame q entry G hG X hX hwf k0 hcode fd' hl' args (by rw [hnp]; exact hargs) hnargs m N d ra hT hN
      hmem hroom htop hargv hra hcs hcs24 hcs8 hsv hsv64)

end L.Compiler
