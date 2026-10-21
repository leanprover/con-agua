import ConAgua.Compiler.Main
import ConAgua.Final.Twin

/-!
# The final theorem: the x64 checker's accept means consistency

`checker_x64_accepts`: run the compiled checker from `ca_enter` on a machine whose input region
holds the bytes `b`; if it returns `rdx = 0` and `rax = ACCEPT`, the twin (con-ron's arena checker)
accepts `[b]` (`TwinAccepts`). The corollaries `x64_model_exists` and `x64_no_False` put that in
con-leche's terms: con-leche's own parser reads `b`, con-leche's pure fold accepts the parsed
records (prepared with some prelude, at some pin list), the accepted environment has a model in
every set theory; and a file declaring a theorem of type `False` is never accepted.

The chain is `compile_correct` (x64 ⊑ L), then `PipelineRefines` (L ⊑ twin, the one named
hypothesis: the per-function refinements the lanes are building, composed), then Theorem 1 and
con-leche (`ConAgua/Final/Twin.lean`). `PipelineRefines` is a hypothesis of the theorems, not an
axiom and not a `sorry`; it is a property of the program `p`, and the theorems hold for every `p`
that has it.

## What is trusted (see `docs/ROADMAP.md` §3, "Trusted base")

* Kraken's x64 semantics (`Ev`, `MachineData`), the assembler, the printer and the loader: the
  printed assembly of `compileProg G.tab p "check"` sits at `k0` (`hcode`);
* the loader's layout: the input bytes, every other array zero, the table and the stack, as `G`
  says (`hG`, `hmem`, `HarnessCall`);
* the harness: it calls `ca_enter` as `HarnessCall` states and reads the verdict as `rdx = 0 ∧ rax =
  ACCEPT`, nothing else;
* buffer to stream: the file's bytes are `b`, read whole (the analogue of con-ron's `hreads`);
* `System.Platform.numBits = 64`.

Not trusted: the capacities `s8`, `s64` the harness picks (any sizes, `PipelineRefines` holds at
all of them: `check` aborts on sizes it cannot work with), the fuel `N` (any `N < 2^62`), the ROM
contents of `p` (pins and prelude bytes: `TwinAccepts` holds at some pin list and con-leche's
theorems at every one; the prelude's records are checked as part of the stream).
-/

namespace ConAgua.Final

open L L.Compiler

universe w

/-- The verdict word `check` returns first for accept. Not `0`, `1` or `2`, so that a status word
or an unset register is never read as accept. -/
def ACCEPT : Word := 0x4143_4345_5054

/-- The memory the loader sets up: the input bytes in byte array `0`, the other byte arrays of
sizes `s8` and the word arrays of sizes `s64`, all zero. -/
def loadMem (b : ByteArray) (s8 s64 : List Nat) : Mem :=
  { bytes := (b.data :: s8.map (Array.replicate · 0)).toArray
    words := (s64.map (Array.replicate · 0)).toArray }

/-- **The named hypothesis: L refines the twin's pipeline.** Every run of `check` (no arguments)
from the loaded memory that returns `ACCEPT` first comes from an accepting twin pipeline on the
same bytes. For every input size below `2^63`, every capacity choice and every L fuel below `2^62`.

This is what the per-function lanes must deliver, composed: from `ArenaR (loadMem b s8 s64)
(AState.init EStore.empty)` (`arenaR_init`, grown to every field, and the input buffer), each stage
of `check` refines its twin stage (`internReservedPins`, `builtinPreludeE`, `parseChunks [b]`,
`preparePrelude`, `internAllPins`, `installFold`, `checkPendingList` from `AState.worker`) in the
`natAddLit_refinesA` shape, at every twin fuel `F ≥ n` for the knot fuels, with L counters for the
twin's counted fuels (`docs/ROADMAP.md` §3 (b)). Partial: nothing is claimed about a run that
aborts, runs out of fuel, or returns anything but `ACCEPT`. -/
def PipelineRefines (p : Prog) : Prop :=
  ∀ (b : ByteArray) (s8 s64 : List Nat) (N : Nat) (rs : List Word) (m' : Mem),
    System.Platform.numBits = 64 → b.size < 2 ^ 63 → N < 2 ^ 62 →
    L.run p N "check" [] (loadMem b s8 s64) = .ok (rs, m') →
    rs.headD 0 = ACCEPT → TwinAccepts [b]

/-- **How the harness calls `ca_enter`** (`compile_correct`'s premises about the machine state, with
no entry arguments): the table address in `rdi`, the fuel in `rsi`, room for the L stack, the stack
top in the table, the return address on the machine stack, and 32 bytes of machine stack that are
mapped and apart from L's regions. -/
structure HarnessCall (G : L.Compiler.Layout) (N : Nat) (dm : MachineData) (ra : Word) : Prop where
  hT : dm.regs.rdi.toNat = G.T
  hN : dm.regs.rsi.toNat = N
  hroom : G.lo + 8 ≤ G.hi
  htop : L.Compiler.rdW dm.dmem (A G.T) = some (UInt64.ofNat G.hi)
  hra : L.Compiler.rdW dm.dmem (A dm.regs.rsp.toNat) = some ra
  hcs : ∀ x, dm.regs.rsp.toNat - 24 ≤ x → x < dm.regs.rsp.toNat + 8 →
    (dm.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧ ¬ G.InArr x ∧ ¬ G.InTab x
  hcs24 : 24 ≤ dm.regs.rsp.toNat
  hcs8 : dm.regs.rsp.toNat + 8 < 2 ^ 64

/-- **The final theorem.** A Kraken host holds the compiled checker `p` (any program with
`PipelineRefines`); the loader put the input bytes `b` and zeroed arrays of any sizes in the layout
`G`; the harness calls `ca_enter` with fuel `N < 2^62`. Then the machine returns to the caller, and
if it reports `rdx = 0` with `rax = ACCEPT`, the twin's pipeline accepts `[b]`. -/
theorem checker_x64_accepts [Host] (p : Prog) (hP : PipelineRefines p)
    (G : L.Compiler.Layout) (hG : G.Ok) (hwf : Prog.wf G.tab p = true) (hnres : 1 ≤ G.tab.nres)
    (k0 : Nat) (hcode : Code (compileProg G.tab p "check") k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (hnargs : G.nargs = 0)
    (b : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (s8 s64 : List Nat) (N : Nat) (hN62 : N < 2 ^ 62) (dm : MachineData) (ra : Word)
    (hmem : MemRel G (loadMem b s8 s64) dm.dmem) (hc : HarnessCall G N dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label enterL) := by
  have hargs : ([] : List Word).length = fd.nparams := hnp.symm
  refine eventually_weaken _ _ _ _ ?_
    (compile_correct p "check" G hG hwf k0 hcode fd hentry [] hargs hnargs
      (loadMem b s8 s64) N dm ra hc.hT hc.hN hmem hc.hroom hc.htop (fun i h => absurd h (by simp))
      hc.hra hc.hcs hc.hcs24 hc.hcs8)
  intro st ⟨hpc, _, _, _, _, hout⟩
  refine ⟨hpc, fun hrdx hacc => ?_⟩
  rcases hout with h1 | hout
  · rw [hrdx] at h1; exact absurd h1 (by decide)
  rcases hrun : L.run p N "check" [] (loadMem b s8 s64) with e | ⟨rs, m'⟩
  · rw [hrun] at hout
    rcases e with _ | _ | _ | _ <;> simp_all [OutcomeRel]
  · rw [hrun] at hout
    obtain ⟨-, hres, -⟩ := hout
    have hrax : st.data.regs.rax = rs.headD 0 := by
      have := hres 0 (by omega)
      simp only [rres] at this
      rwa [show rs.getD 0 0 = rs.headD 0 by cases rs <;> rfl] at this
    exact hP b s8 s64 N rs m' h64 hb hN62 hrun (hrax ▸ hacc)

/-- **Corollary: an accepted file has a model.** Under `checker_x64_accepts`'s premises, if the
machine reports accept, con-leche's parser reads `b` into records `rc`, con-leche's pure fold
accepts them (prepared with some prelude, at some pin list) with an environment `env`, and `env`
has a model in the set theory `V`. -/
theorem x64_model_exists (V : Type w) [ConLeche.SetTheory V] [Host] (p : Prog)
    (hP : PipelineRefines p)
    (G : L.Compiler.Layout) (hG : G.Ok) (hwf : Prog.wf G.tab p = true) (hnres : 1 ≤ G.tab.nres)
    (k0 : Nat) (hcode : Code (compileProg G.tab p "check") k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (hnargs : G.nargs = 0)
    (b : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (s8 s64 : List Nat) (N : Nat) (hN62 : N < 2 ^ 62) (dm : MachineData) (ra : Word)
    (hmem : MemRel G (loadMem b s8 s64) dm.dmem) (hc : HarnessCall G N dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT →
          ∃ (pins : List ConLeche.NatOpPinSet) (preC : ConLeche.Frontend.PreludeIx)
            (rc : ConLeche.Frontend.ParseResultD) (F : Nat) (env : ConLeche.Env),
            ConLeche.Frontend.parseChunks [b] = .ok rc ∧
            ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pins
              (ConLeche.Frontend.preparePrelude preC rc.decls).toList = .ok env ∧
            Nonempty (ConLeche.Model V env)))
      dm (label enterL) :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, h⟩ => ⟨hpc, fun hrdx hacc => twinAccepts_model V (h hrdx hacc)⟩)
    (checker_x64_accepts p hP G hG hwf hnres k0 hcode fd hentry hnp hnargs b h64 hb s8 s64 N hN62
      dm ra hmem hc)

/-- **Corollary: no `False`.** Under `checker_x64_accepts`'s premises, if `b` declares a theorem of
type `False` (in `jsonWithTheoremFalse`'s shape), the machine returns and does not report accept. -/
theorem x64_no_False (V : Type w) [ConLeche.SetTheory V] [Host] (p : Prog)
    (hP : PipelineRefines p)
    (G : L.Compiler.Layout) (hG : G.Ok) (hwf : Prog.wf G.tab p = true) (hnres : 1 ≤ G.tab.nres)
    (k0 : Nat) (hcode : Code (compileProg G.tab p "check") k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (hnargs : G.nargs = 0)
    (b : ByteArray) (hfalse : ConLeche.jsonWithTheoremFalse [b])
    (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (s8 s64 : List Nat) (N : Nat) (hN62 : N < 2 ^ 62) (dm : MachineData) (ra : Word)
    (hmem : MemRel G (loadMem b s8 s64) dm.dmem) (hc : HarnessCall G N dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        ¬ (st.data.regs.rdx = 0 ∧ st.data.regs.rax = ACCEPT))
      dm (label enterL) :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, h⟩ => ⟨hpc, fun ⟨hrdx, hacc⟩ => twinAccepts_no_False V hfalse (h hrdx hacc)⟩)
    (checker_x64_accepts p hP G hG hwf hnres k0 hcode fd hentry hnp hnargs b h64 hb s8 s64 N hN62
      dm ra hmem hc)

/-! ## The hypothesis is satisfiable

`PipelineRefines` is not contradictory: a `check` that never accepts has it, so the theorems above are
not vacuous in `p`. (What they say about the real checker is the point of `PipelineRefines`'s
proof, which the lanes are building.) -/

/-- A `check` that always rejects. -/
def rejectProg : Prog := [("check", { nparams := 0, nlocals := 0, body := .ret [.const 0] })]

/-- It refines the twin, vacuously. -/
theorem pipelineRefines_reject : PipelineRefines rejectProg := by
  intro b s8 s64 N rs m' _ _ _ hrun hacc
  cases N with
  | zero =>
    simp [L.run, invoke, lookupFn, rejectProg, callFn, exec, StateT.run, throw, throwThe,
      MonadExceptOf.throw, Except.map] at hrun
    cases hrun
  | succ n =>
    simp [L.run, invoke, lookupFn, rejectProg, callFn, exec, step, evalArgs, evalE] at hrun
    obtain ⟨rfl, -⟩ := hrun
    simp [Sig.retVal, Sig.retOr] at hacc
    exact absurd hacc (by decide)

/-! The ledger: con-leche's three axioms. `PipelineRefines` is a hypothesis of the statements, not an
axiom of the environment, so it is not listed. -/

/-- info: 'ConAgua.Final.x64_model_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms x64_model_exists

/-- info: 'ConAgua.Final.x64_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms x64_no_False

end ConAgua.Final
