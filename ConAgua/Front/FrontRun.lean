import ConAgua.Front.LineRefine
import ConAgua.Front.DriverRefine
import ConAgua.Scan.Validator

/-!
# Bytes → stores: `front_run()` refines con-ron's `parseBytes`

The whole-buffer driver (`ConAgua.Front.Driver`) instantiated with `front_init` and `front_line`:
`frontRun_refines` says that when `front_run()` returns `0`, con-ron's `parseBytes b` (from the
arena state `a₀` the memory is related to) accepts, and the memory after is related to its final
arena state by `ArenaD` and to its final parse state by `StateDR`. `frontAllProg` is the whole
program; `frontAllProg_lookups` discharges every lookup hypothesis.

The models the driver iterates are `front_init`'s and `front_line`'s, each with the fact that the
input bytes are unchanged (`Keep`, a property of every L run of a program without byte stores),
which the next line's spec needs.
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Front.Fields
open ConLeche.Frontend
open ConRon.Arena ConRon.Arena.Frontend

namespace L.Front

/-- `front_line`'s model, with the input unchanged, as three words. -/
def lineKW (b : Array UInt8) (m : Mem) (i : Word) : Option (Word × Word × Mem) :=
  match frontLineW b m i with
  | none => none
  | some (r, m') => if m'.arr8 IN = m.arr8 IN then some (r.headD 0, r.tail.headD 0, m') else none

/-- `front_init`'s model, with the input unchanged. -/
def initKW (m : Mem) : Option Mem :=
  match frontInitW m with
  | none => none
  | some m' => if m'.arr8 IN = m.arr8 IN then some m' else none

/-- The driver's invariant: the input is `b`, and the memory is related to the arena and parse
states. -/
def FrontInv (b : ByteArray) (m : Mem) (a : AState) (st : StateD) : Prop :=
  m.arr8 IN = b.data ∧ ArenaD m a ∧ StateDR m st

theorem frontLineW_shape (b : Array UInt8) (m m' : Mem) (i : Word) (r : List Word)
    (h : frontLineW b m i = some (r, m')) : r = [0, 0] ∨ r = [1, r.tail.headD 0] := by
  unfold frontLineW at h
  split at h
  · simp at h; exact .inl h.1.symm
  split at h
  · obtain ⟨m₁, -, h⟩ := Option.map_eq_some_iff.mp h
    simp only [okRes, Prod.mk.injEq] at h
    exact .inr (by rw [← h.1]; rfl)
  · simp at h; exact .inr (by rw [← h.1]; rfl)

section refine
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem lineKW_step (m m' : Mem) (i : USize) (ok nx : Word) (st : StateD) (a : AState)
    (hI : FrontInv b m a st) (_hi : i < b.usize) (h : lineKW b.data m i.toUInt64 = some (ok, nx, m'))
    (hok : ok ≠ 0) : LineStepI (FrontInv b) b i nx st a m' := by
  unfold lineKW at h
  split at h
  · cases h
  rename_i r m₁ hW
  split at h
  · rename_i hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rcases frontLineW_shape _ _ _ _ _ hW with hr | hr
    · rw [hr] at hok; exact absurd rfl hok
    rw [hr] at hW
    obtain ⟨r', q, st', h1, h2, h3, h4, h5, h6⟩ :=
      frontLineW_refines b h64 hsize m m₁ hI.1 i a st hI.2.1 hI.2.2 _ hW
    exact ⟨r', q, st', h1, h2, h3, h4, ⟨hk.trans hI.1, h5, h6⟩⟩
  · cases h

/-- **The driver's model refines `parseBytes`**: if `front_init`'s and then the loop's models
accept from a memory holding `b` and related to `a₀` and the blank parse state, `parseBytes b`
accepts with the invariant after. -/
theorem frontRunW_refines (m m' : Mem) (a₀ : AState) (hm : m.arr8 IN = b.data)
    (hA : ArenaD m a₀) (hD : StateDR m StateD.blank)
    (h : runI (lineKW b.data) b.size (initKW m) = some (0, m')) :
    ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧ FrontInv b m' a' st' := by
  refine runI_refines (FrontInv b) b h64 hsize (lineKW b.data) (lineKW_step b h64 hsize)
    (fun m a => m.arr8 IN = b.data ∧ ArenaD m a ∧ StateDR m StateD.blank) initKW ?_ m m' a₀
    ⟨hm, hA, hD⟩ h
  intro m m₁ a ⟨hm, hA, hD⟩ hi
  unfold initKW at hi
  split at hi
  · cases hi
  rename_i m₂ hW
  split at hi
  · rename_i hk
    cases hi
    obtain ⟨h1, h2, h3⟩ := frontInitW_refines m m₁ a hA hD hW
    refine ⟨AM.res StateD.init a, AM.st StateD.init a, ?_, hk.trans hm, h2, h3⟩
    exact AM.run_of_ok _ _ h1
  · cases hi

end refine

/-! ## The L run -/

section run
variable (p : Prog) (hS : ScanLookups p) (hL : FrontLookups p)
  (hpf : p.lookup "front_line" = some frontLine) (hps : p.lookup "str_put" = some strPut)
  (hpn : p.lookup "apply_nstr" = some applyNStr) (hpu : p.lookup "apply_nnum" = some applyNNum)
  (hpl : p.lookup "apply_level" = some applyLevel)
  (hpr : p.lookup "apply_rec" = some applyRec) (hpt : p.lookup "apply_str" = some applyStr)
  (hE : ExprLookups p) (hpy : p.lookup "apply_any" = some applyAny)
  (hpi : p.lookup "front_init" = some frontInit) (hpd : p.lookup "front_run" = some frontRun)

include hS hL hpf hps hpn hpu hpl hpr hpt hE hpy in
theorem frontLineK_spec (b : Array UInt8) (hb : b.size < 2 ^ 63) (Z : Nat) (hZ : Z < 2 ^ 63)
    (n : Nat) (s₀ : St) (i : Word) (hm : s₀.mem.arr8 IN = b) (hz : (s₀.mem.arr64 POOL).size = Z)
    (hi : i < UInt64.ofNat b.size) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "front_line" [i]
    ⦃fun r s' => lineKW b s₀.mem i = some (r.headD 0, r.tail.headD 0, s'.mem) ∧
      Keep s₀.mem s'.mem ∧ LocEq s' s₀; ⊤⦄ := by
  have hi' : i.toNat ≤ b.size := by have := L.Scan.lt_of_lt_ofNat hi; omega
  have h := Triple.keep hE.no_st8
    (frontLine_spec p hS hL hpf hps hpn hpu hpl hpr hpt hE hpy b hb n s₀ hm i hi' (by omega))
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hW, hk, hl⟩ := M.of_run (P := fun s => s = s₀) hs hrun h
  refine ⟨?_, hk, hl⟩
  unfold lineKW
  rw [hW]
  simp [Keep.arr8 hk]

include hL hpi hE in
theorem frontInitK_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "front_init" []
    ⦃fun _ s' => initKW s₀.mem = some s'.mem ∧ Keep s₀.mem s'.mem ∧ LocEq s' s₀; ⊤⦄ := by
  have h := Triple.keep hE.no_st8 (frontInit_spec p hL hpi n s₀)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨⟨-, hW⟩, hk, hl⟩ := M.of_run (P := fun s => s = s₀) hs hrun h
  refine ⟨?_, hk, hl⟩
  unfold initKW
  rw [hW]
  simp [Keep.arr8 hk]

include hS hL hpf hps hpn hpu hpl hpr hpt hE hpy hpi hpd in
/-- **Bytes → stores, in one theorem**: when `front_run()` returns `0` on a memory holding the
input `b` and related to the arena state `a₀` (by `ArenaD`) and to the blank parse state, con-ron's
`parseBytes b` accepts from `a₀`, and the memory after is related to its final arena state by
`ArenaD` and to its final parse state by `StateDR`. -/
theorem frontRun_refines (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data)
    (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63) (a₀ : AState) (hA : ArenaD s₀.mem a₀)
    (hD : StateDR s₀.mem StateD.blank) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem st'; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun h0
  have hW := M.of_run (P := fun s => s = s₀) hs hrun
    (frontRun_spec p (lineKW b.data) b.data _
      (fun n s₀ i hm hz hi => frontLineK_spec p hS hL hpf hps hpn hpu hpl hpr hpt hE hpy b.data
        hsize _ hpool n s₀ i hm hz hi)
      initKW (fun n s₀ _ _ => frontInitK_spec p hL hE hpi n s₀) hpd n s₀ hm rfl)
  rw [h0] at hW
  obtain ⟨st', a', h1, -, h2, h3⟩ := frontRunW_refines b h64 hsize s₀.mem s'.mem a₀ hm hA hD hW
  exact ⟨st', a', h1, h2, h3⟩

end run

/-! ## The whole program -/

/-- Every function of the frontend: the validator, the fields passes, the stores, the apply
steps, the line and the driver. -/
def frontAllProg : Prog := L.Scan.Validator.valProg ++
  [("rec_nat_list", recNatList), ("rec_str_name", recStrName),
   ("rec_num_name", recNumName), ("rec_line_loop", recLineLoop), ("obj_val", objVal),
   ("rec_obj", recObj), ("expr_val", exprVal), ("rec_expr_loop", recExprLoop)] ++
  exprProg.filter (fun f => f.1 != "skip_digits" && f.1 != "num_end") ++
  [("front_line", frontLine), ("apply_rec", applyRec), ("apply_str", applyStr),
   ("apply_any", applyAny), ("front_run", frontRun),
   ("esc_sur", L.Front.Unescape.escSur), ("esc_one", L.Front.Unescape.escOne),
   ("utf8_put", L.Front.Unescape.utf8Put), ("str_put_esc", L.Front.Unescape.strPutEsc)]

theorem frontAllProg_noSt8 : frontAllProg.noSt8 = true := by decide

/-- The compiler's static check passes (`compile_correct` applies): one byte array, 67 word
arrays. -/
theorem frontAllProg_wf :
    L.Compiler.Prog.wf (L.Compiler.Prog.tab frontAllProg 1 67) frontAllProg = true := by
  decide +kernel

theorem frontAllProg_scan : ScanLookups frontAllProg := by constructor <;> rfl

theorem frontAllProg_front : FrontLookups frontAllProg := by constructor <;> rfl

theorem frontAllProg_expr : ExprLookups frontAllProg := by
  refine ⟨frontAllProg_front, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, frontAllProg_noSt8⟩ <;> rfl

/-- **Bytes → stores, for the whole program.** -/
theorem frontAll_refines (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data)
    (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63) (a₀ : AState) (hA : ArenaD s₀.mem a₀)
    (hD : StateDR s₀.mem StateD.blank) :
    ⦃fun s => s = s₀⦄
    invoke frontAllProg (exec frontAllProg n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem st'; ⊤⦄ :=
  frontRun_refines frontAllProg frontAllProg_scan frontAllProg_front rfl rfl rfl rfl rfl rfl rfl
    frontAllProg_expr rfl rfl rfl b h64 hsize n s₀ hm hpool a₀ hA hD

/-- A memory with 67 word arrays of 4096 words and the input `s`. -/
def frontMemOf (s : String) : Mem := { initMem (List.replicate 67 4096) with bytes := #[s.toUTF8.data] }

/- A header, a name, a level, and expression lines of six kinds (a 30-digit literal among them):
accepted. -/
#guard (run frontAllProg 100000 "front_run" [] (frontMemOf
  "{\"meta\":{\"x\":1}}\n{\"in\":1,\"str\":{\"pre\":0,\"str\":\"N\\u00e4t\\n\"}}\n{\"il\":1,\"succ\":0}\n\
  {\"ie\":0,\"sort\":1}\n{\"ie\":1,\"const\":{\"name\":1,\"us\":[0,1]}}\n\
  {\"ie\":2,\"app\":{\"fn\":1,\"arg\":0}}\n{\"ie\":3,\"natVal\":\"123456789012345678901234567890\"}\n\
  {\"ie\":4,\"lam\":{\"binderInfo\":\"default\",\"body\":0,\"name\":1,\"type\":2}}")).toOption.map
  (·.1) == some [0]
/- A line that does not scan: its number. An unbound id: the run aborts. -/
#guard (run frontAllProg 100000 "front_run" [] (frontMemOf
  "{\"il\":1,\"succ\":0}\n{\"il\":2,\"succ\":}\n")).toOption.map (·.1) == some [2]
#guard (run frontAllProg 100000 "front_run" [] (frontMemOf
  "{\"ie\":0,\"sort\":5}\n")).toOption.isNone

end L.Front
