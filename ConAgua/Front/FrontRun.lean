import ConAgua.Front.LineRefine
import ConAgua.Front.DriverRefine
import ConAgua.Scan.Validator
import ConRon.Bridge.Frontend.Chunks

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
open ConLeche.Frontend hiding StateD RecordVerdict applyLine parseBytes ParseResultD
open ConRon.Arena ConRon.Arena.Frontend

namespace L.Front

/-- `front_line`'s model, with the input unchanged, as three words. -/
noncomputable def lineKW (p : Prog) (b : Array UInt8) (m : Mem) (i : Word) :
    Option (Word × Word × Mem) :=
  match frontLineW p b m i with
  | none => none
  | some (r, m') => if m'.arr8 IN = m.arr8 IN then some (r.headD 0, r.tail.headD 0, m') else none

/-- `front_init`'s model, with the input unchanged. -/
def initKW (m : Mem) : Option Mem :=
  match frontInitW m with
  | none => none
  | some m' => if m'.arr8 IN = m.arr8 IN then some m' else none

/-- What con-ron's own bridge keeps of the arena and parse states across the lines
(`ConRon.Bridge.Frontend.applyLine_run`): the store is well formed (`StateOK`, which the apply step
of an `inductive` line reads), the scratch tier is off, the pins hold, and the parse state is
persistent and related to con-leche's. -/
def TwinOK (a : AState) (st : StateD) : Prop :=
  ConRon.Bridge.StateOK a ∧ a.store.scratchOn = false ∧ ConRon.Bridge.PinsOK a ∧
    ConRon.Bridge.Frontend.PersStateD st ∧ ∃ sc, ConRon.Bridge.Frontend.StateDRel a.store st sc

/-- A line con-ron applies keeps `TwinOK`. -/
theorem TwinOK.line {a : AState} {st : StateD} (h : TwinOK a st) {r : LineRec} {st' : StateD}
    (h1 : AM.ok (applyLine st r) a) (h2 : AM.res (applyLine st r) a = .inl st') :
    TwinOK (AM.st (applyLine st r) a) st' := by
  obtain ⟨hok, hoff, hpins, hp, sc, hrel⟩ := h
  cases hr : (applyLine st r).run a with
  | error e => simp [AM.ok, hr] at h1
  | ok q =>
    obtain ⟨x, a'⟩ := q
    have hx : x = .inl st' := by simpa [AM.res, hr] using h2
    have ha : AM.st (applyLine st r) a = a' := by simp [AM.st, hr]
    rw [ha]
    subst hx
    obtain ⟨hstep, hpers, y, -, hsum⟩ := ConRon.Bridge.Frontend.applyLine_run hok hoff hpins hrel hp hr
    refine ⟨hstep.ok, by rw [hstep.scratch]; exact hoff, hpins.mono hstep.ext hstep.pins, hpers st' rfl, ?_⟩
    cases y with
    | inl sc' => exact ⟨sc', hsum⟩
    | inr w => exact hsum.elim

/-- `StateD.init` establishes `TwinOK`. -/
theorem TwinOK.init {a a₁ : AState} {st₀ : StateD} (hok : ConRon.Bridge.StateOK a)
    (hoff : a.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a)
    (h : StateD.init.run a = .ok (st₀, a₁)) : TwinOK a₁ st₀ := by
  obtain ⟨hstep, hp, hrel⟩ := ConRon.Bridge.Frontend.StateD_init_run hok hoff h
  exact ⟨hstep.ok, by rw [hstep.scratch]; exact hoff, hpins.mono hstep.ext hstep.pins, hp, _, hrel⟩

/-- The driver's invariant: the input is `b`, the memory is related to the arena and parse states,
and con-ron's bridge invariant holds of them (`TwinOK`). -/
def FrontInv (b : ByteArray) (m : Mem) (a : AState) (st : StateD) : Prop :=
  m.arr8 IN = b.data ∧ ArenaD m a ∧ StateDR m st ∧ TwinOK a st ∧ ModeOK m

theorem frontLineW_shape (p : Prog) (b : Array UInt8) (m m' : Mem) (i : Word) (r : List Word)
    (h : frontLineW p b m i = some (r, m')) : r = [0, 0] ∨ r = [1, r.tail.headD 0] := by
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

theorem lineKW_step (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (m m' : Mem) (i : USize) (ok nx : Word) (st : StateD)
    (a : AState) (hI : FrontInv b m a st) (_hi : i < b.usize)
    (h : lineKW p b.data m i.toUInt64 = some (ok, nx, m'))
    (hok : ok ≠ 0) : LineStepI (FrontInv b) b i nx st a m' := by
  unfold lineKW at h
  split at h
  · cases h
  rename_i r m₁ hW
  split at h
  · rename_i hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rcases frontLineW_shape _ _ _ _ _ _ hW with hr | hr
    · rw [hr] at hok; exact absurd rfl hok
    rw [hr] at hW
    obtain ⟨⟨r', q, st', h1, h2, h3, h4, h5, h6⟩, hM⟩ :=
      frontLineW_refines b h64 hsize p hFI hAI hII hXI m m₁ hI.1 i a st hI.2.1 hI.2.2.1
        hI.2.2.2.2 hI.2.2.2.1.1 _ hW
    exact ⟨r', q, st', h1, h2, h3, h4, ⟨hk.trans hI.1, h5, h6, hI.2.2.2.1.line h3 h4, hM⟩⟩
  · cases h

omit h64 hsize in
/-- `front_init`'s model keeps the mode (it interns the anonymous name and `zero`). -/
theorem frontInitW_mode (m m' : Mem) (hW : frontInitW m = some m') (hmo : ModeOK m) : ModeOK m' := by
  simp only [frontInitW] at hW
  cases h1 : putK NID 0 (nainternW m) with
  | none => rw [h1] at hW; simp [initK] at hW
  | some m₁ =>
    rw [h1, initK_some] at hW
    obtain ⟨w, m₃, hI, -, hp⟩ := putK_eq h1
    obtain ⟨w', m₄, hI', -, hp'⟩ := putK_eq hW
    have e1 := MemFrame.modeOK (tblPutW_frame (.inl rfl) hp)
      (h := MemFrame.modeOK (consInternM_frame nanonCS_wf hI) (by decide) (by decide) hmo)
    exact MemFrame.modeOK (tblPutW_frame (.inr (.inl rfl)) hp')
      (h := MemFrame.modeOK (consInternM_frame zeroCS_wf hI') (by decide) (by decide) e1)

omit h64 hsize in
/-- `front_init`'s model, from a memory related to `a` and the blank parse state, establishes the
driver's invariant. -/
theorem initKW_inv : ∀ (m m₁ : Mem) (a : AState),
    (m.arr8 IN = b.data ∧ ArenaD m a ∧ StateDR m StateD.blank ∧ ConRon.Bridge.StateOK a ∧
      a.store.scratchOn = false ∧ ConRon.Bridge.PinsOK a ∧ ModeOK m) → initKW m = some m₁ →
    ∃ st₀ a₁, StateD.init.run a = .ok (st₀, a₁) ∧ FrontInv b m₁ a₁ st₀ := by
  intro m m₁ a ⟨hm, hA, hD, hok, hoff, hpins, hmo⟩ hi
  unfold initKW at hi
  split at hi
  · cases hi
  rename_i m₂ hW
  split at hi
  · rename_i hk
    cases hi
    obtain ⟨h1, h2, h3⟩ := frontInitW_refines m m₁ a hA hD hW
    have hr := AM.run_of_ok _ _ h1
    exact ⟨AM.res StateD.init a, AM.st StateD.init a, hr, hk.trans hm, h2, h3,
      TwinOK.init hok hoff hpins hr, frontInitW_mode m m₁ hW hmo⟩
  · cases hi

/-- **The driver's model refines `parseBytes`**: if `front_init`'s and then the loop's models
accept from a memory holding `b` and related to `a₀` and the blank parse state, `parseBytes b`
accepts with the invariant after. -/
theorem frontRunW_refines (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (m m' : Mem) (a₀ : AState) (hm : m.arr8 IN = b.data)
    (hA : ArenaD m a₀) (hD : StateDR m StateD.blank) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀) (hmo : ModeOK m)
    (h : runI (lineKW p b.data) b.size (initKW m) = some (0, m')) :
    ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧ FrontInv b m' a' st' :=
  runI_refines (FrontInv b) b h64 hsize (lineKW p b.data)
    (lineKW_step b h64 hsize p hFI hAI hII hXI)
    (fun m a => m.arr8 IN = b.data ∧ ArenaD m a ∧ StateDR m StateD.blank ∧ ConRon.Bridge.StateOK a ∧
      a.store.scratchOn = false ∧ ConRon.Bridge.PinsOK a ∧ ModeOK m) initKW (initKW_inv b)
    m m' a₀ ⟨hm, hA, hD, hok, hoff, hpins, hmo⟩ h

end refine

/-- A run invariant `∃ a st, Inv' m a st` of the memory, kept by every line applied (`ok ≠ 0`),
from a step lemma at `USize` positions (as `lineKW_step`). -/
theorem inv_step (p : Prog) (Inv' : Mem → AState → StateD → Prop) (b : ByteArray)
    (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
    (hstep : ∀ (m m' : Mem) (i : USize) (ok nx : Word) (st : StateD) (a : AState), Inv' m a st →
      i < b.usize → lineKW p b.data m i.toUInt64 = some (ok, nx, m') → ok ≠ 0 →
      LineStepI Inv' b i nx st a m')
    (m : Mem) (i : Word) (ok nx : Word) (m' : Mem) (hI : ∃ a st, Inv' m a st)
    (hi : i < UInt64.ofNat b.size) (hok : ok ≠ 0) (h : lineKW p b.data m i = some (ok, nx, m')) :
    ∃ a st, Inv' m' a st := by
  obtain ⟨a, st, hI⟩ := hI
  have hi' := L.Scan.lt_of_lt_ofNat hi
  have hbs : b.data.size = b.size := rfl
  have hu : (USize.ofNat i.toNat).toNat = i.toNat := ConAgua.Scan.StrLink.usz h64 _ (by omega)
  have hiu : (USize.ofNat i.toNat).toUInt64 = i := by
    apply UInt64.toNat_inj.mp; rw [USize.toNat_toUInt64, hu]
  have hlt : USize.ofNat i.toNat < b.usize := by
    rw [USize.lt_iff_toNat_lt, hu, ConAgua.Scan.usize_toNat_eq b h64 (by omega)]; omega
  rw [← hiu] at h
  obtain ⟨_r, _q, st', _h1, _h2, _h3, _h4, h5⟩ := hstep m m' _ ok nx st a hI hlt h hok
  exact ⟨_, st', h5⟩

/-! ## The L run -/

section run
variable (p : Prog) (hS : ScanLookups p) (hL : FrontLookups p)
  (hpf : p.lookup "front_line" = some frontLine) (hps : p.lookup "str_put" = some strPut)
  (hpn : p.lookup "apply_nstr" = some applyNStr) (hpu : p.lookup "apply_nnum" = some applyNNum)
  (hpl : p.lookup "apply_level" = some applyLevel)
  (hpr : p.lookup "apply_rec" = some applyRec) (hpt : p.lookup "apply_str" = some applyStr)
  (hE : ExprLookups p) (hpy : p.lookup "apply_any" = some applyAny)
  (hF : DeclFieldLookups p) (hDL : DeclLookups p) (hpz : p.lookup "apply_dline" = some applyDLine)
  (hpi : p.lookup "front_init" = some frontInit) (hpd : p.lookup "front_run" = some frontRun)
  (hFI : L.Front.Ind.IndFieldLookups p) (hAI : L.Front.Ind.IndApplyLookups p)
  (hII : L.Front.Ind.IndInstallLookups p) (hXI : L.Front.Ind.IndLineLookups p)

include hS hL hpf hps hpn hpu hpl hpr hpt hE hpy hF hDL hpz in
/-- `front_line` under a run invariant `Inv` that bounds the pool's top (`hInv`) and that every
line applied keeps (`hpres`, a fact of the model). -/
theorem frontLineK_spec (b : Array UInt8) (hb : b.size < 2 ^ 63) (Inv : Mem → Prop)
    (hInv : ∀ m, Inv m → pcap m < 2 ^ 63 ∧ m.top.toNat ≤ pcap m)
    (hpres : ∀ m i ok nx m', Inv m → i < UInt64.ofNat b.size → ok ≠ 0 →
      lineKW p b m i = some (ok, nx, m') → Inv m')
    (n : Nat) (s₀ : St) (i : Word) (hm : s₀.mem.arr8 IN = b) (hI : Inv s₀.mem)
    (hi : i < UInt64.ofNat b.size) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "front_line" [i]
    ⦃fun r s' => lineKW p b s₀.mem i = some (r.headD 0, r.tail.headD 0, s'.mem) ∧
      Keep s₀.mem s'.mem ∧ (r.headD 0 ≠ 0 → Inv s'.mem) ∧ LocEq s' s₀; ⊤⦄ := by
  have hi' : i.toNat ≤ b.size := by have := L.Scan.lt_of_lt_ofNat hi; omega
  obtain ⟨h1, h2⟩ := hInv _ hI
  have h := Triple.keep hE.no_st8
    (frontLine_spec p hS hL hpf hps hpn hpu hpl hpr hpt hE hpy hF hDL hpz b hb n s₀ hm i hi' h1 h2)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hW, hk, hl⟩ := M.of_run (P := fun s => s = s₀) hs hrun h
  have hK : lineKW p b s₀.mem i = some (r.headD 0, r.tail.headD 0, s'.mem) := by
    unfold lineKW
    rw [hW]
    simp [Keep.arr8 hk]
  exact ⟨hK, hk, fun h0 => hpres _ _ _ _ _ hI hi h0 hK, hl⟩

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

include hL hpi hE in
/-- `front_init` from the run's first memory establishes a run invariant `∃ a st, Inv m a st`
(from the model's init obligation of `runI_refines`). -/
theorem initK_inv (Inv : Mem → AState → StateD → Prop) (Inv₀ : Mem → AState → Prop)
    (hinit : ∀ m m₁ a, Inv₀ m a → initKW m = some m₁ →
      ∃ st₀ a₁, StateD.init.run a = .ok (st₀, a₁) ∧ Inv m₁ a₁ st₀)
    (s₀ : St) (a₀ : AState) (h₀ : Inv₀ s₀.mem a₀) (n : Nat) (s₁ : St) (hs₁ : s₁.mem = s₀.mem) :
    ⦃fun s => s = s₁⦄ invoke p (exec p n) "front_init" []
    ⦃fun _ s' => initKW s₁.mem = some s'.mem ∧ Keep s₁.mem s'.mem ∧
      (∃ a st, Inv s'.mem a st) ∧ LocEq s' s₁; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hi, hk, hl⟩ := M.of_run (P := fun s => s = s₁) hs hrun (frontInitK_spec p hL hE hpi n s₁)
  refine ⟨hi, hk, ?_, hl⟩
  rw [hs₁] at hi
  obtain ⟨st₀, a₁, -, hI⟩ := hinit _ _ _ h₀ hi
  exact ⟨a₁, st₀, hI⟩

include hS hL hpf hps hpn hpu hpl hpr hpt hE hpy hF hDL hpz hpi hpd hFI hAI hII hXI in
/-- **Bytes → stores, in one theorem**: when `front_run()` returns `0` on a memory holding the
input `b` and related to the arena state `a₀` (by `ArenaD`) and to the blank parse state, con-ron's
`parseBytes b` accepts from `a₀`, and the memory after is related to its final arena state by
`ArenaD` and to its final parse state by `StateDR`. -/

@[refines ConRon.Arena.Frontend.parseBytes]
theorem frontRun_refines (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data)
    (_hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63) (a₀ : AState) (hA : ArenaD s₀.mem a₀)
    (hD : StateDR s₀.mem StateD.blank) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem st'; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun h0
  have hW := M.of_run (P := fun s => s = s₀) hs hrun
    (frontRun_specI p (lineKW p b.data) b.data (fun m => ∃ a st, FrontInv b m a st)
      (fun n s₁ i hm hI hi => frontLineK_spec p hS hL hpf hps hpn hpu hpl hpr hpt hE hpy hF hDL hpz b.data
        hsize _ (fun m ⟨_, _, hI⟩ => ⟨hI.2.1.1.lit.1.2.2.1, hI.2.1.1.lit.1.2.2.2.1⟩)
        (inv_step p (FrontInv b) b h64 hsize
          (fun m m' i ok nx st a hI hi h hok => lineKW_step b h64 hsize p hFI hAI hII hXI m m' i ok nx
            st a hI hi h hok)) n s₁ i hm hI hi)
      initKW s₀.mem (fun n s₁ hs₁ => initK_inv p hL hE hpi (FrontInv b) _ (initKW_inv b)
        s₀ a₀ ⟨hm, hA, hD, hok, hoff, hpins, hmode⟩ n s₁ hs₁)
      hpd n s₀ hm rfl)
  rw [h0] at hW
  obtain ⟨st', a', h1, -, h2, h3, -⟩ :=
    frontRunW_refines b h64 hsize p hFI hAI hII hXI s₀.mem s'.mem a₀ hm hA hD hok hoff hpins hmode hW
  exact ⟨st', a', h1, h2, h3⟩

end run

/-! ## The whole program -/

/-- Every function of the frontend: the validator, the fields passes, the stores, the apply
steps, the line and the driver. -/
def frontAllProg : Prog := L.Scan.Validator.valProg ++
  [("rec_nat_list", recNatList), ("rec_str_name", recStrName),
   ("rec_num_name", recNumName), ("rec_line_loop", recLineLoop), ("obj_val", objVal),
   ("rec_obj", recObj), ("expr_val", exprVal), ("rec_expr_loop", recExprLoop)] ++
  exprProg.filter (fun f => f.1 != "skip_digits" && f.1 != "num_end" && f.1 != "byte_in" &&
    f.1 != "hex_val" && f.1 != "hex4" && f.1 != "hex3") ++
  [("front_line", frontLine), ("apply_rec", applyRec), ("apply_str", applyStr),
   ("apply_any", applyAny), ("front_run", frontRun),
   ("match_dlit", matchDlit), ("str_code", strCode), ("hints_val", hintsVal),
   ("d_member", dMember), ("decl_val", declVal), ("decl_code", declCodeF),
   ("rec_decl_obj", recDeclObj), ("rec_decl_line", recDeclLine),
   ("lp_put", lpPut), ("decl_kind", declKind), ("decl_push", declPush), ("decl_cv", declCv),
   ("apply_decl", applyDecl), ("apply_dline", applyDLine)] ++
  L.Front.Ind.indFieldsFns ++ L.Front.Ind.indApplyFns ++ L.Arena.levelProg ++ [("e_view", L.Ind.eView)]

set_option maxRecDepth 100000

theorem frontAllProg_noSt8 : frontAllProg.noSt8 = true := by decide +kernel

theorem frontAllProg_scan : ScanLookups frontAllProg := by
  unfold ScanLookups scanLookupsFns; repeat (first | exact ProgHas.nil | refine ProgHas.cons rfl ?_)

theorem frontAllProg_front : FrontLookups frontAllProg := by constructor <;> rfl

theorem frontAllProg_expr : ExprLookups frontAllProg := by
  refine ⟨frontAllProg_front, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    frontAllProg_noSt8⟩ <;> rfl

theorem frontAllProg_dfields : DeclFieldLookups frontAllProg := by
  unfold DeclFieldLookups declFieldLookupsFns; repeat (first | exact ProgHas.nil | refine ProgHas.cons rfl ?_)

theorem frontAllProg_decl : DeclLookups frontAllProg :=
  ⟨frontAllProg_expr, rfl, rfl, rfl, rfl, rfl⟩

theorem frontAllProg_indFields : L.Front.Ind.IndFieldLookups frontAllProg := by
  constructor <;> first | rfl | exact frontAllProg_noSt8

theorem frontAllProg_indApply : L.Front.Ind.IndApplyLookups frontAllProg := by
  constructor
  · exact frontAllProg_decl
  · constructor <;> rfl
  all_goals rfl

theorem frontAllProg_indInstall : L.Front.Ind.IndInstallLookups frontAllProg := by
  constructor <;> rfl

theorem frontAllProg_indLine : L.Front.Ind.IndLineLookups frontAllProg := by
  constructor <;> rfl

/-- **Bytes → stores, for the whole program.** -/
theorem frontAll_refines (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data)
    (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63) (a₀ : AState) (hA : ArenaD s₀.mem a₀)
    (hD : StateDR s₀.mem StateD.blank) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke frontAllProg (exec frontAllProg n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem st'; ⊤⦄ :=
  frontRun_refines frontAllProg frontAllProg_scan frontAllProg_front rfl rfl rfl rfl rfl rfl rfl
    frontAllProg_expr rfl frontAllProg_dfields frontAllProg_decl rfl rfl rfl frontAllProg_indFields
    frontAllProg_indApply frontAllProg_indInstall frontAllProg_indLine b h64 hsize n s₀ hm hpool a₀ hA hD
    hok hoff hpins hmode

/-- A memory with 224 word arrays of 4096 words and the input `s` (the inductive lines' scratch
arrays `IFR`/`IFL` are 70, 71, the level heap 192). -/
def frontMemOf (s : String) : Mem := { initMem (List.replicate 224 4096) with bytes := #[s.toUTF8.data] }

/- A header, a name, a level, and expression lines of six kinds (a 30-digit literal among them):
accepted. -/
#guard (run frontAllProg 100000 "front_run" [] (frontMemOf
  "{\"meta\":{\"x\":1}}\n{\"in\":1,\"str\":{\"pre\":0,\"str\":\"N\\u00e4t\\n\"}}\n{\"il\":1,\"succ\":0}\n\
  {\"ie\":0,\"sort\":1}\n{\"ie\":1,\"const\":{\"name\":1,\"us\":[0,1]}}\n\
  {\"ie\":2,\"app\":{\"fn\":1,\"arg\":0}}\n{\"ie\":3,\"natVal\":\"123456789012345678901234567890\"}\n\
  {\"ie\":4,\"lam\":{\"binderInfo\":\"default\",\"body\":0,\"name\":1,\"type\":2}}\n\
  {\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n\
  {\"def\":{\"hints\":{\"regular\":3},\"levelParams\":[1],\"name\":1,\"safety\":\"safe\",\"type\":0,\"value\":2}}")).toOption.map
  (·.1) == some [0]
/- A line that does not scan: its number. An unbound id: the run aborts. -/
#guard (run frontAllProg 100000 "front_run" [] (frontMemOf
  "{\"il\":1,\"succ\":0}\n{\"il\":2,\"succ\":}\n")).toOption.map (·.1) == some [2]
#guard (run frontAllProg 100000 "front_run" [] (frontMemOf
  "{\"ie\":0,\"sort\":5}\n")).toOption.isNone

end L.Front
