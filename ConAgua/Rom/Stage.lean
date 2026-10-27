import ConAgua.Rom.PinSets
import ConRon.Bridge.Checker.Pins
import ConAgua.Arena.RomPins

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Rom

theorem internAllPins_split (pins : List ConLeche.NatOpPinSet) :
    internAllPins pins = internAllPins [] >>= fun _ => internPinSets pins := by
  simp only [internAllPins, internPinSets, bind_assoc, pure_bind]

open L.Arena

/-- **`intern_all_pins` over a buffer that starts with `romData`, up to the variant list**: the
startup items are the twin's `internAllPins []`, and the variant list starts right after
`romData`. -/
theorem internAllPinsW_fixed (rom : List UInt8) (hr : RomOK rom) (rest : List UInt8)
    (hrom : rom = romData ++ rest) (n : Nat) (mem mem' : Mem) (a : AState) (hA : ArenaD mem a)
    (hmo : ModeOK mem)
    (hP : PinsReadyP a) (hst : (stkTop mem).toNat < 2 ^ 61) (hc : 132 < (mem.arr64 CTL).size)
    (hW : internAllPinsW rom n mem = some mem') :
    ∃ (n' : Nat) (m₁ : Mem) (a₁ : AState) (v : List INatOpPinSet) (q' : Word),
      (internAllPins []).run a = .ok (v, a₁) ∧ ArenaD m₁ a₁ ∧ (RsetR mem → RsetR m₁) ∧
      stkTop m₁ = stkTop mem ∧ MemFrame ExprA ExprC mem m₁ ∧
      internPinSetsW rom n' m₁ (UInt64.ofNat romData.length) = some (q', mem') ∧ ModeOK m₁ := by
  cases n with
  | zero => simp [internAllPinsW] at hW
  | succ n =>
  simp only [internAllPinsW] at hW
  split at hW
  case isFalse => cases hW
  rename_i hcl
  rcases hI : romItemsW rom n (resetMem mem) allPinsOff with _ | ⟨q, m₁⟩ <;> rw [hI] at hW
  · simp [iapK] at hW
  simp only [iapK] at hW
  rcases hS : internPinSetsW rom n m₁ q with _ | ⟨q', m₂⟩ <;> rw [hS] at hW
  · simp [iap2K] at hW
  simp only [iap2K, Option.some.injEq] at hW
  subst hW
  have hd : rom.drop allPinsOff.toNat = encItems [] (itemsAllPins []) ++ rest := by
    rw [hrom, allPinsOff_toNat, romData_split, romPins,
      List.append_assoc (encNames pinNames ++ encNames reservedBasisNameValues ++ romCIData), List.drop_left]
  have hA' : ArenaD (resetMem mem) a := ArenaD.frameHi (resetMem_frame1 _) (by simp) (by simp) hA
  obtain ⟨m', a', -, hrunI, hR, -, hq, hf, hs, hz⟩ := romItemsW_ok rom hr _ allPins_fits n (resetMem mem) a
    allPinsOff rest [] ∅ q m₁ hA' ((memFrame_top (resetMem_frame1 mem) (by decide)).mode hA.1.lit.1 hmo)
    (MemoR.fresh mem hc) hd (by rw [resetMem_stk]; exact hst)
    (by rw [(resetMem_frame1 _).2.2.1]; omega) hI
  obtain ⟨v, hv⟩ := simZ_internAllPins [] ∅ a m' a' hP (by rw [runItems_reset]; exact hrunI)
  have hqd : q = UInt64.ofNat romData.length := by
    have hl := romData_len
    apply UInt64.toNat_inj.mp
    rw [hq, allPinsOff_toNat, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    simp [romData, romPins]; omega
  subst hqd
  exact ⟨n, m₁, a', v, q', hv, hR, fun h0 => hz (h0.reset hcl), by rw [hs, resetMem_stk],
    (resetMem_frame mem).trans hf, hS,
    ((memFrame_top (resetMem_frame1 mem) (by decide)).trans (romItemsW_topK rom _ _ _ _ _ hI)).mode hA.1.lit.1 hmo⟩

/-! ## The program over `PB` -/

/-- **`pb_check` over the pin-data buffer**: on a run that returns, the buffer `bs` (byte array
`PB`) starts with `romData`. -/
theorem pbCheck_PB (P : Prog) (hno : Prog.noSt8PB P = true) (hp : P.lookup "pb_check" = some pbCheck)
    (bs : List UInt8) (hr : RomOK bs) (n : Nat) (s₀ : St) (hbs : s₀.mem.arr8 PB = bs.toArray) :
    ⦃fun s => s = s₀⦄
    invoke P (exec P n) "pb_check" []
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ bs = romData ++ bs.drop romData.length; ⊤⦄ := by
  refine triple_subPB (bs := bs) hno (fun s hs => hs ▸ hbs) ?_
  have hp' : (Prog.subPB bs P).lookup "pb_check" = some (pbCheck.subPB bs) := by
    rw [lookup_subPB, hp]; rfl
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hm, -, -, hpre⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (pbCheck_specW (Prog.subPB bs P) bs hr hp' n s₀)
  exact ⟨hloc, hm, hpre⟩

def _root_.L.BSrc.noPB : L.BSrc → Bool
  | .arr a => a != PB
  | .rom _ => true

/-- A function that reads no pin data is its own substitution. -/
def _root_.L.Expr.noPB : L.Expr → Bool
  | .bin _ a b | .cmpw _ a b => a.noPB && b.noPB
  | .ld8 a i => a != PB && i.noPB
  | .ld64 _ i | .ldc _ i => i.noPB
  | .len8 a => a != PB
  | .ld64t _ t i => t.noPB && i.noPB
  | .len64t _ t => t.noPB
  | .ld8x8 b i => b.noPB && i.noPB
  | _ => true

def _root_.L.WArr.noPB : L.WArr → Bool
  | .plain _ => true
  | .tier _ t => t.noPB

def _root_.L.Cond.noPB : L.Cond → Bool
  | .cmp _ a b => a.noPB && b.noPB
  | .and p q | .or p q => p.noPB && q.noPB
  | .not p => p.noPB

def _root_.L.Stmt.noPB : L.Stmt → Bool
  | .set _ e => e.noPB
  | .st8 _ i e | .st64 _ i e => i.noPB && e.noPB
  | .seq s t => s.noPB && t.noPB
  | .ite c s t => c.noPB && s.noPB && t.noPB
  | .while c s => c.noPB && s.noPB
  | .ret es | .call _ _ es => es.all L.Expr.noPB
  | .gset _ e => e.noPB
  | .st64t _ t i e => t.noPB && i.noPB && e.noPB
  | .copy64 d di s si n => d.noPB && di.noPB && s.noPB && si.noPB && n.noPB
  | .copy8w d di s si n => d.noPB && di.noPB && s.noPB && si.noPB && n.noPB
  | .scan8 _ s i e _ => s.noPB && i.noPB && e.noPB
  | .abort e => e.noPB
  | _ => true

theorem _root_.L.BSrc.subPB_noPB (bs : List UInt8) : ∀ b : L.BSrc, b.noPB = true → b.subPB bs = b := by
  intro b; cases b <;> simp_all [L.BSrc.noPB, L.BSrc.subPB]

theorem _root_.L.Expr.subPB_noPB (bs : List UInt8) : ∀ e : L.Expr, e.noPB = true → e.subPB bs = e := by
  intro e; induction e <;> simp_all [L.Expr.noPB, L.Expr.subPB, L.BSrc.subPB_noPB]

theorem _root_.L.WArr.subPB_noPB (bs : List UInt8) : ∀ w : L.WArr, w.noPB = true → w.subPB bs = w := by
  intro w; cases w <;> simp_all [L.WArr.noPB, L.WArr.subPB, L.Expr.subPB_noPB]

theorem _root_.L.Cond.subPB_noPB (bs : List UInt8) : ∀ c : L.Cond, c.noPB = true → c.subPB bs = c := by
  intro c; induction c <;> simp_all [L.Cond.noPB, L.Cond.subPB, L.Expr.subPB_noPB]

theorem _root_.L.Stmt.subPB_noPB (bs : List UInt8) : ∀ s : L.Stmt, s.noPB = true → s.subPB bs = s := by
  have hl : ∀ es : List L.Expr, (∀ x ∈ es, x.noPB = true) → es.map (L.Expr.subPB bs) = es := fun es h => by
    conv => rhs; rw [← List.map_id es]
    exact List.map_congr_left (fun x hx => L.Expr.subPB_noPB bs x (h x hx))
  intro s; induction s <;> simp_all [L.Stmt.noPB, L.Stmt.subPB, L.Cond.subPB_noPB, L.Expr.subPB_noPB,
    L.WArr.subPB_noPB, L.BSrc.subPB_noPB, List.all_eq_true]

/-- A function of the program that reads no pin data is unchanged by the substitution. -/
theorem lookup_subPB_noPB (bs : List UInt8) {P : Prog} {f : FnName} {fd : FunDecl}
    (h : P.lookup f = some fd) (hn : fd.body.noPB = true) : (Prog.subPB bs P).lookup f = some fd := by
  rw [lookup_subPB, h]
  simp only [Option.map_some, FunDecl.subPB, L.Stmt.subPB_noPB bs _ hn]

/-- **`intern_reserved_pins` over the pin-data buffer refines `internReservedPins`**, for a buffer
that starts with `romData` (`pb_check`) and a program whose substituted readers are the ROM
readers at the buffer (`IrpProg bs 0 (P.subPB bs)`: the readers are `toPB` of the ROM readers,
`romName_subPB`, …; every other function reads no pin data, `lookup_subPB_noPB`). -/
theorem internReservedPins_PB (P : Prog) (hno : Prog.noSt8PB P = true) (bs : List UInt8)
    (hL : IrpProg bs 0 (Prog.subPB bs P)) (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length)
    (n : Nat) (s₀ : St) (a₀ : AState) (hbs : s₀.mem.arr8 PB = bs.toArray) (hA : ArenaD s₀.mem a₀)
    (hmo : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke P (exec P n) "intern_reserved_pins" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok internReservedPins a₀ ∧
      ArenaD s'.mem (AM.st internReservedPins a₀) ∧ PinsFull s'.mem (AM.st internReservedPins a₀).pins ∧
      pinW s'.mem 0 ≠ 0 ∧ MemFrame PinA StoreC s₀.mem s'.mem ∧ ModeOK s'.mem; ⊤⦄ := by
  refine triple_subPB (bs := bs) hno (fun s hs => hs ▸ hbs) ?_
  refine internReservedPins_refines bs 0 (Prog.subPB bs P) hL hr
    (romCIData ++ (encItems [] (itemsAllPins romPins) ++ bs.drop romData.length)) ?_ pinNames_fit.1 pinNames_fit.2 n s₀ a₀ hA hmo
  conv => lhs; rw [hpre]
  simp [romData]

/-- **`RsetR` at the start**: on all-zero word arrays (the loaded memory) with room for its `CTL`
words. It survives every stage before `intern_all_pins` that leaves `RSET`, `RMEMO`, `CTL[132]`,
`CTL[148]` alone (`RsetR.frame`). -/
theorem RsetR_zero (m : Mem) (hz : ∀ b x, rdW (m.arr64 b) x = 0) (hctl : 150 ≤ (m.arr64 CTL).size) :
    RsetR m := by
  refine ⟨∅, memoRG_zero rsetSch bmKey (fun _ => ()) m hz (by simp [rsetSch]; omega), fun k hk => ?_⟩
  simp [memoCnt, hz] at hk

open ConRon.Bridge ConRon.Bridge.Frontend in
/-- **`intern_all_pins`'s model, in the decoder direction**: on a buffer that starts with
`romData`, a run that returns is the twin's `internAllPins P` for the pin list `P` the buffer's
variant list decodes to, and the 40-word records hold the interned variants (`PinSetsR`). -/
theorem internAllPinsW_dec (rom : List UInt8) (hr : RomOK rom) (rest : List UInt8)
    (hrom : rom = romData ++ rest) (n : Nat) (mem mem' : Mem) (a : AState) (hA : ArenaD mem a)
    (hmo : ModeOK mem) (hP : PinsReadyP a) (hok : StateOK a) (hpins : PinsOK a) (hpp : PersPins a)
    (hoff : a.store.scratchOn = false) (hR : RsetR mem) (hst : (stkTop mem).toNat < 2 ^ 61)
    (hc : 151 < (mem.arr64 CTL).size) (hW : internAllPinsW rom n mem = some mem') :
    ∃ (pins : List ConLeche.NatOpPinSet) (ips : List INatOpPinSet) (a' : AState),
      (internAllPins pins).run a = .ok (ips, a') ∧ ArenaD mem' a' ∧ PinSetsR mem' ips ∧
      StateOK a' ∧ RsetR mem' ∧ erecTop mem' ≤ (mem'.arr64 EREC).size ∧ ModeOK mem' := by
  obtain ⟨n', m₁, a₁, v, q', hv, hA1, hz, hs, hf, hS, hmo1⟩ :=
    internAllPinsW_fixed rom hr rest hrom n mem mem' a hA hmo hP hst (by omega) hW
  obtain ⟨hok1, -⟩ := internAllPins_run hok hpins hpp hoff hv
  obtain ⟨pins, ips, a', hrun, hA', hPS, hok', hR', -, -, -, htop, hmo'⟩ := internPinSetsW_dec rom hr n' m₁ a₁ _ q' mem' hA1
    hmo1 (hz hR) hok1 (by rw [hs]; exact hst) (by rw [hf.2.2.1]; exact hc) hS
  refine ⟨pins, ips, a', ?_, hA', hPS, hok', hR', htop, hmo'⟩
  rw [internAllPins_split, run_bind_of _ _ _ _ _ hv]; exact hrun

/-- **`intern_all_pins` over the pin-data buffer refines `internAllPins P`**, `P` the pin list the
buffer decodes to (any buffer that starts with `romData`, `pb_check`); the variant records hold
`P` interned (`PinSetsR`). The program's substituted functions must be the ROM version's
(`PinProg bs (P.subPB bs)`).

A full refinement in the decoder direction: the pin list is the twin's input, the buffer is L's,
and `TwinAccepts` takes the pin list existentially, so every L run that returns is a twin run at
the decoded list. The startup half (`internAllPins []`) is the ROM's fixed data. What the buffer cannot spell (string literals, `natVal ≥ 2^64`: D6) is a
completeness gap of the format, as `read_nat`'s 18 digits are for `parseChunks` (D2). Through it
the ROM interns it alone reaches (`internPinSet(s)`, `internExpr`, `internExprList`, and below
`BasisKind.decls`/`declsA` the `Frontend.internCI` family) count as covered. -/
@[refines ConRon.Arena.internAllPins]
theorem internAllPins_PB (P : Prog) (hno : Prog.noSt8PB P = true) (bs : List UInt8)
    (hL : PinProg bs (Prog.subPB bs P)) (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length)
    (n : Nat) (s₀ : St) (a₀ : AState) (hbs : s₀.mem.arr8 PB = bs.toArray) (hA : ArenaD s₀.mem a₀)
    (hmo : ModeOK s₀.mem) (hP : PinsReadyP a₀) (hok : ConRon.Bridge.StateOK a₀) (hpins : ConRon.Bridge.PinsOK a₀)
    (hpp : ConRon.Bridge.PersPins a₀) (hoff : a₀.store.scratchOn = false) (hR : RsetR s₀.mem)
    (hst : (stkTop s₀.mem).toNat < 2 ^ 61) (hc : 151 < (s₀.mem.arr64 CTL).size) :
    ⦃fun s => s = s₀⦄
    invoke P (exec P n) "intern_all_pins" []
    ⦃fun _ s' => LocEq s' s₀ ∧ ∃ (pins : List ConLeche.NatOpPinSet) (ips : List INatOpPinSet) (a' : AState),
      (internAllPins pins).run a₀ = .ok (ips, a') ∧ ArenaD s'.mem a' ∧ PinSetsR s'.mem ips ∧
      ConRon.Bridge.StateOK a' ∧ RsetR s'.mem ∧ erecTop s'.mem ≤ (s'.mem.arr64 EREC).size ∧ ModeOK s'.mem; ⊤⦄ := by
  refine triple_subPB (bs := bs) hno (fun s hs => hs ▸ hbs) ?_
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (internAllPinsPB_specW bs (Prog.subPB bs P) hL n s₀ ⟨hA.1.lit.1.2.2.1, hA.1.lit.1.top41⟩)
  subst hs
  exact ⟨hloc, internAllPinsW_dec bs hr _ hpre n _ _ a₀ hA hmo hP hok hpins hpp hoff hR hst hc hW⟩

end L.Rom
