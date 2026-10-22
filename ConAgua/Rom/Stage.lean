import ConAgua.Rom.PinReadSpec
import ConAgua.Rom.DecExpr

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
    (hP : PinsReadyP a) (hst : (stkTop mem).toNat < 2 ^ 61) (hc : 132 < (mem.arr64 CTL).size)
    (hW : internAllPinsW rom n mem = some mem') :
    ∃ (n' : Nat) (m₁ : Mem) (a₁ : AState) (v : List INatOpPinSet) (q' : Word),
      (internAllPins []).run a = .ok (v, a₁) ∧ ArenaD m₁ a₁ ∧ (RsetR mem → RsetR m₁) ∧
      stkTop m₁ = stkTop mem ∧ MemFrame ExprA ExprC mem m₁ ∧
      internPinSetsW rom n' m₁ (UInt64.ofNat romData.length) = some (q', mem') := by
  cases n with
  | zero => simp [internAllPinsW] at hW
  | succ n =>
  simp only [internAllPinsW] at hW
  split at hW
  case isFalse => cases hW
  rename_i hcl
  cases hI : romItemsW rom n (resetMem mem) allPinsOff with
  | none => rw [hI] at hW; simp [iapK] at hW
  | some r =>
  obtain ⟨q, m₁⟩ := r
  rw [hI] at hW
  simp only [iapK] at hW
  cases hS : internPinSetsW rom n m₁ q with
  | none => rw [hS] at hW; simp [iap2K] at hW
  | some r =>
  obtain ⟨q', m₂⟩ := r
  rw [hS] at hW
  simp only [iap2K, Option.some.injEq] at hW
  subst hW
  have hd : rom.drop allPinsOff.toNat = encItems [] (itemsAllPins []) ++ rest := by
    rw [hrom, allPinsOff_toNat, romData, romPins, ← List.append_assoc, List.append_assoc,
      List.drop_left]
  have hA' : ArenaD (resetMem mem) a := ArenaD.frameHi (resetMem_frame1 _) (by simp) (by simp) hA
  obtain ⟨m', a', -, hrunI, hR, -, hq, hf, hs, hz⟩ := romItemsW_ok rom hr _ allPins_fits n (resetMem mem) a
    allPinsOff rest [] ∅ q m₁ hA' (MemoR.fresh mem hc) hd (by rw [resetMem_stk]; exact hst)
    (by rw [(resetMem_frame1 _).2.2.1]; omega) hI
  obtain ⟨v, hv⟩ := simZ_internAllPins [] allPins_noProj ∅ a m' a' hP (by rw [runItems_reset]; exact hrunI)
  have hqd : q = UInt64.ofNat romData.length := by
    have hl := romData_len
    apply UInt64.toNat_inj.mp
    rw [hq, allPinsOff_toNat, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    simp [romData, romPins]; omega
  subst hqd
  exact ⟨n, m₁, a', v, q', hv, hR, fun h0 => hz (h0.reset hcl), by rw [hs, resetMem_stk],
    (resetMem_frame mem).trans hf, hS⟩

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

/-- A function that reads no pin data is its own substitution. -/
def _root_.L.Expr.noPB : L.Expr → Bool
  | .bin _ a b | .cmpw _ a b => a.noPB && b.noPB
  | .ld8 a i => a != PB && i.noPB
  | .ld64 _ i | .ldc _ i => i.noPB
  | .len8 a => a != PB
  | _ => true

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
  | _ => true

theorem _root_.L.Expr.subPB_noPB (bs : List UInt8) : ∀ e : L.Expr, e.noPB = true → e.subPB bs = e := by
  intro e; induction e <;> simp_all [L.Expr.noPB, L.Expr.subPB]

theorem _root_.L.Cond.subPB_noPB (bs : List UInt8) : ∀ c : L.Cond, c.noPB = true → c.subPB bs = c := by
  intro c; induction c <;> simp_all [L.Cond.noPB, L.Cond.subPB, L.Expr.subPB_noPB]

theorem _root_.L.Stmt.subPB_noPB (bs : List UInt8) : ∀ s : L.Stmt, s.noPB = true → s.subPB bs = s := by
  have hl : ∀ es : List L.Expr, (∀ x ∈ es, x.noPB = true) → es.map (L.Expr.subPB bs) = es := fun es h => by
    conv => rhs; rw [← List.map_id es]
    exact List.map_congr_left (fun x hx => L.Expr.subPB_noPB bs x (h x hx))
  intro s; induction s <;> simp_all [L.Stmt.noPB, L.Stmt.subPB, L.Cond.subPB_noPB, L.Expr.subPB_noPB,
    List.all_eq_true]

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
    (n : Nat) (s₀ : St) (a₀ : AState) (hbs : s₀.mem.arr8 PB = bs.toArray) (hA : ArenaD s₀.mem a₀) :
    ⦃fun s => s = s₀⦄
    invoke P (exec P n) "intern_reserved_pins" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok internReservedPins a₀ ∧
      ArenaD s'.mem (AM.st internReservedPins a₀) ∧ PinsFull s'.mem (AM.st internReservedPins a₀).pins ∧
      pinW s'.mem 0 ≠ 0 ∧ MemFrame PinA StoreC s₀.mem s'.mem; ⊤⦄ := by
  refine triple_subPB (bs := bs) hno (fun s hs => hs ▸ hbs) ?_
  refine internReservedPins_refines bs 0 (Prog.subPB bs P) hL hr
    (encItems [] (itemsAllPins romPins) ++ bs.drop romData.length) ?_ pinNames_fit.1 pinNames_fit.2 n s₀ a₀ hA
  conv => lhs; rw [hpre]
  simp [romData]

/-- **`RsetR` at the start**: on all-zero word arrays (the loaded memory) with room for its `CTL`
words. It survives every stage before `intern_all_pins` that leaves `RSET`, `RMEMO`, `CTL[132]`,
`CTL[148]` alone (`RsetR.frame`). -/
theorem RsetR_zero (m : Mem) (hz : ∀ b x, rdW (m.arr64 b) x = 0) (hctl : 150 ≤ (m.arr64 CTL).size) :
    RsetR m := by
  refine ⟨∅, memoRG_zero rsetSch bmKey (fun _ => ()) m hz (by simp [rsetSch]; omega), fun k hk => ?_⟩
  simp [memoCnt, hz] at hk

end L.Rom
