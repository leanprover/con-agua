import ConAgua.Checker.RomProgB

/-!
# The ROM stages of `check` for the checker's program (lane `pipeline`)

The program hypotheses of `pbCheck_PB`, `internReservedPins_PB`, `internAllPins_PB`
(`Rom/Stage.lean`) for `checkerProg`: no store to `PB` (`checkerProg_noSt8PB`, `RomProg0.lean`),
`pb_check`'s binding, and the substituted program's readers (`checkerProg_irp`,
`checkerProg_pinProg`, `RomProgA.lean`, `RomProgB.lean`); the three stages at `checkerProg`.
The loaded memory's initial facts are in `RomProgInit.lean`, `cap_check`'s spec in
`CapCheck.lean`.
-/

namespace L.Checker

open ConRon.Arena
open L L.Rom L.Arena
open Std.WP
open scoped Lean.Order

set_option maxRecDepth 100000 in
theorem checkerProg_pbCheck : checkerProg.lookup "pb_check" = some pbCheck := rfl

set_option maxRecDepth 100000 in
theorem checkerProg_capCheck : checkerProg.lookup "cap_check" = some capCheckL := rfl

/-- `pb_check` at `checkerProg`. -/
theorem checkerProg_pbCheck_PB (bs : List UInt8) (hr : RomOK bs) (n : Nat) (s₀ : St)
    (hbs : s₀.mem.arr8 PB = bs.toArray) :
    ⦃fun s => s = s₀⦄
    invoke checkerProg (exec checkerProg n) "pb_check" []
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ bs = romData ++ bs.drop romData.length; ⊤⦄ :=
  pbCheck_PB checkerProg checkerProg_noSt8PB checkerProg_pbCheck bs hr n s₀ hbs

/-- `intern_reserved_pins` at `checkerProg`. -/
theorem checkerProg_internReservedPins_PB (bs : List UInt8) (hr : RomOK bs)
    (hpre : bs = romData ++ bs.drop romData.length)
    (n : Nat) (s₀ : St) (a₀ : AState) (hbs : s₀.mem.arr8 PB = bs.toArray) (hA : ArenaD s₀.mem a₀)
    (hmo : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke checkerProg (exec checkerProg n) "intern_reserved_pins" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok ConRon.Arena.internReservedPins a₀ ∧
      ArenaD s'.mem (AM.st ConRon.Arena.internReservedPins a₀) ∧
      PinsFull s'.mem (AM.st ConRon.Arena.internReservedPins a₀).pins ∧
      pinW s'.mem 0 ≠ 0 ∧ MemFrame PinA StoreC s₀.mem s'.mem ∧ ModeOK s'.mem; ⊤⦄ :=
  internReservedPins_PB checkerProg checkerProg_noSt8PB bs (checkerProg_irp bs) hr hpre n s₀ a₀ hbs hA hmo

/-- `intern_all_pins` at `checkerProg`. -/
theorem checkerProg_internAllPins_PB (bs : List UInt8) (hr : RomOK bs)
    (hpre : bs = romData ++ bs.drop romData.length)
    (n : Nat) (s₀ : St) (a₀ : AState) (hbs : s₀.mem.arr8 PB = bs.toArray) (hA : ArenaD s₀.mem a₀)
    (hmo : ModeOK s₀.mem) (hP : PinsReadyP a₀) (hok : ConRon.Bridge.StateOK a₀) (hpins : ConRon.Bridge.PinsOK a₀)
    (hpp : ConRon.Bridge.PersPins a₀) (hoff : a₀.store.scratchOn = false) (hR : RsetR s₀.mem)
    (hst : (stkTop s₀.mem).toNat < 2 ^ 61) (hc : 151 < (s₀.mem.arr64 CTL).size) :
    ⦃fun s => s = s₀⦄
    invoke checkerProg (exec checkerProg n) "intern_all_pins" []
    ⦃fun _ s' => LocEq s' s₀ ∧ ∃ (pins : List ConLeche.NatOpPinSet) (ips : List INatOpPinSet) (a' : AState),
      (ConRon.Arena.internAllPins pins).run a₀ = .ok (ips, a') ∧ ArenaD s'.mem a' ∧ PinSetsR s'.mem ips ∧
      ConRon.Bridge.StateOK a' ∧ RsetR s'.mem ∧ erecTop s'.mem ≤ (s'.mem.arr64 EREC).size ∧ ModeOK s'.mem; ⊤⦄ :=
  internAllPins_PB checkerProg checkerProg_noSt8PB bs (checkerProg_pinProg bs) hr hpre n s₀ a₀ hbs hA hmo
    hP hok hpins hpp hoff hR hst hc

end L.Checker
