module

public import ConAgua.Arena.DefEqStuckIrrel
import ConAgua.Arena.DefEqStuckEta
import ConAgua.Arena.IndView
import ConAgua.Arena.RefWalk

@[expose] public section

/-!
# `stuck_str` refines `defeqStuck`'s string-literal arms (lane `defeq`, helper `defeq-top`)

A string literal against an application headed by `String.ofList` at the empty levels:
`strLitToConstructor`, then the knot's `defeq`; every other case `stuckIrrel` (`stuckStrT`). The model `strE` is in
`DefEqModels.lean`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin's arms -/

/-- **`defeqStuck`'s string-literal arm**, `side` `false` for the literal on the left. -/
def stuckStrT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) (side : Bool)
    (l : ConLeche.Literal) (fo : EIdx) : AM Bool :=
  match l with
  | .strVal st =>
    if fo.tag == ETag.const then
      view fo >>= fun v => match v with
        | .const cO usO => do
          let el ← emptyLevels
          let sl ← pinStringOfList
          if cO = sl ∧ usO = el ∧ (← strLitStored fe) then do
            let c ← strLitToConstructor st
            if side then r.defeq depth a c else r.defeq depth c b
          else stuckIrrel r fe depth a b
        | _ => stuckIrrel r fe depth a b
    else stuckIrrel r fe depth a b
  | _ => stuckIrrel r fe depth a b

/-- The arm past the head's view and the pins. -/
theorem stuckStrT_run (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) (side : Bool)
    (st : String) (fo : EIdx) (s : AState) (m : Mem) (hP : PinsFull m s.pins) (cO : NIdx) (usO : LsIdx)
    (ht : (fo.tag == ETag.const) = true) (hv : s.store.view fo = some (.const cO usO)) :
    (stuckStrT r fe depth a b side (.strVal st) fo).run s =
      (strLitStored fe >>= fun x =>
        if cO = decI (pinW m (1 + 6)) ∧ usO = decI (pinW m 52) ∧ x = true then do
          let c ← strLitToConstructor st
          if side then r.defeq depth a c else r.defeq depth c b
        else stuckIrrel r fe depth a b).run s := by
  simp only [stuckStrT, ht, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind,
    emptyLevels, pinEmptyLevels_run hP, pinStringOfList, PIN_STRING_OF_LIST, pinAt_run hP 6 (by decide)]

/-- A `stuck_irrel` tail, both outcomes (`si_ref`, its answer re-listed). -/
theorem si_tail {p : Prog} (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    {K : Except Err (List Word × Mem) → Except Err (List Word × Mem)}
    (hK1 : ∀ e, K (.error e) = .error e)
    (hK2 : ∀ v : List Word × Mem, K (.ok v) = .ok ([v.1.headD 0], v.2))
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (m : Mem) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hS : CoreS dn m a₀ vis fe M eb) (hmode : mode < 4) (heb : eb = (mode >>> 1) &&& 1)
    (ha : HW a) (hb : HW b) :
    RefE (StuckG p n) (K (siE p n m mode vis d a b))
      (stuckIrrel (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn m vis fe M eb ResH) := by
  cases n with
  | zero => rw [show siE p 0 m mode vis d a b = .error .outOfFuel from rfl, hK1]; exact RefE.of_cls0 rfl
  | succ k =>
  exact RefE.tail_relist1 hK1 hK2 (fun hG => hG.mono (by omega))
    (si_ref p hq hi hc k (hk.mono (by omega)) F ⟨m, Locals.init []⟩ a₀ dn vis fe M eb mode d a b
      (by omega) (by omega) ⟨hS, hmode, heb⟩ ha hb)

/-- **`stuck_str` refines `stuckStrT`, both outcomes** (`lt` a literal handle, `side` the
literal's side): the errors are the `defeq` slot's and `stuck_irrel`'s. -/
theorem str_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b side lt fo : Word) (l : ConLeche.Literal) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hlt : HW lt) (hfo : HW fo)
    (hg : tagW lt = 8) (hl : a₀.store.view (decE lt) = some (.lit l)) :
    RefE (StuckG p n) (strE p (n + 1) s₀.mem mode vis d a b side lt fo)
      (stuckStrT (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b) (side != 0) l
        (decE fo)) a₀ (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  sorry

/-- **`stuck_str` refines `stuckStrT`** at the knot (`str_ref`'s ok half). -/
@[refines_part ConRon.Arena.defeqStuck "the string-literal arms (stuckStrT)"]
theorem stuckStr_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b side lt fo : Word) (l : ConLeche.Literal) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hlt : HW lt) (hfo : HW fo)
    (hg : tagW lt = 8) (hl : a₀.store.view (decE lt) = some (.lit l)) :
    CoreSpec p (n + 1) "stuck_str" [mode, vis, d, a, b, side, lt, fo]
      (stuckStrT (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b) (side != 0) l
        (decE fo)) decBool s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (strE_spec p hq.stuckStr hq.stuckIrrel hq.setCert hq.setWith hq.setWtb hq.setGo
    hq.setTail hq.sunit hq.suHead hq.suTail (n + 1) s₀ mode vis d a b side lt fo)
    (str_ref p hq hi hc n hk F s₀ a₀ dn vis fe M eb mode d a b side lt fo l hF hn hs ha hb hlt hfo hg hl)

end L.Arena
