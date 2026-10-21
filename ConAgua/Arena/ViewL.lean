module

public import ConAgua.Arena.Store

@[expose] public section

/-!
# The L side of the expression view: handle words and branch-free arithmetic

What every expression walk's L code shares: a handle word's tier bit and index (the tag is
`h >> 28`), the view's checks (`viewOK`: the scratch tier open for a scratch handle, the index
below the tier's count `CTL[c + t]`), and the branch-free `max`, truncating `z - 1` and the
saturating range arithmetic of the derived words (`satSuccW`, `satPredW`), which keep a walk's
bodies loop- and branch-free per tag (the house rule; `DESIGN.md`, lane `walk`).
-/

namespace L.Arena

/-- The larger of two words (branch-free in L: `x + (y - x) * u64(x < y)`). -/
def maxW (x y : Word) : Word := x + (y - x) * (if x < y then 1 else 0)

/-- Truncating `z - 1` (branch-free in L: `z - u64(0 < z)`). -/
def predW (z : Word) : Word := z - (if 0 < z then 1 else 0)

/-- The tier bit and the index of a handle word. -/
def tierW (h : Word) : Word := (h >>> 27) &&& 1
def idxW (h : Word) : Word := h &&& 134217727

/-- The view checks: a scratch handle needs the scratch tier open, and the index must be below
the tier's count `CTL[c + t]`. -/
def viewOK (m : Mem) (h c : Word) : Prop :=
  ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) ∧ idxW h < rdW (m.arr64 CTL) (c + tierW h)

/-- `min (x + 1) 32767` without wrapping (branch-free in L:
`(x + 1) * u64(x < 32767) + 32767 * u64(32767 <= x)`), con-leche's `satSucc`. -/
def satSuccW (x : Word) : Word :=
  (x + 1) * (if x < 32767 then 1 else 0) + 32767 * (if 32767 ≤ x then 1 else 0)

/-- con-leche's `satPred`: `32767` stays, `0` stays, else `x - 1` (branch-free in L:
`x - u64(0 < x) + u64(x == 32767)`). -/
def satPredW (x : Word) : Word := x - (if 0 < x then 1 else 0) + (if x = 32767 then 1 else 0)

end L.Arena
