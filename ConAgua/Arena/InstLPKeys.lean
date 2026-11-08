module

public import ConAgua.Arena.InstLP
import ConAgua.Arena.LevelInternRef
import Std.Tactic.BVDecide.Normalize.BitVec
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConRon.Bridge.Grind
public import ConAgua.Arena.LevelApd
import all ConAgua.Arena.InstLP

@[expose] public section

/-!
# `keys_ok`: the substitution's keys are stored names

The twin reads the keys back (`readNamesM`), which fails on a handle that does not view. L
checks each key word on the spine stack (`keys_ok`, past the cut-off, where the twin reads them):
a name handle (tag below `3`, the scratch tier open, the index below the tier's count). Under
`ArenaR` such a handle views (`viewN_anon`/`str`/`num`), and under the name store's
well-formedness (`CoreS.nwf`) a viewing handle reads back (con-ron's `denoteN_of_view`).
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **The model of `keys_ok`**: `some ()` where every key word is a name handle. -/
def keysOkW : Nat → Mem → Word → Word → Option Unit
  | 0, _, _, _ => none
  | n + 1, m, o, l =>
    if l = 0 then some ()
    else if 4294967296 ≤ rdW (m.arr64 SPN) o then none
    else if tierW (rdW (m.arr64 SPN) o) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if (3 : Word) ≤ tagW (rdW (m.arr64 SPN) o) then none
    else if nameCnt m (tagW (rdW (m.arr64 SPN) o)) (tierW (rdW (m.arr64 SPN) o)) ≤
        idxW (rdW (m.arr64 SPN) o) then none
    else keysOkW n m (o + 1) (l - 1)

@[arena_grind =] theorem keysOkW_succ (n : Nat) (m : Mem) (o l : Word) :
    keysOkW (n + 1) m o l =
      if l = 0 then some ()
      else if 4294967296 ≤ rdW (m.arr64 SPN) o then none
      else if tierW (rdW (m.arr64 SPN) o) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
      else if (3 : Word) ≤ tagW (rdW (m.arr64 SPN) o) then none
      else if nameCnt m (tagW (rdW (m.arr64 SPN) o)) (tierW (rdW (m.arr64 SPN) o)) ≤
          idxW (rdW (m.arr64 SPN) o) then none
      else keysOkW n m (o + 1) (l - 1) := rfl

theorem keysOk_spec (p : Prog) (hk : p.lookup "keys_ok" = some keysOk) (n : Nat) :
    ∀ (s₀ : St) (o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "keys_ok" [o, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ keysOkW n s₀.mem o l = some (); ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l; rw [invoke_eq _ hk]; simp only [callFn, keysOk]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l
    rw [invoke_eq _ hk]
    simp only [callFn, keysOk]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE, ih] <;>
      finish [tierW, idxW, nameCnt]

/-- A name handle that views reads back. -/
theorem viewN_den {a : AState} (hwf : NStoreWF a.store.lss.ls.ns) {h : NIdx} {v : NNodeView} {a' : AState}
    (hr : (viewN h).run a = .ok (v, a')) : ∃ x, denoteN a.store.lss.ls.ns h = some x := by
  sorry

/-- **The checked keys read back**: their handles' names, as the twin's `readNamesM` needs them,
and the stack slice related to them (`ILWEnv.keys`). -/
theorem keysOkW_names {m : Mem} {a : AState} (hR : ArenaR m a) (hwf : NStoreWF a.store.lss.ls.ns) :
    ∀ (n : Nat) (o l : Word) (lps : List NIdx), keysOkW n m o l = some () →
      hslice? (aread (m.arr64 SPN)) o.toNat l.toNat = some lps → o.toNat + l.toNat < 2 ^ 64 →
      ∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks ∧ NmsR (nameN a.store.lss.ls.ns) m SPN o l ks := by
  sorry

end L.Arena
