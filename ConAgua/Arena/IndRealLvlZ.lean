import ConAgua.Arena.StubInd
import ConAgua.Arena.CallF
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.LevelZero
import ConAgua.L.ProgHas
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# `lv_zero_caps`' model (lane `indproofs4`, helper `lvl`)

The program- and fuel-free model `lzcF := callF lzcP "lv_zero_caps"` (the recipe of `IndReal.lean`)
over the call-closed sub-program `lzcP` (`lv_zero_caps`, lane `levels`' `lv_zero` with the heap
reads and pushes it calls, `erec_alloc`, the copy `lh_er_copy`). It writes the level heap `LH`, the
record pool `EREC` and their tops `CTL[192]`, `CTL[129]` (`lzcP_closed`); its word model `lzcW`
(`lzc_spec`). The refinement under `StageT` is `IndRealLvlZT.lean`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `lh_er_copy(d, s, l)` -/

/-- The model of `lh_er_copy`: `EREC[d + j] := LH[s + j]` for `j < l`. -/
def lheCopyW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, d, s, l =>
    if l = 0 then some m
    else lheCopyW n (m.set64 EREC d (rdW (m.arr64 LH) s)) (d + 1) (s + 1) (l - 1)

section arms
variable (n : Nat) (m : Mem) (d s l : Word)
theorem lheCopyW_nil (hl : l = 0) : lheCopyW (n + 1) m d s l = some m := by simp [lheCopyW, hl]
theorem lheCopyW_step (hl : l ≠ 0) :
    lheCopyW (n + 1) m d s l =
      lheCopyW n (m.set64 EREC d (rdW (m.arr64 LH) s)) (d + 1) (s + 1) (l - 1) := by
  simp [lheCopyW, hl]
end arms

grind_pattern [ind_grind] lheCopyW_nil => lheCopyW (n + 1) m d s l
grind_pattern [ind_grind] lheCopyW_step => lheCopyW (n + 1) m d s l

theorem lheCopy_spec (p : Prog) (hp : p.lookup "lh_er_copy" = some L.Stubs.lhErCopy) (n : Nat) :
    ∀ (s₀ : St) (d s l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "lh_er_copy" [d, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ lheCopyW n s₀.mem d s l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ d s l; rw [invoke_eq _ hp]; simp only [callFn, L.Stubs.lhErCopy]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ d s l
    rw [invoke_eq _ hp]
    simp only [callFn, L.Stubs.lhErCopy]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 20)

/-- **What an `LH → EREC` copy leaves** (`erCopy_get`). -/
theorem lheCopyW_get (n : Nat) : ∀ (m m' : Mem) (d s l : Word), lheCopyW n m d s l = some m' →
    s.toNat + l.toNat < 2 ^ 64 →
    d.toNat + l.toNat ≤ (m.arr64 EREC).size → (m.arr64 EREC).size < 2 ^ 64 →
    (∀ b, b ≠ EREC → m'.arr64 b = m.arr64 b) ∧ (m'.arr64 EREC).size = (m.arr64 EREC).size ∧
    m'.words.size = m.words.size ∧
    ∀ i, (m'.arr64 EREC)[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + l.toNat then some ((m.arr64 LH)[s.toNat + (i - d.toNat)]?.getD 0)
      else (m.arr64 EREC)[i]? :=
  erCopy_get (by decide) (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) n

/-! ## `lv_zero_caps(l)` -/

/-- After the copy: the record words, the heap top restored. -/
def lzcK3 (t0 q k : Word) : Option Mem → Option (List Word × Mem)
  | none => none
  | some m3 => some ([1, q, k], m3.set64 CTL 192 t0)

/-- After the allocation: the copy. -/
def lzcK2 (n : Nat) (t0 k : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m2) => lzcK3 t0 q k (lheCopyW n m2 q t0 k)

/-- After `lv_zero`: `never`, or the pushed names copied to a fresh record slice. -/
def lzcK1 (n : Nat) (t0 : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (z, m1) =>
    if z ≠ 0 then some ([0, 0, 0], m1.set64 CTL 192 t0)
    else lzcK2 n t0 (htop m1 - t0) (erAllocW m1 (htop m1 - t0))

/-- **The model of `lv_zero_caps`** at the fuel `n + 1` (its callees at `n`). -/
def lzcW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, l => lzcK1 n (htop m) (zeroW n m l)

/-- `lv_zero_caps`' functions. -/
def lzcP : Prog :=
  [("lv_zero_caps", L.Stubs.lvZeroCapsL), ("lv_zero", lvZero), ("lv_node", lvNode),
   ("lh_push", lhPush), ("erec_alloc", erecAlloc), ("lh_er_copy", L.Stubs.lhErCopy)]

def lzcFns : List FnName := lzcP.map (·.1)

/-- `lv_zero_caps` writes the level heap, the record pool and their tops only. -/
theorem lzcP_closed : closedA lzcP [LH, EREC] [192, 129] lzcFns = true := by decide +kernel

section spec
variable (p : Prog) (hpz : p.lookup "lv_zero_caps" = some L.Stubs.lvZeroCapsL)
  (hz : p.lookup "lv_zero" = some lvZero) (hn : p.lookup "lv_node" = some lvNode)
  (hpp : p.lookup "lh_push" = some lhPush) (ha : p.lookup "erec_alloc" = some erecAlloc)
  (hc : p.lookup "lh_er_copy" = some L.Stubs.lhErCopy)

include hpz hz hn hpp ha hc in
theorem lzc_spec (n : Nat) (s₀ : St) (l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_zero_caps" [l]
    ⦃fun r s' => LocEq s' s₀ ∧ lzcW n s₀.mem l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpz]
  simp only [callFn, L.Stubs.lvZeroCapsL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hm1 : ∀ z m1, zeroW n s₀.mem l = some (z, m1) → z ≠ 0 →
        lzcW (n + 1) s₀.mem l = some ([0, 0, 0], m1.set64 CTL 192 (htop s₀.mem)) := by
      intro z m1 h1 h2; simp [lzcW, h1, lzcK1, h2]
    have hm2 : ∀ m1 q m2 m3, zeroW n s₀.mem l = some (0, m1) →
        erAllocW m1 (htop m1 - htop s₀.mem) = some (q, m2) →
        lheCopyW n m2 q (htop s₀.mem) (htop m1 - htop s₀.mem) = some m3 →
        lzcW (n + 1) s₀.mem l =
          some ([1, q, htop m1 - htop s₀.mem], m3.set64 CTL 192 (htop s₀.mem)) := by
      intro m1 q m2 m3 h1 h2 h3; simp [lzcW, h1, lzcK1, lzcK2, h2, lzcK3, h3]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        lvZero_spec p hn hpp hz n, erecAlloc_specW p ha n, lheCopy_spec p hc n] <;>
      finish (gen := 20) [htop]

end spec

/-- The program bundle. -/
abbrev LzcF (p : Prog) : Prop := ProgHas p lzcP

/-- **The model of `lv_zero_caps`** (program- and fuel-free). -/
noncomputable def lzcF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF lzcP "lv_zero_caps" m args

theorem lzcF_spec (p : Prog) (hp : LzcF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_zero_caps" args
    ⦃fun r s' => LocEq s' s₀ ∧ lzcF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec lzcP_closed (hp.agree lzcFns) (by decide) n s₀ args

/-- The model is the word model at some fuel. -/
theorem lzcF_lzcW {m m' : Mem} {l : Word} {r : List Word} (h : lzcF m [l] = some (r, m')) :
    ∃ n, lzcW n m l = some (r, m') := by
  obtain ⟨n, hc⟩ := callF_run h
  obtain ⟨s', rfl, -, hw⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lzc_spec lzcP rfl rfl rfl rfl rfl rfl n _ l) hc
  exact ⟨n, hw⟩

end L.Ind
