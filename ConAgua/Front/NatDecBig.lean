module

public import ConAgua.Front.NatDec
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.Frame
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Front.NatDec
import all ConAgua.Arena.NatAdd
import all ConAgua.Arena.NatMul

@[expose] public section

/-!
# Long decimal literals: `nat_dec_split` and `nat_dec_big`

Word models over `callW` of every callee (`l_model`), for the value proofs in `NatDecBigVal.lean`.
-/

open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Front

open L.Arena

/-- **`nat_dec_split`** (generated): `splitW`, every call through `callW`. -/
l_model natDecSplit_spec (p : Prog) (hs : p.lookup "nat_dec_split" = some natDecSplit)
  fns [hs ↦ splitW list]
  specs [callW_spec p n "nat_dec_chunks", callW_spec p n "nat_dec_split", callW_spec p n "nat_mul",
    callW_spec p n "nat_add"]
  grind [arena_grind]

/-- **`nat_dec_big`** (generated): `bigW`, every call through `callW`. -/
l_model natDecBig_spec (p : Prog) (hb : p.lookup "nat_dec_big" = some natDecBig)
  fns [hb ↦ bigW list]
  specs [callW_spec p n "nat_dec_split", callW_spec p n "nat_mul"]
  grind [arena_grind]

/-! ## `nat_dec` -/

/-- The functions of `natDecProg`. -/
def natDecFns : List FnName := natDecProg.map (·.1)

set_option maxRecDepth 100000 in
/-- `natDecProg` writes only the pool's tiers and `CTL[0]`, and calls only its own functions. -/
theorem natDec_closed : closedA natDecProg [POOL, tier1 POOL] [0] natDecFns = true := by decide +kernel

/-- **`nat_dec(c, d)`'s model equation**, in a program that binds `natDecProg`'s functions as
`natDecProg` does. -/
theorem natDec_specW (p : Prog) (b : Array UInt8) (hpn : p.lookup "nat_dec" = some natDec)
    (hag : ∀ g ∈ natDecFns, p.lookup g = natDecProg.lookup g) (n : Nat) (s₀ : St)
    (hm : s₀.mem.arr8 IN = b) (c d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_dec" [c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ natDecW b s₀.mem c d = some (r, s'.mem); ⊤⦄ := by
  have hpc : p.lookup "dec_chunk" = some decChunk := (hag _ (by decide)).trans rfl
  have hpm : p.lookup "nat_mad" = some natMad := (hag _ (by decide)).trans rfl
  have hpd : p.lookup "nat_dec_chunks" = some natDecChunks := (hag _ (by decide)).trans rfl
  rw [invoke_eq _ hpn]
  simp only [callFn, natDec]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        callF_spec natDec_closed hag (f := "nat_dec_big") (by decide) n,
        natDecChunks_specW p b hpc hpm hpd n] <;> finish [natDecW]

/-- `nat_dec_big`'s first result is the old top. -/
theorem bigW_top {p : Prog} {n : Nat} {m m' : Mem} {c d : Word} {r : List Word}
    (h : bigW p n m c d = some (r, m')) : r.headD 0 = m.top := by
  cases n with
  | zero => rw [bigW.eq_1] at h; cases h
  | succ n =>
  rw [bigW.eq_2] at h
  rcases hL : bigW.loop1 p (n + 1) m (d - c) 1 19 with _ | ⟨k, m₀⟩
  · rw [hL, bigW.k_loop1.eq_1] at h; cases h
  rw [hL] at h
  by_cases hlen : m₀.len64 (tierA POOL (rdW (m.arr64 CTL) 0 >>> 40)) <
      (rdW (m.arr64 CTL) 0 &&& 1099511627775) + k + k + 1
  · rw [bigW.k_loop1.abort1 _ _ _ _ _ _ _ _ _ hlen] at h; cases h
  rw [bigW.k_loop1.arm1 _ _ _ _ _ _ _ _ _ hlen] at h
  generalize bigW.loop2 _ _ _ _ _ _ _ = x at h
  rcases x with _ | mk
  · rw [bigW.k_loop2.eq_1] at h; cases h
  rw [bigW.k_loop2.eq_2] at h
  generalize callW _ _ _ _ _ = y at h
  rcases y with _ | ⟨r₅, m₅⟩
  · rw [bigW.k_nat_dec_split.eq_1] at h; cases h
  rw [bigW.k_nat_dec_split.eq_2] at h
  cases h
  simp [rdW, Mem.top]

theorem big_run {n : Nat} {m m' : Mem} {c d : Word} {r : List Word}
    (h : callW natDecProg n "nat_dec_big" [c, d] m = some (r, m')) : bigW natDecProg n m c d = some (r, m') := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (natDecBig_spec natDecProg rfl n ⟨m, Locals.init []⟩ c d) h
  exact hW

/-- **`nat_dec` on a long literal changes only the pool's tiers and `CTL[0]`** (from the program
text, `natDec_closed`). -/
theorem natDecBig_frame {m m' : Mem} {c d : Word} {r : List Word}
    (h : callF natDecProg "nat_dec_big" m [c, d] = some (r, m')) :
    MemFrame [POOL, tier1 POOL] [0] m m' := by
  obtain ⟨n, hn⟩ := callF_run h
  obtain ⟨s', rfl, hF, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (invoke_memFrame natDec_closed n (f := "nat_dec_big") (by decide) [c, d] ⟨m, Locals.init []⟩) hn
  exact hF

/-- `nat_dec`'s first result is the old top. -/
theorem natDecW_big_top {m m' : Mem} {c d : Word} {r : List Word}
    (h : callF natDecProg "nat_dec_big" m [c, d] = some (r, m')) : r.headD 0 = m.top := by
  obtain ⟨n, hn⟩ := callF_run h
  exact bigW_top (big_run hn)

end L.Front
