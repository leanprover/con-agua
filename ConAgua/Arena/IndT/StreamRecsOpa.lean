module

public import ConAgua.Arena.IndRealOpf
import ConAgua.Arena.IndRealOpf3
import ConAgua.Arena.IndRealOpf2
import ConAgua.Arena.DeclNatCv
import ConAgua.Arena.IndRealAbs
import ConAgua.Arena.InstListRefine
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.StubInd
import all ConAgua.Arena.IndStream
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.MemoLib

@[expose] public section

/-!
# `open_pis_at_fvars` under the stage relation (lane `ronsync2`, stage 3)

`open_pis_at_fvars(n, e, i)` (`IndStream.lean`, the twin's `openPisAtFvars`, which the stream's
`recTyCheck` calls) is `open_pis_at_fvars_f`'s fallback half: `opa_go` from the stack top, the
free variables copied to a fresh pool slice, the top put back. Its body over its callees' runs
(`opaTopK`, by `vcgen`) and `opa_ok`: a returning call is the twin's run with `KeepPost decOLE`
and `AbsOK` after (`opaGo_ok`, `opfTail_ok` of `IndRealOpf3.lean`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `open_pis_at_fvars(n, e, i)`'s body over its callees' runs. -/
def opaTopK (p : Prog) (k : Nat) (m : Mem) (n e i : Word) : Option (List Word × Mem) :=
  if i >>> 63 ≠ 0 then none else
  if m.len64 SPN < rdW (m.arr64 CTL) 136 then none else
  ntBW (callW p k "opa_go" [n, e, i] m) (opfK3 k n (rdW (m.arr64 CTL) 136))

theorem opaTopK_spec (p : Prog) (hp : p.lookup "open_pis_at_fvars" = some openPisAtFvarsL)
    (ha : p.lookup "iw_alloc" = some iwAlloc) (hs : p.lookup "spn_to_iw" = some spnToIwL)
    (k : Nat) (s₀ : St) (n e i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "open_pis_at_fvars" [n, e, i]
    ⦃fun r s' => LocEq s' s₀ ∧ opaTopK p k s₀.mem n e i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, openPisAtFvarsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p k "opa_go", iwAlloc_specW p ha k, s2i_spec p hs k] <;>
    finish (gen := 20) [opaTopK, opfK3, opfTail_some, ntBW]

section
variable (vis : Word) (fe : IFEnv)

/-- **`open_pis_at_fvars` refines `openPisAtFvars`** under the stage relation and the walk memos
(a first fvar index `≥ 2^63` aborts, deviation D33); the memos are well formed after. -/
@[refines ConRon.Arena.openPisAtFvars]
theorem opa_ok {p : Prog} (hO : OpfF p) (hl : p.lookup "open_pis_at_fvars" = some openPisAtFvarsL)
    (N : Nat) (n e i : Word) (he : H e) :
    RelW (fun m args => callW p N "open_pis_at_fvars" args m) [n, e, i] (fun m a => StageR vis fe m a ∧ AbsOK m)
      (openPisAtFvars n.toNat (decI e) i.toNat)
      (fun m m' a r x => KeepPost vis fe decOLE m m' a r x ∧ AbsOK m') := by
  intro m m' a r hc ⟨hS, hAb⟩
  dsimp only at hc
  rcases N with _ | K
  · rw [callW_zero] at hc; cases hc
  have c' := callW_model (M := fun mm => opaTopK p K mm n e i)
    (fun s => opaTopK_spec p hl (hO.get "iw_alloc") (hO.get "spn_to_iw") K s n e i) hc
  have hw63 : (m.arr64 SPN).size < 2 ^ 63 := hAb.wk.2.2.1
  simp only [opaTopK] at c'
  obtain ⟨hsh, c'⟩ := of_ite_none c'
  have hi : i.toNat < 2 ^ 63 := by
    have h1 := congrArg UInt64.toNat (Decidable.not_not.mp hsh)
    rw [UInt64.toNat_shiftRight] at h1
    simp only [UInt64.toNat_zero, UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod,
      Nat.reducePow] at h1
    have := i.toNat_lt
    omega
  generalize hco : rdW (m.arr64 CTL) 136 = co at c'
  obtain ⟨hlen, c'⟩ := of_ite_none c'
  have hcob : co.toNat ≤ (m.arr64 SPN).size := by
    have : ¬ (((m.arr64 SPN).size : Nat).toUInt64 < co) := hlen
    rw [UInt64.lt_iff_toNat_lt] at this
    have h2 : (((m.arr64 SPN).size : Nat).toUInt64).toNat = (m.arr64 SPN).size := by
      simp [Nat.toUInt64]; omega
    omega
  obtain ⟨r2, m2, h2, c'⟩ := ntBW_some c'
  rw [callW_agree opfP_closed (hO.agree opfPFns) K (by decide)] at h2
  obtain ⟨x2, a2, hrun2, hS2, hg2, hAb2, -, hO2⟩ := opaGo_ok vis fe K m m2 a n e i r2 h2
    hS hAb he (by rw [hco]; exact hcob) (by rw [hco]; omega)
  rw [hco] at hO2
  simp only [opfK3] at c'
  cases x2 with
  | none =>
    rw [ite_eq_left (show r2.headD 0 = 0 from hO2)] at c'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
    obtain ⟨hS3, hg3⟩ := stageR_hi hS2 (MemFrame.setCtl m2 136 co) (by simp) (by simp) (by decide)
      (by decide)
    exact ⟨_, _, hrun2, ⟨hS3, hg2.trans hg3, rfl⟩,
      hAb2.frameD (MemFrame.setCtl m2 136 co) (by decide) (by decide)⟩
  | some q =>
    obtain ⟨fvs, b⟩ := q
    obtain ⟨h0, hb, hdb, -, hsl, -⟩ := hO2
    rw [ite_eq_right (by rw [h0]; decide)] at c'
    obtain ⟨⟨hS', hg', hdec⟩, hAb'⟩ := opfTail_ok vis fe hS2 hAb2 hsl hb c'
    rw [hdb] at hdec
    exact ⟨_, _, hrun2, ⟨hS', hg2.trans hg', hdec⟩, hAb'⟩

end

end L.Ind

end
