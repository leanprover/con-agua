import ConAgua.Arena.RecCheckSpec17

/-!
# `RecCheck`: `consBlockRecsTF` (lane `indproofs3`, helper `rec`)

Each checked recursor with its stored rules (`tgt_stored_rules`, `RecCheckSpec17`) at its major,
the rules copied into one consecutive run (`rules_to_erec`), a fresh `.recInfo` record
(`cons_block_recs_push`) pushed by lane `decls2`'s `env_push`. The rules' lookups at the
constructors' view `vis₂` (the twin's `fe.restrictTo vis₂`: `StageR.restrict`/`unrestrict`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `rules_to_erec` -/

/-- The memory after one record's eleven copies (each copy reads the memory of its time). -/
def cpMem (m : Mem) (b old : Word) : Mem :=
  let m1 := m.set64 EREC b (rdW (m.arr64 EREC) old)
  let m2 := m1.set64 EREC (b + 1) (rdW (m1.arr64 EREC) (old + 1))
  let m3 := m2.set64 EREC (b + 2) (rdW (m2.arr64 EREC) (old + 2))
  let m4 := m3.set64 EREC (b + 3) (rdW (m3.arr64 EREC) (old + 3))
  let m5 := m4.set64 EREC (b + 4) (rdW (m4.arr64 EREC) (old + 4))
  let m6 := m5.set64 EREC (b + 5) (rdW (m5.arr64 EREC) (old + 5))
  let m7 := m6.set64 EREC (b + 6) (rdW (m6.arr64 EREC) (old + 6))
  let m8 := m7.set64 EREC (b + 7) (rdW (m7.arr64 EREC) (old + 7))
  let m9 := m8.set64 EREC (b + 8) (rdW (m8.arr64 EREC) (old + 8))
  let m10 := m9.set64 EREC (b + 9) (rdW (m9.arr64 EREC) (old + 9))
  m10.set64 EREC (b + 10) (rdW (m10.arr64 EREC) (old + 10))

/-- **The model of `rule_copy`.** -/
def rcpW (m : Mem) (b old : Word) : Option (List Word × Mem) := some ([0], cpMem m b old)

def rteK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([0], m)

/-- **The model of `rules_to_erec_go`** (exec fuel). -/
def rteGoW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, b, ro, rl =>
    if rl = 0 then some ([0], m)
    else rteK1 (rteGoW n (cpMem m b (rdW (m.arr64 IW) ro)) (b + 11) (ro + 1) (rl - 1))

def rteK3 (b rl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([b, rl], m)

def rteK2 (n : Nat) (ro rl : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (b, m) => rteK3 b rl (rteGoW n m b ro rl)

/-- **The model of `rules_to_erec`** (exec fuel). -/
def rteW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, ro, rl => if 4294967296 ≤ rl then none else rteK2 n ro rl (erAllocW m (rl * 11))

section arms
variable (n : Nat) (m : Mem) (b ro rl : Word) (r : List Word)
theorem rcW_eq (old : Word) : rcpW m b old = some ([0], cpMem m b old) := rfl
theorem rteGoW_nil (h : rl = 0) : rteGoW (n + 1) m b ro rl = some ([0], m) := by simp [rteGoW, h]
theorem rteGoW_cons (h : ¬ rl = 0) : rteGoW (n + 1) m b ro rl =
    rteK1 (rteGoW n (cpMem m b (rdW (m.arr64 IW) ro)) (b + 11) (ro + 1) (rl - 1)) := by simp [rteGoW, h]
theorem rteK1_some : rteK1 (some (r, m)) = some ([0], m) := rfl
theorem rteW_big (h : 4294967296 ≤ rl) : rteW (n + 1) m ro rl = none := by simp [rteW, h]
theorem rteW_ok' (h : ¬ 4294967296 ≤ rl) : rteW (n + 1) m ro rl = rteK2 n ro rl (erAllocW m (rl * 11)) := by
  simp [rteW, h]
theorem rteK2_some : rteK2 n ro rl (some (b, m)) = rteK3 b rl (rteGoW n m b ro rl) := rfl
theorem rteK3_some : rteK3 b rl (some (r, m)) = some ([b, rl], m) := rfl
end arms
attribute [ind_grind] rcW_eq rteGoW_nil rteGoW_cons rteK1_some rteW_big rteW_ok' rteK2_some rteK3_some

/-- The lookups of `cons_block_recs_tf`. -/
structure CbrLook (p : Prog) : Prop where
  tsr : TsrLook p
  rp : RecProg p
  rc : p.lookup "rule_copy" = some ruleCopy
  rteg : p.lookup "rules_to_erec_go" = some rulesToErecGo
  rir : p.lookup "rec_info_rec" = some recInfoRec
  rte : p.lookup "rules_to_erec" = some rulesToErec
  push : p.lookup "cons_block_recs_push" = some consBlockRecsPush
  mi : p.lookup "block_shape_major_idx_at" = some blockShapeMajorIdxAt
  rpa : p.lookup "block_shape_rule_prefix_at" = some blockShapeRulePrefixAt
  cbr : p.lookup "cons_block_recs_tf" = some consBlockRecsTF

theorem rc_spec (p : Prog) (L : CbrLook p) (n : Nat) (s₀ : St) (b old : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rule_copy" [b, old]
    ⦃fun r s' => LocEq s' s₀ ∧ rcpW s₀.mem b old = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.rc]
  simp only [callFn, ruleCopy]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
      finish [rcpW, cpMem]

theorem rteGo_spec (p : Prog) (L : CbrLook p) (n : Nat) :
    ∀ (s₀ : St) (b ro rl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rules_to_erec_go" [b, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ rteGoW n s₀.mem b ro rl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ b ro rl
    rw [invoke_eq _ L.rteg]; simp only [callFn, rulesToErecGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ b ro rl
    rw [invoke_eq _ L.rteg]
    simp only [callFn, rulesToErecGo]
    sym (gen := 80) (instances := 20000) only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, rc_spec p L n, ih] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

theorem rte_spec (p : Prog) (L : CbrLook p) (n : Nat) (s₀ : St) (ro rl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rules_to_erec" [ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ rteW n s₀.mem ro rl = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
    rw [invoke_eq _ L.rte]
    simp only [callFn, rulesToErec]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, erecAlloc_specW p L.tsr.ea n,
        rteGo_spec p L n] <;>
      finish (gen := 20)

end L.Ind
