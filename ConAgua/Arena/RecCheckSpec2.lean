import ConAgua.Arena.RecCheck
import ConAgua.Arena.RecCheckSpec
import ConAgua.Arena.IndSumSpec2

/-!
# More refinements of `RecCheck` (lane `indproofs`, helper `recb`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `ctors_have_name`: `ctors.any (·.1.name == name)` -/

/-- **The model of `ctors_have_name`.** -/
def chnW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, co, cl, name =>
    if cl = 0 then some 0
    else if rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) co)) = name then some 1
    else chnW n m (co + 1) (cl - 1) name

section arms
variable (n : Nat) (m : Mem) (co cl name : Word)
theorem chnW_nil (h : cl = 0) : chnW (n + 1) m co cl name = some 0 := by simp [chnW, h]
theorem chnW_hit (h : cl ≠ 0) (hx : rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) co)) = name) :
    chnW (n + 1) m co cl name = some 1 := by simp [chnW, h, hx]
theorem chnW_next (h : cl ≠ 0) (hx : rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) co)) ≠ name) :
    chnW (n + 1) m co cl name = chnW n m (co + 1) (cl - 1) name := by simp [chnW, h, hx]
end arms

grind_pattern [ind_grind] chnW_nil => chnW (n + 1) m co cl name
grind_pattern [ind_grind] chnW_hit => chnW (n + 1) m co cl name
grind_pattern [ind_grind] chnW_next => chnW (n + 1) m co cl name

theorem ctorsHaveName_spec (p : Prog) (hp : p.lookup "ctors_have_name" = some ctorsHaveName) (n : Nat) :
    ∀ (s₀ : St) (co cl name : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ctors_have_name" [co, cl, name]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ chnW n s₀.mem co cl name = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ co cl name; rw [invoke_eq _ hp]; simp only [callFn, ctorsHaveName]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ co cl name
    rw [invoke_eq _ hp]
    simp only [callFn, ctorsHaveName]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)


/-- A decoded constructor pair's name word. -/
theorem decCN_nameW {m : Mem} {p : Nat} {x : IConstantVal × Nat} (h : decCN m p = some x)
    (hp : p < 2 ^ 64) :
    ∃ w, rdW (m.arr64 EREC) (rdW (m.arr64 IW) (UInt64.ofNat p)) = w ∧ w.toNat < 2 ^ 32 ∧
      x.1.name = decI w := by
  simp only [decCN, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨q, hq, cv, hcv, nF, -, rfl⟩ := h
  have hr := iwN_rdW hq hp
  obtain ⟨w, hw, hw32, hn⟩ := decCV_name hcv
  refine ⟨w, ?_, hw32, hn⟩
  rw [hr.1]
  have : (UInt64.ofNat q).toNat = q := by simp; have := hr.2; omega
  simp only [rdW, this]
  have hw' : (m.arr64 EREC)[q]? = some w := hw
  rw [hw']; rfl

theorem chnW_ok (n : Nat) : ∀ (m : Mem) (co cl name r : Word) (ctors : List (IConstantVal × Nat)),
    chnW n m co cl name = some r → decPL m (decCN m) co.toNat cl.toNat = some ctors →
    name.toNat < 2 ^ 32 → co.toNat + cl.toNat < 2 ^ 64 →
    (r != 0) = ctors.any (fun c => c.1.name == (decI name : NIdx)) ∧ r.toNat ≤ 1 := by
  induction n with
  | zero => intro m co cl name r ctors h; simp [chnW] at h
  | succ n ih =>
    intro m co cl name r ctors h hd hn hb
    by_cases hl : cl = 0
    · rw [chnW_nil n m co cl name hl] at h
      simp only [Option.some.injEq] at h
      subst h
      have hz : cl.toNat = 0 := by rw [hl]; rfl
      rw [hz] at hd
      simp [decPL] at hd
      subst hd
      simp
    · obtain ⟨hsum, hco1⟩ := toNat_succ_of_lt hb hl
      obtain ⟨l1, hl1⟩ : ∃ l1, cl.toNat = l1 + 1 := ⟨cl.toNat - 1, by
        have : cl.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
        omega⟩
      rw [hl1] at hd
      obtain ⟨pp, x, ys, rfl, hp, hx, hys⟩ := decPL_cons hd
      have hrd := iwN_rdW hp (by omega)
      rw [UInt64.ofNat_toNat] at hrd
      obtain ⟨w, hw, hw32, hname⟩ := decCN_nameW hx hrd.2
      have hiff : (w = name) ↔ (x.1.name == (decI name : NIdx)) = true := by
        rw [hname, beq_iff_eq, decI_eq_iff w hw32, decI_word_self name hn]
      rw [← hrd.1] at hw
      by_cases he : w = name
      · rw [chnW_hit n m co cl name hl (by rw [hw]; exact he)] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [List.any_cons, hiff.mp he]
      · rw [chnW_next n m co cl name hl (by rw [hw]; exact he)] at h
        have hys' : decPL m (decCN m) (co + 1).toNat (cl - 1).toNat = some ys := by
          have hl1' : (cl - 1).toNat = l1 := by omega
          rw [hco1, hl1']; exact hys
        have := ih m (co + 1) (cl - 1) name r ys h hys' hn (by omega)
        have hne : ¬ (x.1.name == (decI name : NIdx)) = true := fun e => he (hiff.mpr e)
        simpa [List.any_cons, hne] using this


/-- **`ctors_have_name` is `ctors.any (·.1.name == name)`** (the test inside `targetMajorNfs`; pure,
the state untouched). -/
theorem ctorsHaveName_refines (p : Prog) (hp : p.lookup "ctors_have_name" = some ctorsHaveName)
    (n : Nat) (s₀ : St) (co cl name : Word) (ctors : List (IConstantVal × Nat))
    (hd : decPL s₀.mem (decCN s₀.mem) co.toNat cl.toNat = some ctors) (hn : name.toNat < 2 ^ 32)
    (hb : co.toNat + cl.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ctors_have_name" [co, cl, name]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      (r.headD 0 != 0) = ctors.any (fun c => c.1.name == (decI name : NIdx)) ∧
      (r.headD 0).toNat ≤ 1; ⊤⦄ := by
  refine triple_post (ctorsHaveName_spec p hp n s₀ co cl name) ?_
  rintro r s' ⟨hl, hm, hw⟩
  exact ⟨hl, hm, chnW_ok n s₀.mem co cl name _ ctors hw hd hn hb⟩

end L.Ind
