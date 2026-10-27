import ConAgua.Arena.DeclDivModSpec.DivModTypePins
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# DecCIDefnValue

`PinsIW`, `PinsIW.grow`, `loop_specW`, `loopW`, `decCI_defn_value`, `cp_specW`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open L.Rom (PinSetR)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **The variant slice**: `IW[o ‥ o + l]` holds pointers to the 40-word records of the variants
`ips`, in order. -/
def PinsIW (m : Mem) (o l : Nat) (ips : List INatOpPinSet) : Prop :=
  o + l ≤ iwTop m ∧ l = ips.length ∧ ∀ (j : Nat) (hj : j < ips.length), ∃ ps : Word,
    (iwA m)[o + j]? = some ps ∧ PinSetR m ps ips[j]

theorem PinsIW.grow {m m' : Mem} {o l : Nat} {ips : List INatOpPinSet} (h : PinsIW m o l ips)
    (hg : IWGrow m m') : PinsIW m' o l ips := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.le_trans h1 hg.1, h2, fun j hj => ?_⟩
  obtain ⟨ps, hp, hP⟩ := h3 j hj
  refine ⟨ps, ?_, PinSetR.grow hP hg⟩
  simp only [iwA] at hp ⊢; rw [hg.2.2.1 _ (by omega)]; exact hp

section loop
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-- **`check_div_mod_pin_loop` is its model `loopW`** (generated). -/
l_model loop_specW (p : Prog) (hp : p.lookup "check_div_mod_pin_loop" = some checkDivModPinLoopL)
  fns [hp ↦ loopW list]
  specs [callW_spec p n "div_mod_pin_guard", callW_spec p n "div_mod_certs_guard", callW_spec p n "check_div_mod_pin_at", callW_spec p n "check_div_mod_pin_loop"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 3200000 bind ntBW instances 10000

end loop

end L.Ind

namespace L.Ind
open L.Arena

theorem decCI_defn_value {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {cv : IConstantVal} {v : EIdx} {hint : ConLeche.ReducibilityHint}
    (h : decCI a dn p = some (.defnInfo cv v hint)) :
    a[p]? = some 1 ∧ ∃ w, a[p + 5]? = some w ∧ w.toNat < 2 ^ 32 ∧ v = decI w := by
  obtain ⟨hk, -⟩ : a[p]? = some 1 ∧ True := by
    rcases decCI_defn_cases h with ⟨cv', v', hint', he, hk, hcv⟩ | ⟨w, hw, hne, hnd⟩
    · exact ⟨hk, trivial⟩
    · exact absurd rfl (hnd cv v hint)
  refine ⟨hk, ?_⟩
  unfold decCI at h
  have hn : nat? a p = some 1 := by simp [nat?, hk]
  rw [hn] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨a1, ha1, h⟩ := h
  cases ha1
  simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨cv2, -, v2, hv2, h3, -, he2⟩ := h
  have hv : v2 = v := by cases he2; rfl
  subst hv
  cases hq : a[p + 5]? with
  | none => simp [hd?, hq] at hv2
  | some w =>
    by_cases hlt : w.toNat < 2 ^ 32
    · have e : (hd? a (p + 5) : Option EIdx) = some (decI w) := by simp [hd?, hq, hlt]
      rw [e] at hv2
      exact ⟨w, rfl, hlt, (Option.some.inj hv2).symm⟩
    · simp [hd?, hq, hlt] at hv2

local notation "V" => ConLeche.CheckMode.verified

section pin
variable {dn : NIdx → Option ConLeche.Name} {p : Prog}

/-- **`check_div_mod_pin` is its model `dmCpW`** (generated). -/
l_model cp_specW (p : Prog) (hp : p.lookup "check_div_mod_pin" = some checkDivModPinL)
  fns [hp ↦ dmCpW list]
  specs [callW_spec p n "div_mod_env_guard", callW_spec p n "env_find", callW_spec p n "check_div_mod_pin_loop"]
  grind [arena_grind] heartbeats 1600000 bind ntBW simp [ntBW, rdW_eq, getElem_rdW']

end pin

end L.Ind
