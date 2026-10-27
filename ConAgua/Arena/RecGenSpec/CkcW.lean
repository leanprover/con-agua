import ConAgua.Arena.IndRealWalk
import ConAgua.Arena.RecGen

/-!
# CkcW

`ckcW`, `ckcK1`, `ckcK2`, `ckcK3`, `ckcK3_some`, `keyClosedTest`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `class_key_of_closed`: `ds.allM` of the `bvarB`/`fvarB` closedness test -/

mutual
/-- **The model of `class_key_of_closed`.** -/
def ckcW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, nP, o, l =>
    if l = 0 then some ([1], m)
    else ckcK1 n nP o l (rdW (m.arr64 IW) o) (bvbF m [CWF, rdW (m.arr64 IW) o])
/-- After `bvar_b`. -/
def ckcK1 (n : Nat) (nP o l e : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m1) =>
    if rb.headD 0 ≠ 0 then some ([0], m1) else ckcK2 n nP o l (fvbF m1 [CWF, e])
/-- After `fvar_b`. -/
def ckcK2 (n : Nat) (nP o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, m2) =>
    if nP < rf.headD 0 then some ([0], m2) else ckcK3 (ckcW n m2 nP (o + 1) (l - 1))
/-- After the recursive call: its first word. -/
def ckcK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (nP o l e : Word) (rb rf r : List Word)
theorem ckcK3_some : ckcK3 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] ckcK3_some => ckcK3 (some (r, m))

/-- The twin's per-parameter closedness test. -/
def keyClosedTest (nP : Nat) (x : EIdx) : AM Bool := do
  if (← bvarB coreWalkFuel x) != 0 then pure false
  else pure ((← fvarB coreWalkFuel x) ≤ nP)

/-! ## `class_fields_of_hits`: the count and class of `ihs.filter (·.1 == i)` -/

l_model classFieldsOfHits_spec (p : Prog)
    (hp : p.lookup "class_fields_of_hits" = some classFieldsOfHits)
  fns [hp ↦ cfhW ro tuple]
  grind [arena_grind] simp [getElem_rdW']

/-- What `class_fields_of_hits` returns about the twin's `hits`: their count, and, when there is
exactly one, its class. -/
def HitsRes (hits : List (Nat × Nat)) (cnt cls : Word) : Prop :=
  cnt.toNat = hits.length ∧ ∀ h, hits = [h] → cls = UInt64.ofNat h.2 ∧ h.2 < 2 ^ 64

theorem decTM_member {m : Mem} {pp : Nat} {t : TargetMajor} (h : decTM m pp = some t) :
    ∃ k, iwN m (pp + 8) = some k ∧ t.member = decON k := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, k, hk, _, -, _, -, rfl⟩ := h
  exact ⟨k, hk, rfl⟩

end L.Ind

end
