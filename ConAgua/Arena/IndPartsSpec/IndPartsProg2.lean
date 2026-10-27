import ConAgua.Arena.IndPartsSpec.PartsConsPL
import ConAgua.Arena.IndPosSpec.NestOccGo
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# IndPartsProg2

`partsSimW`, `memWk`, `memberIdxAt_specK`, `ctorMember_specK`, `ctmW`, `partsIwRd` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A real callee's word-model fact (`RelW`) as a `Sim`. -/
theorem partsSimW {α : Type} {W : Mem → List Word → Option (List Word × Mem)} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    (h : RelW W args pre op post) {m : Mem} {a : AState} (hpre : pre m a) :
    Sim (W m args) op a (fun r x m' a' => post m m' a' r x) :=
  fun r m' e => h m m' a r e hpre

/-! ## `ctor_member` -/

/-- `member_idx_at`'s model at every exec fuel. -/
def memWk : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, no, nl, lvls, e => memW n m no nl lvls e

theorem memberIdxAt_specK (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hp : p.lookup "member_idx_at" = some memberIdxAt)
    (n : Nat) (s₀ : St) (no nl lvls e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "member_idx_at" [no, nl, lvls, e]
    ⦃fun r s' => LocEq s' s₀ ∧ memWk n s₀.mem no nl lvls e = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => rw [invoke_eq _ hp]; simp only [callFn, memberIdxAt]; vcgen [exec] <;> grind
  | succ n => exact memberIdxAt_spec p hv hf hp n s₀ no nl lvls e

/-- **`ctor_member` is its model `ctmW`** (generated). -/
l_model ctorMember_specK (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hm : p.lookup "member_idx_at" = some memberIdxAt)
    (hp : p.lookup "ctor_member" = some ctorMember) (hst : StripProg p) (had : AdF p)
  fns [hp ↦ ctmW list]
  specs [stripPis_specF p hst n, gafF_spec p had n, memberIdxAt_specK p hv hf hm n]
  grind [ind_grind] finish [rdW_eq] gen 20

/-! ## Reading decoded records' words -/

/-- A number of the pool decoded below the top: the word L reads there, below the top. -/
theorem partsIwRd {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) {w : Word} (hw : w.toNat = i) :
    rdW (m.arr64 IW) w = UInt64.ofNat v ∧ v < 2 ^ 64 ∧ i < iwTop m := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨hi, hx'⟩ := truncM_iw_get hx
  simp only [iwA] at hx'
  refine ⟨?_, x.toNat_lt, hi⟩
  rw [rdW_of_get? hw.symm hx']; simp

theorem partsIwLt {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) : i < iwTop m := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, -⟩ := h
  exact (truncM_iw_get hx).1

/-- The type handle of a constant decoded below the top. -/
theorem partsCVType {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp (truncM m) q = some cv)
    {w : Word} (hw : w.toNat = q) :
    (rdW (m.arr64 EREC) (w + 3)).toNat < 2 ^ 32 ∧ decI (rdW (m.arr64 EREC) (w + 3)) = cv.type := by
  obtain ⟨x, hx, hxl, hxe⟩ := hd?_some (decCV_type h)
  obtain ⟨hi, hx'⟩ := truncM_er_get hx
  simp only [erA] at hx'
  have hE : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt
  have hw3 : (w + 3).toNat = q + 3 := by rw [UInt64.toNat_add]; simp; omega
  rw [rdW_of_get? hw3.symm hx']
  exact ⟨hxl, hxe.symm⟩

/-- A word sum that does not wrap. -/
theorem partsAddNoOv {a b : Word} (h : ¬ a + b < a) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
  have := b.toNat_lt; have := a.toNat_lt
  rw [UInt64.toNat_add]; omega

/-- After `sl_cons`: the slice (the shared tail of the hand `IndParts` models). -/
def bgoK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

/-! ## The census theorems -/

/-- The program bundle of the groups. -/
structure IndPartsProg2 (p : Prog) : Prop extends IndPartsProg p where
  view : p.lookup "e_view" = some eView
  find : p.lookup "sl_find" = some slFind
  midx : p.lookup "member_idx_at" = some memberIdxAt
  cmem : p.lookup "ctor_member" = some ctorMember
  rec2 : p.lookup "rec2" = some rec2
  gone : p.lookup "block_groups_one" = some blockGroupsOne
  ggo : p.lookup "block_groups_go" = some blockGroupsGo
  groups : p.lookup "block_groups" = some blockGroups

end L.Ind

end
