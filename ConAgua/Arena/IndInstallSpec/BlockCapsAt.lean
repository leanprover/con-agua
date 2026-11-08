module

public import ConAgua.Arena.IndInstall
public import ConAgua.Arena.IndMaster
public import ConAgua.Arena.IndPartsSpec.MemberNames
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.Env
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndInstall

@[expose] public section

/-!
# BlockCapsAt: `ConRon.Arena.blockCapsAt` (an IW slice copied into fresh EREC words), `ConRon.Arena.blockCapsAt` (the ctor-name list), `ConRon.Arena.checkBlockPositivity` (the empty NestState)

The refinement theorems `checkBlockPositivityInit_refines`, `blockCapsCtorNames_refines`, `blockCapsAtErCopy_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `check_block_positivity_init` -/

theorem checkBlockPositivityInit_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "check_block_positivity_init" = some checkBlockPositivityInit) (n : Nat)
    (s₀ : St) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_positivity_init" []
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = rec6Mem s₀.mem 0 0 0 0 0 0 ∧
      r.headD 0 = rdW (s₀.mem.arr64 CTL) 200 ∧
      (rdW (s₀.mem.arr64 CTL) 200).toNat + 6 ≤ (s₀.mem.arr64 IW).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockPositivityInit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_spec p ha n] <;>
      finish [rec6Mem, allocMem]

theorem posInit_dec {m : Mem} (hsz : (m.arr64 IW).size < 2 ^ 64) (hc : 200 < (m.arr64 CTL).size)
    (hroom : (rdW (m.arr64 CTL) 200).toNat + 6 ≤ (m.arr64 IW).size) :
    decNS (rec6Mem m 0 0 0 0 0 0) (rdW (m.arr64 CTL) 200).toNat = some {} ∧
    IWGrow m (rec6Mem m 0 0 0 0 0 0) ∧
    MemFrame [IW] [200] m (rec6Mem m 0 0 0 0 0 0) ∧ iwTop (rec6Mem m 0 0 0 0 0 0) = iwTop m + 6 := by
  generalize hq : rdW (m.arr64 CTL) 200 = q0 at *
  have hp := rec6Mem_post m 0 0 0 0 0 0 hc (by rw [hq]; exact hroom) hsz
  obtain ⟨hget, hg, hf, htop⟩ := hp
  refine ⟨?_, hg, hf, ?_⟩
  · have e : ∀ j, j < 6 → ((rec6Mem m 0 0 0 0 0 0).arr64 IW)[q0.toNat + j]? = some 0 := by
      intro j hj
      have := hget j hj
      rw [hq] at this
      rw [this]
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    simp only [decNS, decAt, decPL, iwN, nat?, iwA, aread_apply, aread_apply]
    have e0 := e 0 (by omega)
    have e1 := e 1 (by omega)
    have e2 := e 2 (by omega)
    have e3 := e 3 (by omega)
    have e4 := e 4 (by omega)
    have e5 := e 5 (by omega)
    simp only [Nat.add_zero] at e0
    simp [e0, e1, e2, e3, e4, e5]
  · simp only [iwTop, htop, hq, UInt64.toNat_add]; simp; omega

/-- **`check_block_positivity_init` is the empty `NestState`** (`{}` of `checkBlockPositivity`):
a fresh all-zero record that decodes as `{}`, the pool only grown. -/
@[refines_part ConRon.Arena.checkBlockPositivity "the empty NestState"]
theorem checkBlockPositivityInit_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "check_block_positivity_init" = some checkBlockPositivityInit) (n : Nat)
    (s₀ : St) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hc : 200 < (s₀.mem.arr64 CTL).size) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_positivity_init" []
    ⦃fun r s' => LocEq s' s₀ ∧ decNS s'.mem (r.headD 0).toNat = some {} ∧
      IWGrow s₀.mem s'.mem ∧ MemFrame [IW] [200] s₀.mem s'.mem ∧ r.headD 0 = rdW (s₀.mem.arr64 CTL) 200 ∧
      iwTop s'.mem = iwTop s₀.mem + 6; ⊤⦄ := by
  refine triple_post (checkBlockPositivityInit_spec p ha hp n s₀ hsz) ?_
  rintro r s' ⟨hl, hm, hr, hroom⟩
  obtain ⟨h1, h2, h3, h4⟩ := posInit_dec hsz hc hroom
  rw [hm, hr]
  exact ⟨hl, h1, h2, h3, rfl, h4⟩

/-! ## `block_caps_ctor_names` -/

/-- The model of `block_caps_ctor_names(o, l)` at the caller's fuel `n` (the copy runs at `n - 1`). -/
def ctorNamesW (n : Nat) (m : Mem) (o l : Word) : Option (List Word × Mem) :=
  match allocW m l with
  | none => none
  | some (q, m1) =>
    match nameCopyW (n - 1) m1 q o l with
    | none => none
    | some m2 => some ([q, l], m2)

theorem blockCapsCtorNames_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "member_names_copy" = some memberNamesCopy)
    (hp : p.lookup "block_caps_ctor_names" = some blockCapsCtorNames) (n : Nat) (s₀ : St)
    (o l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_caps_ctor_names" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ctorNamesW n s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockCapsCtorNames]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hmod : ∀ q m1 m2, allocW s₀.mem l = some (q, m1) → nameCopyW n m1 q o l = some m2 →
        ctorNamesW (n + 1) s₀.mem o l = some ([q, l], m2) := by
      intro q m1 m2 h1 h2
      simp [ctorNamesW, h1, h2]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n, memberNamesCopy_spec p hc n] <;>
      finish (gen := 20)

/-- **What `block_caps_ctor_names` builds**: a fresh `IW` slice of the names of the constants
`cvs`, given as the first words of the pointers in the slice `(o, l)`. -/
theorem ctorNamesW_dec {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : ctorNamesW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop m)
    (cvs : List IConstantVal) (hlen : cvs.length = l.toNat)
    (hcv : ∀ j (hj : j < l.toNat), ∃ v a, iwN m (o.toNat + j) = some v ∧ v < iwTop m ∧
      iwN m v = some a ∧ decCVp m a = some cvs[j]) :
    r = [rdW (m.arr64 CTL) 200, l] ∧
    decHL m' (rdW (m.arr64 CTL) 200).toNat l.toNat = some (cvs.map (·.name)) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
    (rdW (m.arr64 CTL) 200).toNat + l.toNat = iwTop m' := by
  sorry

theorem decCN_some {m : Mem} {v : Nat} {y : IConstantVal × Nat} (h : decCN m v = some y) :
    (∃ a, iwN m v = some a ∧ decCVp m a = some y.1) ∧ iwN m (v + 1) = some y.2 := by
  rw [decCN] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := h
  exact ⟨⟨a, ha, hb⟩, hc⟩

/-- **`block_caps_ctor_names` is the ctor-name list of `blockCapsAt`** (`cs.map (·.1.name)`):
the new `IW` slice decodes as the names of the constructors `cs` at the pointer slice `(o, l)`. -/
@[refines_part ConRon.Arena.blockCapsAt "the ctor-name list"]
theorem blockCapsCtorNames_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "member_names_copy" = some memberNamesCopy)
    (hp : p.lookup "block_caps_ctor_names" = some blockCapsCtorNames) (n : Nat) (s₀ : St)
    (o l : Word) (cs : List (IConstantVal × Nat))
    (hcs : decPL s₀.mem (decCN s₀.mem) o.toNat l.toNat = some cs)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hcl : 200 < (s₀.mem.arr64 CTL).size)
    (hsrc : o.toNat + l.toNat ≤ iwTop s₀.mem)
    (hptr : ∀ j v, j < l.toNat → iwN s₀.mem (o.toNat + j) = some v → v < iwTop s₀.mem) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_caps_ctor_names" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [rdW (s₀.mem.arr64 CTL) 200, l] ∧
      decHL s'.mem (rdW (s₀.mem.arr64 CTL) 200).toNat l.toNat = some (cs.map (·.1.name)) ∧
      IWGrow s₀.mem s'.mem ∧ MemFrame [IW] [200] s₀.mem s'.mem ∧
      (rdW (s₀.mem.arr64 CTL) 200).toNat + l.toNat = iwTop s'.mem; ⊤⦄ := by
  refine triple_post (blockCapsCtorNames_spec p ha hc hp n s₀ o l) ?_
  rintro r s' ⟨hl, hm⟩
  have hlen := decPL_length _ hcs
  have := ctorNamesW_dec hm hsz hcl hsrc (cs.map (·.1)) (by simp [hlen]) (fun j hj => by
    obtain ⟨v, y, hv, hy, hget⟩ := decPL_get l.toNat o.toNat cs hcs j hj
    obtain ⟨⟨a, hva, hcv⟩, -⟩ := decCN_some hy
    have hj' : j < cs.length := by omega
    have hy' : cs[j] = y := by
      simpa [List.getElem?_eq_getElem hj'] using hget
    refine ⟨v, a, hv, hptr j v hj hv, hva, ?_⟩
    simp [List.getElem_map, hy', hcv])
  simp only [List.map_map] at this
  exact ⟨hl, this⟩

theorem decPL_of_get {m : Mem} {α : Type} (f : Nat → Option α) : ∀ (xs : List α) (o : Nat),
    (∀ j (hj : j < xs.length), ∃ v, iwN m (o + j) = some v ∧ f v = some xs[j]) →
    decPL m f o xs.length = some xs
  | [], o, _ => by simp [decPL]
  | x :: xs, o, h => by
    obtain ⟨v0, hv0, hf0⟩ := h 0 (by simp)
    have ih := decPL_of_get f xs (o + 1) (fun j hj => by
      obtain ⟨v, hv, hf⟩ := h (j + 1) (by simpa using hj)
      refine ⟨v, ?_, by simpa using hf⟩
      have e : o + (j + 1) = o + 1 + j := by omega
      simpa [e] using hv)
    rw [List.length_cons, decPL_succ]
    simp only [Nat.add_zero] at hv0
    simp [hv0, hf0, ih]

/-! ## `block_caps_at_er_copy` -/

/-- The model of `block_caps_at_er_copy_go`. -/
def ieCopyW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, d, s, l =>
    if l = 0 then some m
    else ieCopyW n (m.set64 EREC d (rdW (m.arr64 IW) s)) (d + 1) (s + 1) (l - 1)

section arms
variable (n : Nat) (m : Mem) (d s l : Word)
theorem ieCopyW_nil (hl : l = 0) : ieCopyW (n + 1) m d s l = some m := by simp [ieCopyW, hl]
theorem ieCopyW_step (hl : l ≠ 0) :
    ieCopyW (n + 1) m d s l =
      ieCopyW n (m.set64 EREC d (rdW (m.arr64 IW) s)) (d + 1) (s + 1) (l - 1) := by
  simp [ieCopyW, hl]
end arms

grind_pattern [ind_grind] ieCopyW_nil => ieCopyW (n + 1) m d s l
grind_pattern [ind_grind] ieCopyW_step => ieCopyW (n + 1) m d s l

theorem ieCopy_spec (p : Prog) (hp : p.lookup "block_caps_at_er_copy_go" = some blockCapsAtErCopyGo) (n : Nat) :
    ∀ (s₀ : St) (d s l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_caps_at_er_copy_go" [d, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ ieCopyW n s₀.mem d s l = some s'.mem; ⊤⦄ := by
  sorry

/-- **What a copy `EREC[d + j] := src[s + j]` leaves** (`F` any model of such a loop: `ieCopyW`,
`lheCopyW`): every array but `EREC` as it was, `EREC` the same size, the destination holding the
source, the rest of `EREC` unchanged. -/
theorem erCopy_get {src : ArrId} (hsrc : src ≠ EREC) {F : Nat → Mem → Word → Word → Word → Option Mem}
    (h0 : ∀ m d s l, F 0 m d s l = none)
    (hF : ∀ n m d s l, F (n + 1) m d s l =
      if l = 0 then some m else F n (m.set64 EREC d (rdW (m.arr64 src) s)) (d + 1) (s + 1) (l - 1))
    (n : Nat) : ∀ (m m' : Mem) (d s l : Word), F n m d s l = some m' →
    s.toNat + l.toNat < 2 ^ 64 →
    d.toNat + l.toNat ≤ (m.arr64 EREC).size → (m.arr64 EREC).size < 2 ^ 64 →
    (∀ b : TieredArray, b ≠ ↑EREC → m'.arr64 b = m.arr64 b) ∧ (m'.arr64 EREC).size = (m.arr64 EREC).size ∧
    ∀ i, (m'.arr64 EREC)[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + l.toNat then some ((m.arr64 src)[s.toNat + (i - d.toNat)]?.getD 0)
      else (m.arr64 EREC)[i]? := by
  induction n with
  | zero => intro m m' d s l h; simp [h0] at h
  | succ n ih =>
    intro m m' d s l h hs hd hsz
    by_cases hl : l = 0
    · rw [hF, ite_eq_left hl] at h
      cases h
      subst hl
      refine ⟨fun _ _ => rfl, rfl, fun i => ?_⟩
      have : ¬ (d.toNat ≤ i ∧ i < d.toNat + (0 : Word).toNat) := by
        simp only [UInt64.toNat_zero]; omega
      simp only [this, ite_false]
    · rw [hF, ite_eq_right hl] at h
      have hl0 : 0 < l.toNat := Nat.pos_of_ne_zero fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
      have hl1 : (l - 1).toNat = l.toNat - 1 := by
        rw [UInt64.toNat_sub]; simp; omega
      have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hs1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hdlt : d.toNat < (m.arr64 EREC).size := by omega
      obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.set64 EREC d (rdW (m.arr64 src) s) := ⟨_, rfl⟩
      rw [← hm1] at h
      have hsz1 : (m1.arr64 EREC).size = (m.arr64 EREC).size := by
        rw [hm1, Mem.arr64_set64_same]; simp
      have hE1 : m1.arr64 src = m.arr64 src := by
        rw [hm1, Mem.arr64_set64_ne _ _ _ _ _ (TieredArray.t0_ne hsrc)]
      have hget1 : ∀ i, (m1.arr64 EREC)[i]? = if i = d.toNat then some ((m.arr64 src)[s.toNat]?.getD 0)
          else (m.arr64 EREC)[i]? := by
        intro i
        rw [hm1, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        by_cases hi : d.toNat = i
        · subst hi
          simp only [hdlt, ite_true]
          simp [rdW]
        · simp [hi, Ne.symm hi]
      obtain ⟨hA, hS, hG⟩ := ih m1 m' (d + 1) (s + 1) (l - 1) h
        (by rw [hs1, hl1]; omega)
        (by rw [hd1, hl1, hsz1]; omega) (by rw [hsz1]; exact hsz)
      rw [hE1] at hG
      refine ⟨fun b hb => (hA b hb).trans ?_, hS.trans hsz1, fun i => ?_⟩
      · rw [hm1, Mem.arr64_set64_ne _ _ _ _ _ hb]
      · rw [hG i, hd1, hl1, hs1]
        by_cases hi : d.toNat ≤ i ∧ i < d.toNat + l.toNat
        · rw [ite_eq_left hi]
          by_cases hid : i = d.toNat
          · subst hid
            have : ¬ (d.toNat + 1 ≤ d.toNat ∧ d.toNat < d.toNat + 1 + (l.toNat - 1)) := by omega
            rw [ite_eq_right this, hget1, ite_eq_left rfl]; simp
          · have h2 : d.toNat + 1 ≤ i ∧ i < d.toNat + 1 + (l.toNat - 1) := by omega
            rw [ite_eq_left h2, show s.toNat + 1 + (i - (d.toNat + 1)) = s.toNat + (i - d.toNat) by omega]
        · rw [ite_eq_right hi, ite_eq_right (by omega), hget1, ite_eq_right (by omega)]

/-- **An `EREC` allocation followed by a write of `EREC` only** (a copy, `erCopy_get`'s first
three facts) is a `MemFrame [EREC] [129]`. -/
theorem erAllocCopy_frame {m m2 : Mem} {l : Word}
    (hA : ∀ b : TieredArray, b ≠ ↑EREC → m2.arr64 b = (erAllocMem m l).arr64 b)
    (hS : (m2.arr64 EREC).size = (m.arr64 EREC).size) :
    MemFrame [EREC] [129] m m2 := by
  sorry

/-- **`block_caps_at_er_copy` is its model `capsErCopyW`** (generated). -/
l_model blockCapsAtErCopy_spec (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hc : p.lookup "block_caps_at_er_copy_go" = some blockCapsAtErCopyGo)
    (hp : p.lookup "block_caps_at_er_copy" = some blockCapsAtErCopy)
  fns [hp ↦ capsErCopyW]
  specs [erecAlloc_specW p ha n, ieCopy_spec p hc n]
  grind [ind_grind]

/-- **What `block_caps_at_er_copy` builds**: a fresh `EREC` slice at the old `EREC` top holding the
`IW` slice `(o, l)`; the hypotheses `StageR.erec` asks for: `EREC` and `CTL[129]` the only changes,
the old records unchanged, the top moved by `l`, `IW` untouched. -/
theorem capsErCopyW_post {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : capsErCopyW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hEs : (m.arr64 EREC).size < 2 ^ 64) (hc : 129 < (m.arr64 CTL).size)
    (hsrc : o.toNat + l.toNat ≤ (m.arr64 IW).size) :
    r = [rdW (m.arr64 CTL) 129, l] ∧ (rdW (m.arr64 CTL) 129).toNat = erTop m ∧
    (∀ j < l.toNat, (m'.arr64 EREC)[erTop m + j]? = (m.arr64 IW)[o.toNat + j]?) ∧
    MemFrame [EREC] [129] m m' ∧ (∀ i < erTop m, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    erTop m' = erTop m + l.toNat ∧ erTop m + l.toNat ≤ (m'.arr64 EREC).size ∧
    m'.arr64 IW = m.arr64 IW := by
  sorry

/-- **`block_caps_at_er_copy` copies an `IW` slice into fresh `EREC` words** (`IIndCaps`'s `all` and
`ctors` fields): the new `EREC` slice at the old top holds the `IW` slice; everything the stage
relation needs from a writer of `EREC` (`StageR.erec`) is stated. -/
@[refines_part ConRon.Arena.blockCapsAt "an IW slice copied into fresh EREC words"]
theorem blockCapsAtErCopy_refines (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hc : p.lookup "block_caps_at_er_copy_go" = some blockCapsAtErCopyGo)
    (hp : p.lookup "block_caps_at_er_copy" = some blockCapsAtErCopy) (n : Nat) (s₀ : St)
    (o l : Word) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hEs : (s₀.mem.arr64 EREC).size < 2 ^ 64)
    (hcl : 129 < (s₀.mem.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ (s₀.mem.arr64 IW).size) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_caps_at_er_copy" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [rdW (s₀.mem.arr64 CTL) 129, l] ∧
      (rdW (s₀.mem.arr64 CTL) 129).toNat = erTop s₀.mem ∧
      (∀ j < l.toNat, (s'.mem.arr64 EREC)[erTop s₀.mem + j]? = (s₀.mem.arr64 IW)[o.toNat + j]?) ∧
      MemFrame [EREC] [129] s₀.mem s'.mem ∧
      (∀ i < erTop s₀.mem, (s'.mem.arr64 EREC)[i]? = (s₀.mem.arr64 EREC)[i]?) ∧
      erTop s'.mem = erTop s₀.mem + l.toNat ∧ erTop s₀.mem + l.toNat ≤ (s'.mem.arr64 EREC).size ∧
      s'.mem.arr64 IW = s₀.mem.arr64 IW; ⊤⦄ := by
  refine triple_post (blockCapsAtErCopy_spec p ha hc hp n s₀ o l) ?_
  rintro r s' ⟨hl, hm⟩
  exact ⟨hl, capsErCopyW_post hm hsz hEs hcl hsrc⟩

/-! ## `(kinds, eidx)` records -/

/-- A `(kinds, eidx)` record: the kinds list at words `0, 1` and the handle at word `2`. -/
def decKE (m : Mem) (v : Nat) : Option (List NestFieldKind × EIdx) := do
  pure (← decAt m (decKL m) v, ← iwH m (v + 2))

end L.Ind

end
