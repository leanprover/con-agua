import ConAgua.Arena.IndPartsSpec6
import ConAgua.Arena.IndInstallSpec
import ConAgua.Arena.IndMaster

/-!
# Refinements of `IndInstall`, part 2 (lane `indproofs`, helper `install`)

The leaves of `BlockInstall.lean`'s L translation: `check_block_positivity_init`,
`block_caps_ctor_names`, `block_caps_at_er_copy`, `check_block_inds_cv_tas`,
`check_block_positivity_member`.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

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
    simp only [decNS, decAt, decPL, iwN, nat?, iwA]
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
  have htl : iwTop m < 2 ^ 64 := UInt64.toNat_lt _
  simp only [ctorNamesW] at h
  cases hal : allocW m l with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  obtain ⟨hq', hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  cases hcp : nameCopyW (n - 1) m1 q o l with
  | none => simp [hcp] at h
  | some m2 =>
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq' hm1
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hIW := allocMem_IW m l
  have hEE : (allocMem m l).arr64 EREC = m.arr64 EREC := by
    simp only [allocMem]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hptr' : ∀ j < l.toNat,
      (rdW ((allocMem m l).arr64 IW) (UInt64.ofNat (o.toNat + j))).toNat < q.toNat := by
    intro j hj
    obtain ⟨v, a, hv, hvb, -, -⟩ := hcv j hj
    obtain ⟨hv', -⟩ := iwN_rdW hv (by simp only [iwTop, hqq] at hsrc; omega)
    rw [hIW, hv']
    simp only [iwTop, hqq] at hvb
    rw [UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]; exact hvb
  obtain ⟨hA, hS, hW, hG⟩ := nameCopyW_get (n - 1) _ _ _ _ _ hcp
    (by simp only [iwTop, hqq] at hsrc; omega)
    (by rw [hIW]; exact hroom) (by rw [hIW]; exact hsz)
    hptr'
  rw [hIW] at hS hG
  rw [hEE] at hG
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m _).trans (copy_frame hA (by rw [hS, hIW]) hW)
  have htop : rdW (m2.arr64 CTL) 200 = q + l := by
    rw [hA CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + l).toNat = q.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  refine ⟨rfl, ?_, ?_, hfr, ?_⟩
  · have := decHL_of_get m2 (cvs.map (·.name)) q.toNat (fun j hj => by
      have hj' : j < l.toNat := by simpa [hlen] using hj
      obtain ⟨v, a, hv, hvb, hva, hcv'⟩ := hcv j hj'
      have hGj := hG (q.toNat + j)
      rw [if_pos (by omega)] at hGj
      have e2 : q.toNat + j - q.toNat = j := by omega
      rw [e2] at hGj
      obtain ⟨hv', -⟩ := iwN_rdW hv (by simp only [iwTop, hqq] at hsrc; omega)
      rw [hv'] at hGj
      obtain ⟨hva', hab⟩ := iwN_rdW hva (by omega)
      rw [hva'] at hGj
      simp only [decCVp, decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcv'
      obtain ⟨nm, hnm, lv, -, ce, -, hcvT⟩ := hcv'
      have hnmE : nm = (cvs[j]).name := by rw [← hcvT]
      obtain ⟨w, hw, hwl', hnm'⟩ : ∃ w, (m.arr64 EREC)[a]? = some w ∧ w.toNat < 2 ^ 32 ∧ decI w = nm := by
        cases hw : (m.arr64 EREC)[a]? with
        | none => simp [hd?, erA, hw] at hnm
        | some w =>
          by_cases hwl : w.toNat < 2 ^ 32
          · refine ⟨w, rfl, hwl, ?_⟩
            simp [hd?, erA, hw, hwl] at hnm
            simp [hnm]
          · simp [hd?, erA, hw, hwl] at hnm
      have hrd : rdW (m.arr64 EREC) (UInt64.ofNat a) = w := by
        have : (UInt64.ofNat a).toNat = a := by simp; omega
        simp [rdW, this, hw]
      rw [hrd] at hGj
      have hnmj : (cvs.map (·.name))[j]'(by simpa [hlen] using hj) = nm := by
        simp [List.getElem_map, hnmE]
      rw [hnmj]
      simp only [iwH, hd?, iwA, hGj, hwl', if_true, Option.bind_some, hnm']
      simp [hwl', hnm'])
    simpa [hlen] using this
  · refine iwGrow_of_frame hfr (N := l) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hG, if_neg (by omega)]
  · simp only [iwTop, htop, hsum]

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

end L.Ind
