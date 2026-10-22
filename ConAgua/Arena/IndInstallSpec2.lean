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

/-! ## `check_block_inds_cv_tas` -/

/-- The model of `check_block_inds_cv_tas_go`. -/
def cvGoW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, d, s, l =>
    if l = 0 then some m
    else cvGoW n (m.set64 IW d (rdW (m.arr64 IW) (rdW (m.arr64 IW) s))) (d + 1) (s + 1) (l - 1)

section arms
variable (n : Nat) (m : Mem) (d s l : Word)
theorem cvGoW_nil (hl : l = 0) : cvGoW (n + 1) m d s l = some m := by simp [cvGoW, hl]
theorem cvGoW_step (hl : l ≠ 0) :
    cvGoW (n + 1) m d s l =
      cvGoW n (m.set64 IW d (rdW (m.arr64 IW) (rdW (m.arr64 IW) s))) (d + 1) (s + 1) (l - 1) := by
  simp [cvGoW, hl]
end arms

grind_pattern [ind_grind] cvGoW_nil => cvGoW (n + 1) m d s l
grind_pattern [ind_grind] cvGoW_step => cvGoW (n + 1) m d s l

theorem checkBlockIndsCvTasGo_spec (p : Prog)
    (hp : p.lookup "check_block_inds_cv_tas_go" = some checkBlockIndsCvTasGo) (n : Nat) :
    ∀ (s₀ : St) (d s l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_inds_cv_tas_go" [d, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ cvGoW n s₀.mem d s l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ d s l; rw [invoke_eq _ hp]; simp only [callFn, checkBlockIndsCvTasGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ d s l
    rw [invoke_eq _ hp]
    simp only [callFn, checkBlockIndsCvTasGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 20)

/-- **What `check_block_inds_cv_tas_go` leaves.** -/
theorem cvGoW_get (n : Nat) : ∀ (m m' : Mem) (d s l : Word), cvGoW n m d s l = some m' →
    s.toNat + l.toNat ≤ d.toNat → d.toNat + l.toNat ≤ (m.arr64 IW).size →
    (m.arr64 IW).size < 2 ^ 64 →
    (∀ j < l.toNat, (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + j))).toNat < d.toNat) →
    (∀ b, b ≠ IW → m'.arr64 b = m.arr64 b) ∧ (m'.arr64 IW).size = (m.arr64 IW).size ∧
    m'.words.size = m.words.size ∧
    ∀ i, (m'.arr64 IW)[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + l.toNat
      then some (rdW (m.arr64 IW) (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + (i - d.toNat)))))
      else (m.arr64 IW)[i]? := by
  induction n with
  | zero => intro m m' d s l h; simp [cvGoW] at h
  | succ n ih =>
    intro m m' d s l h hsd hd hsz hptr
    by_cases hl : l = 0
    · rw [cvGoW_nil n m d s l hl] at h
      cases h
      subst hl
      refine ⟨fun _ _ => rfl, rfl, rfl, fun i => ?_⟩
      have : ¬ (d.toNat ≤ i ∧ i < d.toNat + (0 : Word).toNat) := by
        simp only [UInt64.toNat_zero]; omega
      simp only [this, if_false]
    · rw [cvGoW_step n m d s l hl] at h
      have hl0 : 0 < l.toNat := by
        have : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      have hl1 : (l - 1).toNat = l.toNat - 1 := by rw [UInt64.toNat_sub]; simp; omega
      have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hs1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hslt : s.toNat < (m.arr64 IW).size := by omega
      have hdlt : d.toNat < (m.arr64 IW).size := by omega
      have hp0 : (rdW (m.arr64 IW) s).toNat < d.toNat := by
        have := hptr 0 hl0; simpa using this
      obtain ⟨v, hv⟩ : ∃ v : Word, v = rdW (m.arr64 IW) (rdW (m.arr64 IW) s) := ⟨_, rfl⟩
      rw [← hv] at h
      obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.set64 IW d v := ⟨_, rfl⟩
      rw [← hm1] at h
      have hsz1 : (m1.arr64 IW).size = (m.arr64 IW).size := by
        rw [hm1, Mem.arr64_set64_same]; simp
      have hm1get : ∀ i, (m1.arr64 IW)[i]? = if i = d.toNat then some v else (m.arr64 IW)[i]? := by
        intro i
        rw [hm1, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        by_cases hi : d.toNat = i
        · subst hi; simp only [hdlt, true_and, if_true]
        · simp [hi, Ne.symm hi]
      have hrd : ∀ x : Word, x.toNat ≠ d.toNat → rdW (m1.arr64 IW) x = rdW (m.arr64 IW) x := by
        intro x hx; rw [hm1]; exact rdW_set64_IW_ne m d v x hx
      have hidx : ∀ k, s.toNat + k < 2 ^ 64 → (UInt64.ofNat (s.toNat + k)).toNat = s.toNat + k :=
        fun k hk => UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hk)
      have hptr1 : ∀ j < (l - 1).toNat,
          (rdW (m1.arr64 IW) (UInt64.ofNat ((s + 1).toNat + j))).toNat < (d + 1).toNat := by
        intro j hj
        have hj' : j + 1 < l.toNat := by rw [hl1] at hj; omega
        have hbase := hptr (j + 1) hj'
        have e1 : (s + 1).toNat + j = s.toNat + (j + 1) := by omega
        rw [e1, hrd _ (by rw [hidx _ (by omega)]; omega), hd1]; omega
      obtain ⟨hA, hS, hW, hG⟩ := ih m1 m' (d + 1) (s + 1) (l - 1) h
        (by rw [hs1, hd1, hl1]; omega) (by rw [hd1, hl1, hsz1]; omega) (by rw [hsz1]; exact hsz)
        hptr1
      refine ⟨fun b hb => (hA b hb).trans ?_, hS.trans hsz1, hW.trans ?_, fun i => ?_⟩
      · rw [hm1, Mem.arr64_set64_ne _ _ _ _ _ hb]
      · rw [hm1]; exact Mem.words_size_set64 _ _ _ _
      · rw [hG i, hd1, hl1, hs1]
        by_cases hi : d.toNat ≤ i ∧ i < d.toNat + l.toNat
        · rw [if_pos hi]
          by_cases hid : i = d.toNat
          · subst hid
            have hnot : ¬ (d.toNat + 1 ≤ d.toNat ∧ d.toNat < d.toNat + 1 + (l.toNat - 1)) := by omega
            rw [if_neg hnot]
            have e3 : s.toNat + (d.toNat - d.toNat) = s.toNat := by omega
            rw [e3, ofNat_toNat_word, hm1get, if_pos rfl, hv]
          · have h2 : d.toNat + 1 ≤ i ∧ i < d.toNat + 1 + (l.toNat - 1) := by omega
            rw [if_pos h2]
            have e4 : s.toNat + 1 + (i - (d.toNat + 1)) = s.toNat + (i - d.toNat) := by omega
            rw [e4]
            have hb2 := hptr (i - d.toNat) (by omega)
            have hi2 := hidx (i - d.toNat) (by omega)
            have e5 : rdW (m1.arr64 IW) (UInt64.ofNat (s.toNat + (i - d.toNat))) =
                rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + (i - d.toNat))) :=
              hrd _ (by rw [hi2]; omega)
            rw [e5, hrd _ (by omega)]
        · rw [if_neg hi, if_neg (by omega), hm1get, if_neg (by omega)]

/-- A pointer slice whose words decode one by one decodes as the list. -/
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

/-- The model of `check_block_inds_cv_tas(cvTa0, restO, restL)` at the caller's fuel `n`. -/
def cvTasW (n : Nat) (m : Mem) (c0 ro rl : Word) : Option (List Word × Mem) :=
  match allocW m (rl + 1) with
  | none => none
  | some (q, m1) =>
    match cvGoW (n - 1) (m1.set64 IW q c0) (q + 1) ro rl with
    | none => none
    | some m2 => some ([q, rl + 1], m2)

theorem checkBlockIndsCvTas_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "check_block_inds_cv_tas_go" = some checkBlockIndsCvTasGo)
    (hp : p.lookup "check_block_inds_cv_tas" = some checkBlockIndsCvTas) (n : Nat) (s₀ : St)
    (c0 ro rl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_inds_cv_tas" [c0, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ cvTasW n s₀.mem c0 ro rl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockIndsCvTas]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hmod : ∀ q m1 m2, allocW s₀.mem (rl + 1) = some (q, m1) →
        cvGoW n (m1.set64 IW q c0) (q + 1) ro rl = some m2 →
        cvTasW (n + 1) s₀.mem c0 ro rl = some ([q, rl + 1], m2) := by
      intro q m1 m2 h1 h2
      simp [cvTasW, h1, h2]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n, checkBlockIndsCvTasGo_spec p hc n] <;>
      finish (gen := 20)

/-- **What `check_block_inds_cv_tas` builds**: `cvTa0 :: rest.map (·.1)`, a fresh `IW` slice of
`EREC` constant pointers. -/
theorem cvTasW_dec {n : Nat} {m m' : Mem} {c0 ro rl : Word} {r : List Word}
    (h : cvTasW n m c0 ro rl = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hrl : rl.toNat + 1 < 2 ^ 64)
    (hsrc : ro.toNat + rl.toNat ≤ iwTop m)
    (cv0 : IConstantVal) (hcv0 : decCVp m c0.toNat = some cv0)
    (cvs : List IConstantVal) (hlen : cvs.length = rl.toNat)
    (hcv : ∀ j (hj : j < rl.toNat), ∃ v a, iwN m (ro.toNat + j) = some v ∧ v < iwTop m ∧
      iwN m v = some a ∧ decCVp m a = some cvs[j]) :
    r = [rdW (m.arr64 CTL) 200, rl + 1] ∧
    decPL m' (decCVp m') (rdW (m.arr64 CTL) 200).toNat (rl.toNat + 1) = some (cv0 :: cvs) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
    (rdW (m.arr64 CTL) 200).toNat + (rl.toNat + 1) = iwTop m' := by
  have hrl1 : (rl + 1).toNat = rl.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  simp only [cvTasW] at h
  cases hal : allocW m (rl + 1) with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  obtain ⟨hq', hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  cases hcp : cvGoW (n - 1) (m1.set64 IW q c0) (q + 1) ro rl with
  | none => simp [hcp] at h
  | some m2 =>
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq' hm1
  rw [hrl1] at hroom
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hIW := allocMem_IW m (rl + 1)
  have hEE : (allocMem m (rl + 1)).arr64 EREC = m.arr64 EREC := by
    simp only [allocMem]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hqt : iwTop m = q.toNat := by simp only [iwTop, hqq]
  have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hqlt : q.toNat < (m.arr64 IW).size := by omega
  have hszA : (((allocMem m (rl + 1)).set64 IW q c0).arr64 IW).size = (m.arr64 IW).size := by
    rw [Mem.arr64_set64_same]; simp [hIW]
  have hAget : ∀ i, (((allocMem m (rl + 1)).set64 IW q c0).arr64 IW)[i]? =
      if i = q.toNat then some c0 else (m.arr64 IW)[i]? := by
    intro i
    rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hIW]
    by_cases hi : q.toNat = i
    · subst hi; simp [hqlt]
    · simp [hi, Ne.symm hi]
  have hrdA : ∀ x : Word, x.toNat ≠ q.toNat →
      rdW (((allocMem m (rl + 1)).set64 IW q c0).arr64 IW) x = rdW (m.arr64 IW) x := by
    intro x hx; rw [rdW_set64_IW_ne _ q c0 x hx, hIW]
  have hidx : ∀ k, ro.toNat + k < 2 ^ 64 → (UInt64.ofNat (ro.toNat + k)).toNat = ro.toNat + k :=
    fun k hk => UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hk)
  have hptr' : ∀ j < rl.toNat,
      (rdW (((allocMem m (rl + 1)).set64 IW q c0).arr64 IW) (UInt64.ofNat (ro.toNat + j))).toNat <
        (q + 1).toNat := by
    intro j hj
    obtain ⟨v, a, hv, hvb, -, -⟩ := hcv j hj
    obtain ⟨hv', -⟩ := iwN_rdW hv (by omega)
    rw [hrdA _ (by rw [hidx j (by omega)]; omega), hv', hq1]
    rw [UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]; omega
  obtain ⟨hA, hS, hW, hG⟩ := cvGoW_get (n - 1) _ _ _ _ _ hcp
    (by rw [hq1]; omega) (by rw [hq1, hszA]; omega) (by rw [hszA]; exact hsz) hptr'
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m _).trans ((set64IW_frame _ q c0).trans (copy_frame hA hS hW))
  have htop : rdW (m2.arr64 CTL) 200 = q + (rl + 1) := by
    rw [hA CTL (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + (rl + 1)).toNat = q.toNat + (rl.toNat + 1) := by
    rw [UInt64.toNat_add, hrl1]; simp; omega
  have hE2 : m2.arr64 EREC = m.arr64 EREC := by
    rw [hA EREC (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide), hEE]
  have hdec2 : decCVp m2 = decCVp m := by
    funext a; simp only [decCVp, erA, hE2]
  refine ⟨rfl, ?_, ?_, hfr, ?_⟩
  · have := decPL_of_get (m := m2) (decCVp m2) (cv0 :: cvs) q.toNat (fun j hj => by
      rw [hdec2]
      cases j with
      | zero =>
        have hg := hG q.toNat
        rw [if_neg (by omega), hAget, if_pos rfl] at hg
        refine ⟨c0.toNat, ?_, by simpa using hcv0⟩
        simp [iwN, nat?, iwA, hg]
      | succ j =>
        have hj' : j < rl.toNat := by simpa [hlen] using hj
        obtain ⟨v, a, hv, hvb, hva, hcv'⟩ := hcv j hj'
        have hGj := hG (q.toNat + (j + 1))
        rw [if_pos (by rw [hq1]; omega), hq1] at hGj
        have e2 : q.toNat + (j + 1) - (q.toNat + 1) = j := by omega
        rw [e2] at hGj
        obtain ⟨hv', -⟩ := iwN_rdW hv (by omega)
        obtain ⟨hva', hab⟩ := iwN_rdW hva (by omega)
        have e3 : rdW (((allocMem m (rl + 1)).set64 IW q c0).arr64 IW)
            (UInt64.ofNat (ro.toNat + j)) = UInt64.ofNat v := by
          rw [hrdA _ (by rw [hidx j (by omega)]; omega), hv']
        have e4 : rdW (((allocMem m (rl + 1)).set64 IW q c0).arr64 IW) (UInt64.ofNat v) =
            UInt64.ofNat a := by
          rw [hrdA _ (by rw [UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]; omega), hva']
        rw [e3, e4] at hGj
        refine ⟨a, ?_, by simpa using hcv'⟩
        simp only [iwN, nat?, iwA, hGj, Option.map_some]
        congr 1
        exact UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega))
    simpa [hlen] using this
  · refine iwGrow_of_frame hfr (N := rl + 1) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq, hrl1]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hG, if_neg (by omega), hAget, if_neg (by omega)]
  · simp only [iwTop, htop, hsum]

/-- The constant at the first word of a record pointer (`rp ↦ rp.1` of a `(cv, _)` pair). -/
def decCV1 (m : Mem) (rp : Nat) : Option IConstantVal := do decCVp m (← iwN m rp)

/-- **`check_block_inds_cv_tas` is `cvTa₀ :: cvs.map (·.1)`** of `checkBlockInds`: the new `IW`
slice of `EREC` constant pointers decodes as `cv0 :: rest`, where `rest` is the formers' constants
read off the first words of the `(cv, _)` pointers of `(restO, restL)`. -/
@[refines_part ConRon.Arena.checkBlockInds "the formers' constants list cvTas"]
theorem checkBlockIndsCvTas_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "check_block_inds_cv_tas_go" = some checkBlockIndsCvTasGo)
    (hp : p.lookup "check_block_inds_cv_tas" = some checkBlockIndsCvTas) (n : Nat) (s₀ : St)
    (c0 ro rl : Word) (cv0 : IConstantVal) (rest : List IConstantVal)
    (hcv0 : decCVp s₀.mem c0.toNat = some cv0)
    (hrest : decPL s₀.mem (decCV1 s₀.mem) ro.toNat rl.toNat = some rest)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hcl : 200 < (s₀.mem.arr64 CTL).size)
    (hrl : rl.toNat + 1 < 2 ^ 64) (hsrc : ro.toNat + rl.toNat ≤ iwTop s₀.mem)
    (hptr : ∀ j v, j < rl.toNat → iwN s₀.mem (ro.toNat + j) = some v → v < iwTop s₀.mem) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_inds_cv_tas" [c0, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [rdW (s₀.mem.arr64 CTL) 200, rl + 1] ∧
      decPL s'.mem (decCVp s'.mem) (rdW (s₀.mem.arr64 CTL) 200).toNat (rl.toNat + 1) =
        some (cv0 :: rest) ∧
      IWGrow s₀.mem s'.mem ∧ MemFrame [IW] [200] s₀.mem s'.mem ∧
      (rdW (s₀.mem.arr64 CTL) 200).toNat + (rl.toNat + 1) = iwTop s'.mem; ⊤⦄ := by
  refine triple_post (checkBlockIndsCvTas_spec p ha hc hp n s₀ c0 ro rl) ?_
  rintro r s' ⟨hl, hm⟩
  have hlen := decPL_length _ hrest
  exact ⟨hl, cvTasW_dec hm hsz hcl hrl hsrc cv0 hcv0 rest hlen (fun j hj => by
    obtain ⟨v, y, hv, hy, hget⟩ := decPL_get rl.toNat ro.toNat rest hrest j hj
    have hj' : j < rest.length := by omega
    have hy' : rest[j] = y := by simpa [List.getElem?_eq_getElem hj'] using hget
    simp only [decCV1, bind, Option.bind_eq_some_iff] at hy
    obtain ⟨a, ha', hy2⟩ := hy
    exact ⟨v, a, hv, hptr j v hj hv, ha', by rw [hy']; exact hy2⟩)⟩

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
  induction n with
  | zero => intro s₀ d s l; rw [invoke_eq _ hp]; simp only [callFn, blockCapsAtErCopyGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ d s l
    rw [invoke_eq _ hp]
    simp only [callFn, blockCapsAtErCopyGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 20)


/-- **What an `IW → EREC` copy leaves**: every array but `EREC` as it was, `EREC` the same size, the
destination holding the `IW` source, the rest of `EREC` unchanged. -/
theorem ieCopyW_get (n : Nat) : ∀ (m m' : Mem) (d s l : Word), ieCopyW n m d s l = some m' →
    s.toNat + l.toNat ≤ (m.arr64 IW).size → (m.arr64 IW).size < 2 ^ 64 →
    d.toNat + l.toNat ≤ (m.arr64 EREC).size → (m.arr64 EREC).size < 2 ^ 64 →
    (∀ b, b ≠ EREC → m'.arr64 b = m.arr64 b) ∧ (m'.arr64 EREC).size = (m.arr64 EREC).size ∧
    m'.words.size = m.words.size ∧
    ∀ i, (m'.arr64 EREC)[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + l.toNat then (m.arr64 IW)[s.toNat + (i - d.toNat)]?
      else (m.arr64 EREC)[i]? := by
  induction n with
  | zero => intro m m' d s l h; simp [ieCopyW] at h
  | succ n ih =>
    intro m m' d s l h hs hE hd hsz
    by_cases hl : l = 0
    · rw [ieCopyW_nil n m d s l hl] at h
      cases h
      subst hl
      refine ⟨fun _ _ => rfl, rfl, rfl, fun i => ?_⟩
      have : ¬ (d.toNat ≤ i ∧ i < d.toNat + (0 : Word).toNat) := by
        simp only [UInt64.toNat_zero]; omega
      simp only [this, if_false]
    · rw [ieCopyW_step n m d s l hl] at h
      have hl0 : 0 < l.toNat := by
        have : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      have hl1 : (l - 1).toNat = l.toNat - 1 := by
        rw [UInt64.toNat_sub]; simp; omega
      have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hs1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hslt : s.toNat < (m.arr64 IW).size := by omega
      have hdlt : d.toNat < (m.arr64 EREC).size := by omega
      obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.set64 EREC d (rdW (m.arr64 IW) s) := ⟨_, rfl⟩
      rw [← hm1] at h
      have hsz1 : (m1.arr64 EREC).size = (m.arr64 EREC).size := by
        rw [hm1, Mem.arr64_set64_same]; simp
      have hE1 : m1.arr64 IW = m.arr64 IW := by
        rw [hm1, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
      have hget1 : ∀ i, (m1.arr64 EREC)[i]? = if i = d.toNat then (m.arr64 IW)[s.toNat]?
          else (m.arr64 EREC)[i]? := by
        intro i
        rw [hm1, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        by_cases hi : d.toNat = i
        · subst hi
          simp only [hdlt, true_and, if_true]
          simp [rdW, Array.getElem?_eq_getElem hslt]
        · simp [hi, Ne.symm hi]
      obtain ⟨hA, hS, hW, hG⟩ := ih m1 m' (d + 1) (s + 1) (l - 1) h
        (by rw [hs1, hl1, hE1]; omega) (by rw [hE1]; exact hE)
        (by rw [hd1, hl1, hsz1]; omega) (by rw [hsz1]; exact hsz)
      rw [hE1] at hG
      refine ⟨fun b hb => (hA b hb).trans ?_, hS.trans hsz1, hW.trans ?_, fun i => ?_⟩
      · rw [hm1, Mem.arr64_set64_ne _ _ _ _ _ hb]
      · rw [hm1]; exact Mem.words_size_set64 _ _ _ _
      · rw [hG i, hd1, hl1, hs1]
        by_cases hi : d.toNat ≤ i ∧ i < d.toNat + l.toNat
        · rw [if_pos hi]
          by_cases hid : i = d.toNat
          · subst hid
            have : ¬ (d.toNat + 1 ≤ d.toNat ∧ d.toNat < d.toNat + 1 + (l.toNat - 1)) := by omega
            rw [if_neg this, hget1, if_pos rfl]; simp
          · have h2 : d.toNat + 1 ≤ i ∧ i < d.toNat + 1 + (l.toNat - 1) := by omega
            rw [if_pos h2]
            congr 1; omega
        · rw [if_neg hi, if_neg (by omega), hget1, if_neg (by omega)]


/-- The model of `block_caps_at_er_copy(o, l)` at the caller's fuel `n` (the copy runs at `n - 1`). -/
def capsErCopyW (n : Nat) (m : Mem) (o l : Word) : Option (List Word × Mem) :=
  match erAllocW m l with
  | none => none
  | some (q, m1) =>
    match ieCopyW (n - 1) m1 q o l with
    | none => none
    | some m2 => some ([q, l], m2)

theorem blockCapsAtErCopy_spec (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hc : p.lookup "block_caps_at_er_copy_go" = some blockCapsAtErCopyGo)
    (hp : p.lookup "block_caps_at_er_copy" = some blockCapsAtErCopy) (n : Nat) (s₀ : St)
    (o l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_caps_at_er_copy" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ capsErCopyW n s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockCapsAtErCopy]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hmod : ∀ q m1 m2, erAllocW s₀.mem l = some (q, m1) → ieCopyW n m1 q o l = some m2 →
        capsErCopyW (n + 1) s₀.mem o l = some ([q, l], m2) := by
      intro q m1 m2 h1 h2
      simp [capsErCopyW, h1, h2]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        erecAlloc_specW p ha n, ieCopy_spec p hc n] <;>
      finish (gen := 20)

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
  simp only [capsErCopyW] at h
  cases hal : erAllocW m l with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  simp only [hal] at h
  cases hcp : ieCopyW (n - 1) m1 q o l with
  | none => simp [hcp] at h
  | some m2 =>
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [erAllocW] at hal
  by_cases h1 : m.len64 EREC < rdW (m.arr64 CTL) 129
  · simp [h1] at hal
  by_cases h2 : m.len64 EREC - rdW (m.arr64 CTL) 129 < l
  · simp [h1, h2] at hal
  simp only [h1, h2, if_false, Option.some.injEq, Prod.mk.injEq] at hal
  obtain ⟨rfl, rfl⟩ := hal
  have hlen : (m.len64 EREC).toNat = (m.arr64 EREC).size := by simp [Mem.len64]; omega
  have hq : (rdW (m.arr64 CTL) 129).toNat ≤ (m.arr64 EREC).size := by
    have : ¬ (m.len64 EREC).toNat < (rdW (m.arr64 CTL) 129).toNat := h1
    omega
  have hroom : (rdW (m.arr64 CTL) 129).toNat + l.toNat ≤ (m.arr64 EREC).size := by
    have : ¬ (m.len64 EREC - rdW (m.arr64 CTL) 129).toNat < l.toNat := h2
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)] at this
    omega
  generalize hqq : rdW (m.arr64 CTL) 129 = q at *
  have hE : (erAllocMem m l).arr64 EREC = m.arr64 EREC := by
    simp only [erAllocMem]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hI : (erAllocMem m l).arr64 IW = m.arr64 IW := by
    simp only [erAllocMem]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  obtain ⟨hA, hS, hW, hG⟩ := ieCopyW_get (n - 1) _ _ _ _ _ hcp
    (by rw [hI]; exact hsrc) (by rw [hI]; exact hsz) (by rw [hE]; exact hroom) (by rw [hE]; exact hEs)
  rw [hE] at hS hG
  rw [hI] at hG
  have hCTL : m2.arr64 CTL = (erAllocMem m l).arr64 CTL := hA CTL (by decide)
  have hf : MemFrame [EREC] [129] m m2 := by
    refine ⟨fun b hb hcb => ?_, fun x hx => ?_, fun b => ?_, ?_⟩
    · rw [hA b (by simpa using hb), erAllocMem, Mem.arr64_set64_ne _ _ _ _ _ hcb]
    · rw [hCTL]; simp only [erAllocMem, rdW_set64]
      have hx' : ¬ (x = 129) := by simpa using hx
      simp [show (129 : Word) ≠ x from fun e => hx' e.symm]
    · by_cases hb : b = EREC
      · subst hb; exact hS
      · rw [hA b hb]; simp only [erAllocMem]
        by_cases hbc : b = CTL
        · subst hbc; exact size_set64 _ _ _ _ _
        · rw [Mem.arr64_set64_ne _ _ _ _ _ hbc]
    · rw [hW]; exact Mem.words_size_set64 _ _ _ _
  have hqe : erTop m = q.toNat := by simp only [erTop, hqq]
  have h129 : (129 : Word).toNat < (m.arr64 CTL).size := by simp; omega
  refine ⟨rfl, hqe.symm, fun j hj => ?_, hf, fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [hG, hqe, if_pos (by omega)]; congr 2; omega
  · rw [hG, if_neg (by omega)]
  · simp only [erTop]
    rw [hCTL]; simp only [erAllocMem, rdW_set64]
    rw [if_pos ⟨trivial, trivial, h129⟩, hqq, UInt64.toNat_add]
    simp; omega
  · rw [hqe, hS]; omega
  · rw [hA IW (by decide), hI]

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

/-! ## `check_block_positivity_member` -/

theorem rec2Mem_size (m : Mem) (a b : Word) :
    ((rec2Mem m a b).arr64 IW).size = (m.arr64 IW).size := by
  simp only [rec2Mem, Mem.arr64_set64_same, allocMem, Array.set!_eq_setIfInBounds,
    Array.size_setIfInBounds]
  rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]

/-- One step of `check_block_positivity_member_go`: the `rec2` record `[IW[e], IW[e+1]]` at the
top, its pointer stored at `kd`, `IW[e + 2]` stored at `nd`. -/
def pmStep (m : Mem) (kd nd s : Word) : Mem :=
  let e := rdW (m.arr64 IW) s
  let m1 := rec2Mem m (rdW (m.arr64 IW) e) (rdW (m.arr64 IW) (e + 1))
  let m2 := m1.set64 IW kd (rdW (m.arr64 CTL) 200)
  m2.set64 IW nd (rdW (m2.arr64 IW) (e + 2))

/-- The model of `check_block_positivity_member_go` (each step needs room for the `rec2` record). -/
def pmGoW : Nat → Mem → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _ => none
  | n + 1, m, kd, nd, s, l =>
    if l = 0 then some m
    else if (rdW (m.arr64 CTL) 200).toNat + 2 ≤ (m.arr64 IW).size then
      pmGoW n (pmStep m kd nd s) (kd + 1) (nd + 1) (s + 1) (l - 1)
    else none

section arms
variable (n : Nat) (m : Mem) (kd nd s l : Word)
theorem pmGoW_nil (hl : l = 0) : pmGoW (n + 1) m kd nd s l = some m := by simp [pmGoW, hl]
theorem pmGoW_step (hl : l ≠ 0) (hr : (rdW (m.arr64 CTL) 200).toNat + 2 ≤ (m.arr64 IW).size) :
    pmGoW (n + 1) m kd nd s l = pmGoW n (pmStep m kd nd s) (kd + 1) (nd + 1) (s + 1) (l - 1) := by
  simp [pmGoW, hl, hr]
theorem pmGoW_full (hl : l ≠ 0) (hr : ¬ (rdW (m.arr64 CTL) 200).toNat + 2 ≤ (m.arr64 IW).size) :
    pmGoW (n + 1) m kd nd s l = none := by
  simp [pmGoW, hl, hr]
end arms

grind_pattern [ind_grind] pmGoW_nil => pmGoW (n + 1) m kd nd s l
grind_pattern [ind_grind] pmGoW_step => pmGoW (n + 1) m kd nd s l
grind_pattern [ind_grind] pmGoW_full => pmGoW (n + 1) m kd nd s l

theorem checkBlockPositivityMemberGo_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (h2 : p.lookup "rec2" = some rec2)
    (hp : p.lookup "check_block_positivity_member_go" = some checkBlockPositivityMemberGo)
    (n : Nat) :
    ∀ (s₀ : St) (kd nd s l : Word), (s₀.mem.arr64 IW).size < 2 ^ 64 →
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_positivity_member_go" [kd, nd, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ pmGoW n s₀.mem kd nd s l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ kd nd s l hsz; rw [invoke_eq _ hp]
    simp only [callFn, checkBlockPositivityMemberGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ kd nd s l hsz
    rw [invoke_eq _ hp]
    simp only [callFn, checkBlockPositivityMemberGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        rec2_spec p ha h2 n, ih] <;>
      finish (gen := 20) [pmStep, rec2Mem_size]

theorem rdW_eq_of_get {a : Array Word} {i : Word} {w : Word} (h : a[i.toNat]? = some w) :
    rdW a i = w := by simp [rdW, h]

theorem rdW_of_get_eq {a b : Array Word} {x y : Word} (h : a[x.toNat]? = b[y.toNat]?) :
    rdW a x = rdW b y := by simp only [rdW, h]

/-- **One step of `check_block_positivity_member_go`**, position by position. -/
theorem pmStep_get (m : Mem) (kd nd s : Word) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hroom : iwTop m + 2 ≤ (m.arr64 IW).size)
    (hkd : kd.toNat < iwTop m) (hnd : nd.toNat < iwTop m) (hne : kd.toNat ≠ nd.toNat)
    (E : Word) (hE : rdW (m.arr64 IW) s = E) (he : E.toNat + 3 ≤ kd.toNat) :
    MemFrame [IW] [200] m (pmStep m kd nd s) ∧
    rdW ((pmStep m kd nd s).arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + 2 ∧
    ∀ i, ((pmStep m kd nd s).arr64 IW)[i]? =
      if i = nd.toNat then (m.arr64 IW)[E.toNat + 2]?
      else if i = kd.toNat then some (rdW (m.arr64 CTL) 200)
      else if i = iwTop m then (m.arr64 IW)[E.toNat]?
      else if i = iwTop m + 1 then (m.arr64 IW)[E.toNat + 1]?
      else (m.arr64 IW)[i]? := by
  have hqT : (rdW (m.arr64 CTL) 200).toNat = iwTop m := rfl
  have hE1 : (E + 1).toNat = E.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have hE2 : (E + 2).toNat = E.toNat + 2 := by
    rw [UInt64.toNat_add]; simp; omega
  have hkdsz : kd.toNat < (m.arr64 IW).size := by omega
  have hndsz : nd.toNat < (m.arr64 IW).size := by omega
  have hEsz : E.toNat + 2 < (m.arr64 IW).size := by omega
  generalize ha : rdW (m.arr64 IW) E = a
  generalize hb : rdW (m.arr64 IW) (E + 1) = b
  have hm1 : rec2Mem m a b = wrIW (allocMem m 2) (rdW (m.arr64 CTL) 200) [a, b] := rec2Mem_eq m a b
  have hIW : (allocMem m 2).arr64 IW = m.arr64 IW := allocMem_IW m 2
  have hg1 : ∀ i, ((rec2Mem m a b).arr64 IW)[i]? =
      if iwTop m ≤ i ∧ i < iwTop m + 2 then [a, b][i - iwTop m]? else (m.arr64 IW)[i]? := by
    intro i
    rw [hm1, wrIW_get _ _ _ _ (by rw [hIW]; simp; omega) (by rw [hIW]; exact hsz), hIW, hqT]
    simp
  have hsz1 : ((rec2Mem m a b).arr64 IW).size = (m.arr64 IW).size := rec2Mem_size m a b
  have hf1 : MemFrame [IW] [200] m (rec2Mem m a b) := rec2Mem_frame m a b
  have hr1 : ∀ x : Word, x.toNat < iwTop m → rdW ((rec2Mem m a b).arr64 IW) x = rdW (m.arr64 IW) x := by
    intro x hx
    have := hg1 x.toNat
    rw [if_neg (by omega)] at this
    exact rdW_of_get_eq this
  have hf2 : MemFrame [IW] [200] (rec2Mem m a b)
      ((rec2Mem m a b).set64 IW kd (rdW (m.arr64 CTL) 200)) := set64IW_frame _ _ _
  have hg2 : ∀ i, (((rec2Mem m a b).set64 IW kd (rdW (m.arr64 CTL) 200)).arr64 IW)[i]? =
      if i = kd.toNat then some (rdW (m.arr64 CTL) 200) else ((rec2Mem m a b).arr64 IW)[i]? := by
    intro i
    rw [set64IW_get, hsz1]
    by_cases hi : i = kd.toNat
    · simp [hi, hkdsz]
    · simp [hi]
  have hr2 : rdW (((rec2Mem m a b).set64 IW kd (rdW (m.arr64 CTL) 200)).arr64 IW) (E + 2) =
      rdW (m.arr64 IW) (E + 2) := by
    have := hg2 (E + 2).toNat
    rw [if_neg (by omega), hg1, if_neg (by omega)] at this
    exact rdW_of_get_eq this
  have hpm : pmStep m kd nd s =
      (((rec2Mem m a b).set64 IW kd (rdW (m.arr64 CTL) 200)).set64 IW nd
        (rdW (((rec2Mem m a b).set64 IW kd (rdW (m.arr64 CTL) 200)).arr64 IW) (E + 2))) := by
    unfold pmStep; simp only [hE, ha, hb]
  rw [hpm]
  refine ⟨?_, ?_, fun i => ?_⟩
  · exact hf1.trans (hf2.trans (set64IW_frame _ _ _))
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    simp only [rec2Mem]
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    exact allocMem_top m 2 hc
  · have hszA : (((rec2Mem m a b).set64 IW kd (rdW (m.arr64 CTL) 200)).arr64 IW).size =
        (m.arr64 IW).size := by rw [← hsz1]; exact size_set64 _ _ _ _ _
    have hrd_get : ∀ x : Word, x.toNat < (m.arr64 IW).size →
        (m.arr64 IW)[x.toNat]? = some (rdW (m.arr64 IW) x) := by
      intro x hx; simp [rdW, Array.getElem?_eq_getElem hx]
    have hv : (m.arr64 IW)[E.toNat + 2]? = some (rdW (m.arr64 IW) (E + 2)) := by
      have := hrd_get (E + 2) (by omega); rwa [hE2] at this
    have hEa : (m.arr64 IW)[E.toNat]? = some a := by
      have := hrd_get E (by omega); rw [ha] at this; exact this
    have hEb : (m.arr64 IW)[E.toNat + 1]? = some b := by
      have := hrd_get (E + 1) (by omega); rw [hb, hE1] at this; exact this
    rw [set64IW_get, hszA, hr2, hg2 i, hg1 i]
    have n1 : iwTop m ≠ nd.toNat := by omega
    have n2 : iwTop m ≠ kd.toNat := by omega
    have n3 : iwTop m + 1 ≠ nd.toNat := by omega
    have n4 : iwTop m + 1 ≠ kd.toNat := by omega
    by_cases h1 : i = nd.toNat
    · simp [h1, hndsz, hv]
    · by_cases h2 : i = kd.toNat
      · simp [h1, h2, hne]
      · by_cases h3 : i = iwTop m
        · simp [h1, h2, h3, hEa, n1, n2]
        · by_cases h4 : i = iwTop m + 1
          · simp [h1, h2, h3, h4, hEb, n3, n4]
          · simp [h1, h2, h3, h4]
            intro h5 h6; omega

/-- **What `check_block_positivity_member_go` leaves**: the pointers to the fresh `[off, len]`
records at `kd + j`, those records (copies of the first two words of `IW[s + j]`) at the old top
`+ 2 j`, the third words at `nd + j`, everything else below the old top unchanged. -/
theorem pmGoW_get (n : Nat) : ∀ (m m' : Mem) (kd nd s l : Word), pmGoW n m kd nd s l = some m' →
    (m.arr64 IW).size < 2 ^ 64 → 200 < (m.arr64 CTL).size →
    s.toNat + l.toNat ≤ kd.toNat → kd.toNat + l.toNat ≤ nd.toNat → nd.toNat + l.toNat ≤ iwTop m →
    iwTop m ≤ (m.arr64 IW).size →
    (∀ j < l.toNat, (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + j))).toNat + 3 ≤ kd.toNat) →
    MemFrame [IW] [200] m m' ∧
    rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + UInt64.ofNat (2 * l.toNat) ∧
    iwTop m + 2 * l.toNat ≤ (m.arr64 IW).size ∧
    (∀ j < l.toNat, (m'.arr64 IW)[kd.toNat + j]? = some (UInt64.ofNat (iwTop m + 2 * j))) ∧
    (∀ j < l.toNat,
      (m'.arr64 IW)[iwTop m + 2 * j]? =
        (m.arr64 IW)[(rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + j))).toNat]? ∧
      (m'.arr64 IW)[iwTop m + 2 * j + 1]? =
        (m.arr64 IW)[(rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + j))).toNat + 1]?) ∧
    (∀ j < l.toNat, (m'.arr64 IW)[nd.toNat + j]? =
      (m.arr64 IW)[(rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + j))).toNat + 2]?) ∧
    (∀ i < iwTop m, ¬ (kd.toNat ≤ i ∧ i < kd.toNat + l.toNat) →
      ¬ (nd.toNat ≤ i ∧ i < nd.toNat + l.toNat) → (m'.arr64 IW)[i]? = (m.arr64 IW)[i]?) := by
  induction n with
  | zero => intro m m' kd nd s l h; simp [pmGoW] at h
  | succ n ih =>
    intro m m' kd nd s l h hsz hc hs hkn hnT hT hE
    by_cases hl : l = 0
    · rw [pmGoW_nil n m kd nd s l hl] at h
      cases h
      subst hl
      refine ⟨MemFrame.refl _ _ _, by simp, by simpa using hT, fun j hj => ?_, fun j hj => ?_,
        fun j hj => ?_, fun i _ _ _ => rfl⟩ <;> simp at hj
    · have hl0 : 1 ≤ l.toNat := by
        rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl
        · omega
      by_cases hr : (rdW (m.arr64 CTL) 200).toNat + 2 ≤ (m.arr64 IW).size
      case neg => rw [pmGoW_full n m kd nd s l hl hr] at h; simp at h
      rw [pmGoW_step n m kd nd s l hl hr] at h
      have hr' : iwTop m + 2 ≤ (m.arr64 IW).size := hr
      have hl1 : (l - 1).toNat = l.toNat - 1 := by rw [UInt64.toNat_sub]; simp; omega
      have hkd1 : (kd + 1).toNat = kd.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hnd1 : (nd + 1).toNat = nd.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hs1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hE0 : (rdW (m.arr64 IW) s).toNat + 3 ≤ kd.toNat := by
        simpa using hE 0 (by omega)
      obtain ⟨hf, hCTL, hget⟩ := pmStep_get m kd nd s hsz hc hr' (by omega) (by omega) (by omega)
        _ rfl hE0
      have hsz1' : ((pmStep m kd nd s).arr64 IW).size = (m.arr64 IW).size := hf.2.2.1 IW
      have hsz1 : ((pmStep m kd nd s).arr64 IW).size < 2 ^ 64 := by rw [hsz1']; exact hsz
      have hc1 : 200 < ((pmStep m kd nd s).arr64 CTL).size := by rw [hf.2.2.1]; exact hc
      have hT1 : iwTop (pmStep m kd nd s) = iwTop m + 2 := by
        simp only [iwTop, hCTL, UInt64.toNat_add]; simp; omega
      -- the input reads, unchanged
      have hrd1 : ∀ x : Word, x.toNat < kd.toNat →
          rdW ((pmStep m kd nd s).arr64 IW) x = rdW (m.arr64 IW) x := by
        intro x hx
        apply rdW_of_get_eq
        rw [hget]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hidx : ∀ k, s.toNat + k < 2 ^ 64 → (UInt64.ofNat (s.toNat + k)).toNat = s.toNat + k :=
        fun k hk => UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hk)
      have hx : ∀ j, UInt64.ofNat ((s + 1).toNat + j) = UInt64.ofNat (s.toNat + (j + 1)) := by
        intro j; rw [hs1, show s.toNat + 1 + j = s.toNat + (j + 1) by omega]
      have hE' : ∀ j < (l - 1).toNat,
          (rdW ((pmStep m kd nd s).arr64 IW) (UInt64.ofNat ((s + 1).toNat + j))).toNat + 3 ≤
            (kd + 1).toNat := by
        intro j hj
        rw [hl1] at hj
        rw [hx j, hrd1 (UInt64.ofNat (s.toNat + (j + 1))) (by rw [hidx (j + 1) (by omega)]; omega), hkd1]
        have := hE (j + 1) (by omega); omega
      obtain ⟨hF, hC, hRm, hP1, hP2, hP3, hP4⟩ := ih _ m' (kd + 1) (nd + 1) (s + 1) (l - 1) h hsz1 hc1
        (by rw [hs1, hkd1, hl1]; omega) (by rw [hkd1, hnd1, hl1]; omega)
        (by rw [hnd1, hl1, hT1]; omega) (by rw [hT1, hsz1']; omega) hE'
      have hrdj : ∀ j, j < l.toNat - 1 →
          rdW ((pmStep m kd nd s).arr64 IW) (UInt64.ofNat ((s + 1).toNat + j)) =
            rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + (j + 1))) := by
        intro j hj
        rw [hx j, hrd1 (UInt64.ofNat (s.toNat + (j + 1))) (by rw [hidx (j + 1) (by omega)]; omega)]
      have hm1old : ∀ k, k < kd.toNat →
          ((pmStep m kd nd s).arr64 IW)[k]? = (m.arr64 IW)[k]? := by
        intro k hk
        rw [hget]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hP4' : ∀ i < iwTop m + 2, ¬ (kd.toNat + 1 ≤ i ∧ i < kd.toNat + 1 + (l.toNat - 1)) →
          ¬ (nd.toNat + 1 ≤ i ∧ i < nd.toNat + 1 + (l.toNat - 1)) →
          (m'.arr64 IW)[i]? = ((pmStep m kd nd s).arr64 IW)[i]? := by
        intro i hi h1 h2
        exact hP4 i (by rw [hT1]; exact hi) (by rw [hkd1, hl1]; exact h1) (by rw [hnd1, hl1]; exact h2)
      have hP1' : ∀ j < l.toNat - 1, (m'.arr64 IW)[kd.toNat + 1 + j]? =
          some (UInt64.ofNat (iwTop m + 2 + 2 * j)) := by
        intro j hj
        have := hP1 j (by omega)
        rw [hkd1, hT1] at this
        exact this
      have hP2' : ∀ j < l.toNat - 1,
          (m'.arr64 IW)[iwTop m + 2 + 2 * j]? =
            (m.arr64 IW)[(rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + (j + 1)))).toNat]? ∧
          (m'.arr64 IW)[iwTop m + 2 + 2 * j + 1]? =
            (m.arr64 IW)[(rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + (j + 1)))).toNat + 1]? := by
        intro j hj
        have := hP2 j (by omega)
        rw [hT1, hrdj j hj] at this
        have hb := hE (j + 1) (by omega)
        rw [hm1old _ (by omega), hm1old _ (by omega)] at this
        exact this
      have hP3' : ∀ j < l.toNat - 1, (m'.arr64 IW)[nd.toNat + 1 + j]? =
          (m.arr64 IW)[(rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + (j + 1)))).toNat + 2]? := by
        intro j hj
        have := hP3 j (by omega)
        rw [hnd1, hrdj j hj] at this
        have hb := hE (j + 1) (by omega)
        rw [hm1old _ (by omega)] at this
        exact this
      have hmT : iwTop m = (rdW (m.arr64 CTL) 200).toNat := rfl
      refine ⟨hf.trans hF, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hC, hCTL, hl1]
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat]
        simp
        omega
      · rw [hT1, hl1] at hRm; omega
      · intro j hj
        cases j with
        | zero =>
          have := hP4' kd.toNat (by omega) (by omega) (by omega)
          simp only [Nat.add_zero, Nat.mul_zero]
          rw [this, hget, if_neg (by omega), if_pos rfl]
          rw [← ofNat_toNat_word (rdW (m.arr64 CTL) 200)]; rfl
        | succ j =>
          have := hP1' j (by omega)
          rw [show kd.toNat + (j + 1) = kd.toNat + 1 + j by omega, this,
            show iwTop m + 2 + 2 * j = iwTop m + 2 * (j + 1) by omega]
      · intro j hj
        cases j with
        | zero =>
          have h1 := hP4' (iwTop m) (by omega) (by omega) (by omega)
          have h2 := hP4' (iwTop m + 1) (by omega) (by omega) (by omega)
          simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
          refine ⟨?_, ?_⟩
          · rw [h1, hget, if_neg (by omega), if_neg (by omega), if_pos rfl]
            simp only [ofNat_toNat_word]
          · rw [h2, hget, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
            simp only [ofNat_toNat_word]
        | succ j =>
          have := hP2' j (by omega)
          rw [show iwTop m + 2 * (j + 1) = iwTop m + 2 + 2 * j by omega,
            show s.toNat + (j + 1) = s.toNat + (j + 1) from rfl]
          exact this
      · intro j hj
        cases j with
        | zero =>
          have h1 := hP4' nd.toNat (by omega) (by omega) (by omega)
          simp only [Nat.add_zero]
          rw [h1, hget, if_pos rfl]
          simp only [ofNat_toNat_word]
        | succ j =>
          have := hP3' j (by omega)
          rw [show nd.toNat + (j + 1) = nd.toNat + 1 + j by omega, this]
      · intro i hi h1 h2
        have := hP4' i (by omega) (by omega) (by omega)
        rw [this, hget, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem allocW_size {m m1 : Mem} {k q : Word} (h : allocW m k = some (q, m1))
    (hsz : (m.arr64 IW).size < 2 ^ 64) : (m1.arr64 IW).size < 2 ^ 64 := by
  obtain ⟨-, rfl, -⟩ := allocW_facts h hsz
  rw [allocMem_IW]; exact hsz

/-- The model of `check_block_positivity_member(o, l)` at the caller's fuel `n`. -/
def posMemberW (n : Nat) (m : Mem) (o l : Word) : Option (List Word × Mem) :=
  match allocW m l with
  | none => none
  | some (kq, m1) =>
    match allocW m1 l with
    | none => none
    | some (nq, m2) =>
      match pmGoW (n - 1) m2 kq nq o l with
      | none => none
      | some m3 => some ([kq, l, nq, l], m3)

theorem checkBlockPositivityMember_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (h2 : p.lookup "rec2" = some rec2)
    (hg : p.lookup "check_block_positivity_member_go" = some checkBlockPositivityMemberGo)
    (hp : p.lookup "check_block_positivity_member" = some checkBlockPositivityMember) (n : Nat)
    (s₀ : St) (o l : Word) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_positivity_member" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ posMemberW n s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockPositivityMember]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hmod : ∀ kq nq m1 m2 m3, allocW s₀.mem l = some (kq, m1) → allocW m1 l = some (nq, m2) →
        pmGoW n m2 kq nq o l = some m3 →
        posMemberW (n + 1) s₀.mem o l = some ([kq, l, nq, l], m3) := by
      intro kq nq m1 m2 m3 h1 h2 h3
      simp [posMemberW, h1, h2, h3]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n, checkBlockPositivityMemberGo_spec p ha h2 hg n] <;>
      finish (gen := 20) [allocW_size]

end L.Ind
