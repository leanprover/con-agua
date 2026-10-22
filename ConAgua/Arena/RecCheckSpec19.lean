import ConAgua.Arena.RecCheckSpec18

/-!
# `RecCheck`: `consBlockRecsTF`, continued (lane `indproofs3`, helper `rec`)

`rules_to_erec` under the stage relation (the run decodes as the rules), `rec_info_rec` (the
`.recInfo` record), `cons_block_recs_push` (with lane `decls2`'s `env_push`), and the recursion.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/-- **`rules_to_erec` under the stage relation**: a fresh consecutive run of the rule records at the
old record top, decoding as the rules. -/
theorem rteW_ok (n : Nat) {m m' : Mem} {a : AState} {ro rl : Word} {r : List Word} {rules : List IRecRule}
    (h : rteW n m ro rl = some (r, m')) (hS : StageR dn vis fe m a)
    (hd : decPL m (rlDec m) ro.toNat rl.toNat = some rules) (hb : ro.toNat + rl.toNat ≤ iwTop m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ r.tail.headD 0 = rl ∧
      decRules (erecP m') (r.headD 0).toNat rl.toNat = some rules ∧ MFr [] [] m m' := by
  cases n with
  | zero => simp [rteW] at h
  | succ n =>
  by_cases hbig : 4294967296 ≤ rl
  · rw [rteW_big (h := hbig)] at h; cases h
  rw [rteW_ok' (h := hbig)] at h
  have hrl : rl.toNat < 2 ^ 32 := by rw [UInt64.le_iff_toNat_le] at hbig; simp at hbig; omega
  cases ha : erAllocW m (rl * 11) with
  | none => rw [ha] at h; simp [rteK2] at h
  | some x =>
  obtain ⟨b, m1⟩ := x
  rw [ha, rteK2_some] at h
  cases h1 : rteGoW n m1 b ro rl with
  | none => rw [h1] at h; simp [rteK3] at h
  | some x =>
  obtain ⟨r1, m2⟩ := x
  rw [h1, rteK3_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  have hm1 := erAllocW_mem ha
  have hI1 : m1.arr64 IW = m.arr64 IW := by rw [hm1]; exact erAllocMem_arr _ _ (by decide)
  have hE1 : m1.arr64 EREC = m.arr64 EREC := by rw [hm1]; exact erAllocMem_arr _ _ (by decide)
  have hk : (rl * 11).toNat = 11 * rl.toNat := by
    rw [UInt64.toNat_mul]; simp; omega
  -- the old records lie below the record pool's top, which is `b`
  have hbq : b.toNat = erTop m := by
    simp only [erAllocW] at ha; split at ha; · cases ha
    split at ha; · cases ha
    simp only [Option.some.injEq, Prod.mk.injEq] at ha; obtain ⟨rfl, -⟩ := ha; rfl
  have hv : ∀ j < rl.toNat, ∃ v rlj, iwN m (ro.toNat + j) = some v ∧ rlDec m v = some rlj ∧ rules[j]? = some rlj ∧
      v + 11 ≤ erTop m := by
    intro j hj
    obtain ⟨v, y, hv, hf, hget⟩ := decPL_get rl.toNat ro.toNat rules hd j hj
    refine ⟨v, y, hv, hf, hget, ?_⟩
    obtain ⟨-, -, -, -, -, h10⟩ := decRule_fields (b := erecP m) (q' := v) hf (fun _ _ => rfl)
    simp only [bool?, Option.map_eq_some_iff] at h10
    obtain ⟨w, hw, -⟩ := h10
    have := erecP_lt hw; omega
  have hsz := hS.2.2.2.1
  have hrdv : ∀ j < rl.toNat, ∀ v, iwN m (ro.toNat + j) = some v →
      rdW (m.arr64 IW) (ro + UInt64.ofNat j) = UInt64.ofNat v ∧ v < 2 ^ 64 := by
    intro j hj v hv'
    exact iwN_rdW_at (w := ro) (k := j) hv' hsz
  have hold : ∀ j < rl.toNat, (rdW (m1.arr64 IW) (ro + UInt64.ofNat j)).toNat + 11 ≤ b.toNat := by
    intro j hj
    obtain ⟨v, rlj, hvj, -, -, hvt⟩ := hv j hj
    obtain ⟨e, hlt⟩ := hrdv j hj v hvj
    rw [hI1, e, UInt64.toNat_ofNat_of_lt' hlt, hbq]; exact hvt
  obtain ⟨hS1, hg1, hq1, htop1, hget1⟩ := erRec_stage ha hS (ruleWords m1 ro rl.toNat)
    (by rw [ruleWords_length, hk])
  have hroom : b.toNat + 11 * rl.toNat ≤ (m1.arr64 EREC).size := by
    obtain ⟨-, h2, -, h4, -⟩ := hS1.2
    have hs := (wrER_frame (ruleWords m1 ro rl.toNat) m1 b).2.2.1 EREC
    rw [ruleWords_length] at htop1; omega
  have hm2 := rteGoW_mem n m1 m2 b ro rl r1 h1 hold hroom (by rw [hE1]; exact hS.2.2.2.2.1)
  subst hm2
  refine ⟨hS1, hg1, rfl, ?_, erRec_mfr ha _⟩
  simp only [List.headD_cons]
  -- the run, record by record
  have hrw := ruleWords_length m1 ro rl.toNat
  generalize hM : wrER m1 b (ruleWords m1 ro rl.toNat) = M at hS1 hg1 htop1 hget1 ⊢
  have hext := IWGrow.erecPExtR hg1
  have hlen := decPL_length m hd
  unfold decRules
  rw [← hlen]
  apply mapM_range_some
  intro j hj
  rw [hlen] at hj
  obtain ⟨v, rlj, hvj, hfj, hgj, hvt⟩ := hv j hj
  obtain ⟨e, hlt⟩ := hrdv j hj v hvj
  have hrj : rules[j] = rlj := by
    rw [List.getElem?_eq_getElem (by omega)] at hgj; exact Option.some.inj hgj
  rw [hrj]
  refine decRule_copy hfj hext (fun i hi => ?_)
  have hEt : erTop m ≤ (m.arr64 EREC).size := hS.2.2.1
  rw [show b.toNat + 11 * j + i = b.toNat + (11 * j + i) by omega,
    erecP_getE (by rw [htop1, hrw]; omega), hget1 (11 * j + i) (by rw [hrw]; omega),
    ruleWords_get m1 ro rl.toNat j i hj hi, hI1, e, hE1, erecP_getE (by omega)]
  have hEs : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  refine (rdW_some ?_ (by omega)).symm
  rw [UInt64.toNat_add]; simp; omega

end rel

end L.Ind
