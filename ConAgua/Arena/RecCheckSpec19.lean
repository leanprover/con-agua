import ConAgua.Arena.RecCheckSpec18

/-!
# `RecCheck`: `consBlockRecsTF`, continued (lane `indproofs3`, helper `rec`)

`rules_to_erec` under the stage relation (the run decodes as the rules), `rec_info_rec` (the
`.recInfo` record), `cons_block_recs_push` (with lane `decls2`'s `env_push`), and the recursion.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `rec_info_rec` -/

/-- The memory after `rec_info_rec`'s nine writes (each copy reads the memory of its time). -/
def riMem (m1 : Mem) (q cv mi rp3 reo rel : Word) : Mem :=
  let m2 := m1.set64 EREC q 5
  let m3 := m2.set64 EREC (q + 1) (rdW (m2.arr64 EREC) cv)
  let m4 := m3.set64 EREC (q + 2) (rdW (m3.arr64 EREC) (cv + 1))
  let m5 := m4.set64 EREC (q + 3) (rdW (m4.arr64 EREC) (cv + 2))
  let m6 := m5.set64 EREC (q + 4) (rdW (m5.arr64 EREC) (cv + 3))
  ((((m6.set64 EREC (q + 5) mi).set64 EREC (q + 6) rp3).set64 EREC (q + 7) reo).set64 EREC (q + 8) rel)

/-- **The model of `rec_info_rec`.** -/
def riW (m : Mem) (cv mi rp3 reo rel : Word) : Option (List Word × Mem) :=
  match erAllocW m 9 with
  | none => none
  | some (q, m1) => some ([q], riMem m1 q cv mi rp3 reo rel)

theorem ri_spec (p : Prog) (L : CbrLook p) (n : Nat) (s₀ : St) (cv mi rp3 reo rel : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec_info_rec" [cv, mi, rp3, reo, rel]
    ⦃fun r s' => LocEq s' s₀ ∧ riW s₀.mem cv mi rp3 reo rel = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.rir]
  simp only [callFn, recInfoRec]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        erecAlloc_specW p L.tsr.ea n] <;>
      finish [riW, riMem]

theorem riMem_eq {m1 : Mem} {q cq mi rp3 reo rel : Word} (hlt : cq.toNat + 4 ≤ q.toNat) (hq : q.toNat + 9 < 2 ^ 64) :
    riMem m1 q cq mi rp3 reo rel = wrER m1 q [5, rdW (m1.arr64 EREC) cq, rdW (m1.arr64 EREC) (cq + 1),
      rdW (m1.arr64 EREC) (cq + 2), rdW (m1.arr64 EREC) (cq + 3), mi, rp3, reo, rel] := by
  have t1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have t2 : (q + 2).toNat = q.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have t3 : (q + 3).toNat = q.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have c1 : (cq + 1).toNat = cq.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have c2 : (cq + 2).toNat = cq.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have c3 : (cq + 3).toNat = cq.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  simp only [riMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl, show q + 6 + 1 = q + 7 by ac_rfl, show q + 7 + 1 = q + 8 by ac_rfl]
  simp (disch := ((try simp only [t1, t2, t3, c1, c2, c3]); omega)) only [rdW_set64_ne_er]

/-- **`class_fe_r_rec` under the stage relation**: a fresh rule-less `.recInfo` record of the constant
at `cq`. -/
theorem riRec_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cq mi rp3 reo rel q : Word} {cv : IConstantVal} {rules : List IRecRule}
    (h : riW m cq mi rp3 reo rel = some ([q], m'))
    (hS : StageR dn vis fe m a) (hcv : decCV (erecP m) cq.toNat = some cv)
    (hru : decRules (erecP m) reo.toNat rel.toNat = some rules) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ MFr [] [] m m' ∧
      decCI (erecP m') dn q.toNat = some (.recInfo cv mi.toNat rp3.toNat rules) := by
  cases h1 : erAllocW m 9 with
  | none => simp [riW, h1] at h
  | some x =>
  obtain ⟨q1, m1⟩ := x
  simp only [riW, h1, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl⟩ := h
  have h3 : (erecP m)[cq.toNat + 3]? ≠ none := by
    have := decCV_type hcv; intro e; simp [hd?, e] at this
  have hcq : cq.toNat + 4 ≤ erTop m := by
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h3; have := erecP_lt hv; omega
  have hE1 : m1.arr64 EREC = m.arr64 EREC := by
    simp only [erAllocW] at h1; split at h1; · cases h1
    split at h1; · cases h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨-, rfl⟩ := h1
    simp only [erAllocMem]; exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  obtain ⟨-, hEtop, -, hEsz, -⟩ := hS.2
  have hq1 : q1.toNat = erTop m := by
    simp only [erAllocW] at h1; split at h1; · cases h1
    split at h1; · cases h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, -⟩ := h1; rfl
  obtain ⟨hS', hg, -, htop', hget⟩ := erRec_stage h1 hS [5, rdW (m.arr64 EREC) cq,
    rdW (m.arr64 EREC) (cq + 1), rdW (m.arr64 EREC) (cq + 2), rdW (m.arr64 EREC) (cq + 3), mi, rp3, reo, rel]
    (by simp)
  have hroom : q1.toNat + 9 < 2 ^ 64 := by
    obtain ⟨-, h2, -, h4, -⟩ := hS'.2; simp only [List.length_cons, List.length_nil] at htop'; omega
  rw [riMem_eq (by omega) hroom, hE1]
  refine ⟨hS', hg, by rw [← hE1]; exact erRec_mfr h1 _, ?_⟩
  generalize hM : wrER m1 q1 _ = M at hS' hg htop' hget
  have hP : ∀ j, j < 9 → (erecP M)[q1.toNat + j]? = ((M.arr64 EREC))[q1.toNat + j]? :=
    fun j hj => erecP_getE (by simp at htop'; omega)
  have c1 : (cq + 1).toNat = cq.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have c2 : (cq + 2).toNat = cq.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have c3 : (cq + 3).toNat = cq.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have hw : ∀ i, i < 4 → (erecP M)[q1.toNat + 1 + i]? = (erecP M)[cq.toNat + i]? := by
    intro i hi
    rw [show q1.toNat + 1 + i = q1.toNat + (i + 1) by omega, hP (i + 1) (by omega),
      hget (i + 1) (by simp; omega), erecP_getE (by omega), hg.2.2.2 _ (by omega)]
    have hlt : cq.toNat + i < (m.arr64 EREC).size := by simp only [erTop] at hEtop hcq; omega
    rcases i with _ | _ | _ | _ | i
    all_goals first
      | omega
      | (simp only [Nat.add_zero, Nat.zero_add] at hlt ⊢
         simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, rdW, c1, c2, c3,
          Array.getElem?_eq_getElem hlt, Option.getD_some])
  have hcv' : decCV (erecP M) (q1.toNat + 1) = some cv := by
    rw [decCV_shift (by simpa using hw 0 (by decide)) (by simpa using hw 1 (by decide))
      (by simpa [Nat.add_assoc] using hw 2 (by decide)) (by simpa [Nat.add_assoc] using hw 3 (by decide))]
    exact ArrExt.decCV (IWGrow.erecPExtR hg) hcv
  have nk : ∀ j (hj : j < 9), nat? (erecP M) (q1.toNat + j) =
      some (([5, rdW (m.arr64 EREC) cq, rdW (m.arr64 EREC) (cq + 1), rdW (m.arr64 EREC) (cq + 2),
        rdW (m.arr64 EREC) (cq + 3), mi, rp3, reo, rel] : List Word)[j]'(by simpa using hj)).toNat := by
    intro j hj
    simp only [nat?, hP j hj, hget j (by simpa using hj)]
    rw [List.getElem?_eq_getElem (by simp; omega)]; rfl
  have n0 := nk 0 (by decide)
  have n5 := nk 5 (by decide)
  have n6 := nk 6 (by decide)
  have n7 := nk 7 (by decide)
  have n8 := nk 8 (by decide)
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at n0 n5 n6 n7 n8
  have hru' : decRules (erecP M) reo.toNat rel.toNat = some rules := (IWGrow.erecPExtR hg).decRules hru
  simp only [decCI, Option.bind_eq_bind, n0, Option.bind_some, hcv', n5, n6, n7, n8, Option.pure_def]
  simp [hru']

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/-- **`rules_to_erec` under the stage relation**: a fresh consecutive run of the rule records at the
old record top, decoding as the rules. -/
theorem rteW_ok (n : Nat) {m m' : Mem} {a : AState} {ro rl : Word} {r : List Word} {rules : List IRecRule}
    (h : rteW n m ro rl = some (r, m')) (hS : StageR dn vis fe m a)
    (hd : decPL m (rlDec m) ro.toNat rl.toNat = some rules) (_hb : ro.toNat + rl.toNat ≤ iwTop m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ r.tail.headD 0 = rl ∧
      decRules (erecP m') (r.headD 0).toNat rl.toNat = some rules ∧ MFr [] [] m m' := by
  obtain _ | n := n
  · simp [rteW] at h
  by_cases hbig : 4294967296 ≤ rl
  · rw [rteW.abort1 (hc1 := hbig)] at h; cases h
  rw [rteW.arm1 (hc1 := hbig)] at h
  have hrl : rl.toNat < 2 ^ 32 := by rw [UInt64.le_iff_toNat_le] at hbig; simp at hbig; omega
  rcases ha : erAllocW m (rl * 11) with _ | ⟨b, m1⟩ <;> simp only [ha, rteW.k_erec_alloc, reduceCtorEq] at h
  rcases h1 : rteGoW n m1 b ro rl with _ | ⟨r1, m2⟩ <;> simp only [h1, rteW.k_rules_to_erec_go, reduceCtorEq] at h
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

/-! ## `cons_block_recs_push` -/

def cbpK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rv, m) => some ([rv.headD 0], m)

def cbpK2 (p : Prog) (n : Nat) (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rq, m) => cbpK3 (callW p n "env_push" [vis, rq.headD 0] m)

def cbpK1 (p : Prog) (n : Nat) (vis cv mI rP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (re, m) => cbpK2 p n vis (riW m cv mI rP (re.headD 0) (re.tail.headD 0))

/-- **The model of `cons_block_recs_push`** (exec fuel). -/
def cbpW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, cv, mI, rP, ro, rl => cbpK1 p n vis cv mI rP (rteW n m ro rl)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis cv mI rP ro rl : Word) (rv rq re : List Word)
theorem cbpW_succ : cbpW p (n + 1) m vis cv mI rP ro rl = cbpK1 p n vis cv mI rP (rteW n m ro rl) := rfl
theorem cbpK1_some : cbpK1 p n vis cv mI rP (some (re, m)) =
    cbpK2 p n vis (riW m cv mI rP (re.headD 0) (re.tail.headD 0)) := rfl
theorem cbpK2_some : cbpK2 p n vis (some (rq, m)) = cbpK3 (callW p n "env_push" [vis, rq.headD 0] m) := rfl
theorem cbpK3_some : cbpK3 (some (rv, m)) = some ([rv.headD 0], m) := rfl
end arms
attribute [ind_grind] cbpW_succ cbpK1_some cbpK2_some cbpK3_some

theorem cbp_spec (p : Prog) (L : CbrLook p) (n : Nat) (s₀ : St) (vis cv mI rP ro rl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cons_block_recs_push" [vis, cv, mI, rP, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ cbpW p n s₀.mem vis cv mI rP ro rl = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
    rw [invoke_eq _ L.push]
    simp only [callFn, consBlockRecsPush]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, rte_spec p L n, ri_spec p L n,
        callW_spec p n "env_push"] <;>
      finish (gen := 20) [loc_init4, loc_init5]

/-! ## The `abstract1` memo across `cons_block_recs_push` -/

theorem rteGoW_afr : ∀ (n : Nat) (m m' : Mem) (b ro rl : Word) (r : List Word),
    rteGoW n m b ro rl = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [rteGoW] at h
  | n + 1, m, m', b, ro, rl, r, h => by
    by_cases h0 : rl = 0
    · rw [rteGoW_nil (h := h0)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [rteGoW_cons (h := h0)] at h
    rcases h2 : rteGoW n (cpMem m b (rdW (m.arr64 IW) ro)) (b + 11) (ro + 1) (rl - 1) with _ | ⟨r2, m2⟩ <;> simp only [h2, rteK1, reduceCtorEq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact (show AFr m (cpMem m b (rdW (m.arr64 IW) ro)) by simp only [cpMem]; afr_set).trans
      (rteGoW_afr n _ _ _ _ _ _ h2)

theorem rteW_afr {n : Nat} {m m' : Mem} {ro rl : Word} {r : List Word}
    (h : rteW n m ro rl = some (r, m')) : AFr m m' := by
  obtain _ | n := n
  · simp [rteW] at h
  by_cases hb : 4294967296 ≤ rl
  · rw [rteW.abort1 (hc1 := hb)] at h; cases h
  rw [rteW.arm1 (hc1 := hb)] at h
  rcases h1 : erAllocW m (rl * 11) with _ | ⟨b, m1⟩ <;> simp only [h1, rteW.k_erec_alloc, reduceCtorEq] at h
  rcases h2 : rteGoW n m1 b ro rl with _ | ⟨r2, m2⟩ <;> simp only [h2, rteW.k_rules_to_erec_go, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (erAllocW_afr h1).trans (rteGoW_afr n _ _ _ _ _ _ h2)

theorem riW_afr {m m' : Mem} {cv mi rp3 reo rel : Word} {r : List Word}
    (h : riW m cv mi rp3 reo rel = some (r, m')) : AFr m m' := by
  simp only [riW] at h
  split at h; · cases h
  rename_i q m1 h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (erAllocW_afr h1).trans (by simp only [riMem]; afr_set)

section rel2
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/-- **`cons_block_recs_push` under the stage relation**: the rules' run, the `.recInfo` record, pushed. -/
theorem cbpW_ok (p : Prog) (L : CbrLook p) (n : Nat) {m m' : Mem} {a : AState} {cv mI rP ro rl : Word}
    {r : List Word} {cvv : IConstantVal} {rules : List IRecRule}
    (h : cbpW p n m vis cv mI rP ro rl = some (r, m')) (hS : StageR dn vis fe m a)
    (hcv : decCV (erecP m) cv.toNat = some cvv)
    (hd : decPL m (rlDec m) ro.toNat rl.toNat = some rules) (hb : ro.toNat + rl.toNat ≤ iwTop m) :
    StageR dn (r.headD 0) (fe.push (.recInfo cvv mI.toNat rP.toNat rules)) m' a ∧ IWGrow m m' ∧
      AFr m m' := by
  obtain _ | n := n
  · simp [cbpW] at h
  rw [cbpW_succ] at h
  rcases h1 : rteW n m ro rl with _ | ⟨re, m1⟩ <;> simp only [h1, cbpK1, reduceCtorEq] at h
  obtain ⟨hS1, hg1, hre, hru, -⟩ := rteW_ok dn fe vis n h1 hS hd hb
  rw [hre] at h
  rcases h2 : riW m1 cv mI rP (re.headD 0) rl with _ | ⟨rq, m2⟩ <;> simp only [h2, cbpK2, reduceCtorEq] at h
  have hrq : rq = [rq.headD 0] := by
    simp only [riW] at h2; split at h2
    · cases h2
    · simp only [Option.some.injEq, Prod.mk.injEq] at h2; rw [← h2.1]; rfl
  rw [hrq] at h2
  obtain ⟨hS2, hg2, -, hci⟩ := riRec_stage h2 hS1 ((IWGrow.erecPExtR hg1).decCV hcv) hru
  obtain ⟨wn, hwn, hwnl, -⟩ := decCI_name hci
  have hwn' : (rdW (m2.arr64 EREC) (rq.headD 0 + 1)).toNat < 2 ^ 32 := by
    have hq1 : (rq.headD 0 + 1).toNat = (rq.headD 0).toNat + 1 := by
      have := erecP_lt hwn; obtain ⟨-, h2', -, h4, -⟩ := hS2.2
      rw [UInt64.toNat_add, show (1 : Word).toNat = 1 from rfl]; exact Nat.mod_eq_of_lt (by omega)
    rw [rdW_of_get? hq1.symm (erecP_get hwn)]; exact hwnl
  rcases h3 : callW p n "env_push" [vis, rq.headD 0] m2 with _ | ⟨rv, m3⟩ <;> simp only [h3, cbpK3, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (envPush_specW p L.rp n ⟨m2, Locals.init []⟩ vis (rq.headD 0) hwn') h3
  subst hs4
  obtain ⟨hS3, hg3⟩ := envPushW_ok hW4 hS2 hci
  exact ⟨by simpa using hS3, (hg1.trans hg2).trans hg3,
    (rteW_afr h1).trans ((riW_afr h2).trans (envPushW_afr hW4))⟩

end rel2

end L.Ind
