import ConAgua.Arena.IndSumSpec.SumRules
import ConAgua.Arena.IndSumSpec.TblProg
import ConAgua.Arena.RecCheckSpec.TsrLook

/-!
# TsrW

`efgW_mem`, `sumHslice_of_get`, `efW_stage`, `efgW_afr`, `efW_afr`, `nat?_shift` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The copy loop writes the slice's words. -/
theorem efgW_mem (n : Nat) : ∀ (m m' : Mem) (q o l : Word) (r ws : List Word),
    efgW n m q o l = some (r, m') → SlR m o l ws → m' = wrER m q ws := by
  induction n with
  | zero => intro m m' q o l r ws h; simp [efgW] at h
  | succ n ih =>
    intro m m' q o l r ws h hs
    cases hs with
    | nil =>
      rw [efgW_nil n m q o 0 rfl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.symm
    | @cons _ _ ws hl hs =>
      rw [efgW_cons n m q o l hl] at h
      obtain ⟨r1, m1, h1, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [efgK_some] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      show m1 = wrER (m.set64 EREC q (rdW (m.arr64 IW) o)) (q + 1) ws
      have hI : (m.set64 EREC q (rdW (m.arr64 IW) o)).arr64 IW = m.arr64 IW :=
        Mem.arr64_set64_ne _ _ _ _ _ (by decide)
      exact ih _ _ _ _ _ _ _ h1 (slR_congr hI hs)

/-- Handle words at `q, q + 1, …` decode as the handle list. -/
theorem sumHslice_of_get {k : IdxKind} {a : Array Word} : ∀ (ws : List Word) (q : Nat),
    (∀ j < ws.length, a[q + j]? = ws[j]?) → (∀ w ∈ ws, H w) →
    (hslice? a q ws.length : Option (List (Idx k))) = some (ws.map decI)
  | [], q, _, _ => by simp [hslice?]
  | w :: ws, q, h, hw => by
    simp only [List.length_cons, hslice?_succ, List.map_cons]
    have h0 : a[q]? = some w := by simpa using h 0 (by simp)
    have ih := sumHslice_of_get (k := k) ws (q + 1) (fun j hj => by
      have := h (j + 1) (by simpa using hj); rw [show q + 1 + j = q + (j + 1) by omega]; simpa using this)
      (fun v hv => hw v (by simp [hv]))
    have hw0 : H w := hw w (by simp)
    simp [hd?, h0, hw0, ih]

/-- **`er_from_iw` under the stage relation**: a fresh `EREC` slice (at the old record top) holding
the `IW` list, decoded in the record pool below its new top. -/
theorem efW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} (n : Nat)
    {m m' : Mem} {o l : Word} {r : List Word} {kk : IdxKind} {xs : List (Idx kk)}
    (h : efW n m o l = some (r, m'))
    (hS : StageR dn vis fe m a) (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ r.tail.headD 0 = l ∧ (r.headD 0).toNat = erTop m ∧
      hslice? (erecP m') (r.headD 0).toNat l.toNat = some xs ∧ erTop m' = erTop m + l.toNat := by
  unfold efW at h
  obtain ⟨q, m1, hal, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  rw [efK1_some] at h
  obtain ⟨r2, m2, hc, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  rw [efK2_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨ws, hws, rfl, hwl⟩ := slR_of_decHL m _ _ xs hd (hS.lt64 hb)
  simp only [UInt64.ofNat_toNat] at hws
  have hI1 : m1.arr64 IW = m.arr64 IW := by
    simp only [erAllocW] at hal; split at hal; · cases hal
    split at hal; · cases hal
    simp only [Option.some.injEq, Prod.mk.injEq] at hal; obtain ⟨-, rfl⟩ := hal
    simp only [erAllocMem]; exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hm2 := efgW_mem n m1 m2 q o l r2 ws hc (slR_congr hI1 hws)
  subst hm2
  have hlen := slR_length hws
  obtain ⟨hS', hg, hq, htop, hget⟩ := erRec_stage hal hS ws hlen.symm
  refine ⟨hS', hg, rfl, hq, ?_, by rw [htop, hlen]⟩
  simp only [List.headD_cons]
  rw [← hlen]
  apply sumHslice_of_get ws q.toNat _ hwl
  intro j hj
  rw [erecP_getE (by rw [htop]; omega), hget j hj]

/-! ## The walk memos across the table's steps -/

theorem efgW_afr : ∀ (n : Nat) (m m' : Mem) (q o l : Word) (r : List Word),
    efgW n m q o l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [efgW] at h
  | n + 1, m, m', q, o, l, r, h => by
    simp only [efgW, efgK.eq_def] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    · refine AFr.trans (set64ER_afr m q (rdW (m.arr64 IW) o)) ?_
      afr_auto h [efgW_afr n _ _ _ _ _ _]

theorem efW_afr {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : efW n m o l = some (r, m')) :
    AFr m m' := by
  simp only [efW, efK1.eq_def, efK2.eq_def] at h
  afr_auto h [erAllocW_afr, efgW_afr _ _ _ _ _ _ _]

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Rule records at another address -/

section shift
variable {a b : Array Word}

theorem nat?_shift {i j : Nat} (h : b[j]? = a[i]?) : nat? b j = nat? a i := by simp [nat?, h]
theorem bool?_shift {i j : Nat} (h : b[j]? = a[i]?) : bool? b j = bool? a i := by simp [bool?, h]
theorem hd?_shift {k : IdxKind} {i j : Nat} (h : b[j]? = a[i]?) : (hd? b j : Option (Idx k)) = hd? a i := by
  simp [hd?, h]

/-- The six plain fields of a rule record, read at another address. -/
theorem decRule_fields {q q' : Nat} {rl : IRecRule} (h : decRule a q = some rl)
    (hw : ∀ i, i < 3 ∨ (8 ≤ i ∧ i < 11) → b[q' + i]? = a[q + i]?) :
    hd? b q' = some rl.ctor ∧ nat? b (q' + 1) = some rl.nfields ∧ nat? b (q' + 2) = some rl.ctorParams ∧
      hd? b (q' + 8) = some rl.rhs ∧ bool? b (q' + 9) = some rl.k ∧ bool? b (q' + 10) = some rl.eta := by
  have tail : ∀ f : IRecRuleFire, (do
      let ctor ← L.Arena.hd? a q
      let nfields ← L.Arena.nat? a (q + 1)
      let ctorParams ← L.Arena.nat? a (q + 2)
      let rhs ← L.Arena.hd? a (q + 8)
      let k ← L.Arena.bool? a (q + 9)
      let eta ← L.Arena.bool? a (q + 10)
      pure ({ ctor, nfields, ctorParams, fire := f, rhs, k, eta } : IRecRule)) = some rl →
      hd? b q' = some rl.ctor ∧ nat? b (q' + 1) = some rl.nfields ∧ nat? b (q' + 2) = some rl.ctorParams ∧
      hd? b (q' + 8) = some rl.rhs ∧ bool? b (q' + 9) = some rl.k ∧ bool? b (q' + 10) = some rl.eta := by
    intro f hf
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at hf
    obtain ⟨c, hc, nf, hnf, cp, hcp, r, hr, k, hk, e, he, rfl⟩ := hf
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hd?_shift (i := q + 0) (by simpa using hw 0 (by omega))]; simpa using hc
    · rw [nat?_shift (hw 1 (by omega))]; exact hnf
    · rw [nat?_shift (hw 2 (by omega))]; exact hcp
    · rw [hd?_shift (hw 8 (by omega))]; exact hr
    · rw [bool?_shift (hw 9 (by omega))]; exact hk
    · rw [bool?_shift (hw 10 (by omega))]; exact he
  unfold L.Arena.decRule at h
  cases h3 : L.Arena.nat? a (q + 3) with
  | none => simp [h3] at h
  | some t =>
  rw [h3] at h
  simp only [Option.bind_eq_bind, Option.bind_some] at h
  match t, h with
  | 0, h => simp only at h; exact tail _ h
  | 1, h =>
    cases hy : (L.Arena.hlist? a (q + 4) : Option (List LIdx)) with
    | none => simp [hy] at h
    | some y =>
    cases hz : (L.Arena.hlist? a (q + 6) : Option (List EIdx)) with
    | none => simp [hy, hz] at h
    | some z =>
    rw [hy, hz] at h; simp only [Option.bind_some] at h; exact tail _ h
  | t + 2, h => simp at h

/-- A rule record whose plain fields are copied and whose fire is a NESTED one at slices `b` decodes. -/
theorem decRule_nested {q q' : Nat} {rl : IRecRule} {lo ll po pl : Nat} {lvls : List LIdx} {pins : List EIdx}
    (h : decRule a q = some rl) (hw : ∀ i, i < 3 ∨ (8 ≤ i ∧ i < 11) → b[q' + i]? = a[q + i]?)
    (h3 : nat? b (q' + 3) = some 1) (h4 : nat? b (q' + 4) = some lo) (h5 : nat? b (q' + 5) = some ll)
    (h6 : nat? b (q' + 6) = some po) (h7 : nat? b (q' + 7) = some pl)
    (hl : hslice? b lo ll = some lvls) (hp : hslice? b po pl = some pins) :
    decRule b q' = some { rl with fire := .nested lvls pins } := by
  obtain ⟨c, n1, n2, n8, n9, n10⟩ := decRule_fields h hw
  unfold L.Arena.decRule
  have e4 : (hlist? b (q' + 4) : Option (List LIdx)) = some lvls := by
    simp only [hlist?, h4, h5, Option.bind_eq_bind, Option.bind_some]; exact hl
  have e6 : (hlist? b (q' + 6) : Option (List EIdx)) = some pins := by
    simp only [hlist?, h6, h7, Option.bind_eq_bind, Option.bind_some]; exact hp
  simp only [h3, e4, Option.bind_eq_bind, Option.bind_some, c, n1, n2, n8, n9, n10, Option.pure_def]
  rw [e6]; rfl

end shift

/-! ## `tgt_stored_rules_remap` -/

/-- The memory after one rebuilt record's eleven writes (each copy reads the memory of its time). -/
def rmMem (m1 : Mem) (q old flo fll fpo fpl : Word) : Mem :=
  let m2 := m1.set64 EREC q (rdW (m1.arr64 EREC) old)
  let m3 := m2.set64 EREC (q + 1) (rdW (m2.arr64 EREC) (old + 1))
  let m4 := m3.set64 EREC (q + 2) (rdW (m3.arr64 EREC) (old + 2))
  let m5 := ((((m4.set64 EREC (q + 3) 1).set64 EREC (q + 4) flo).set64 EREC (q + 5) fll).set64 EREC (q + 6)
    fpo).set64 EREC (q + 7) fpl
  let m6 := m5.set64 EREC (q + 8) (rdW (m5.arr64 EREC) (old + 8))
  let m7 := m6.set64 EREC (q + 9) (rdW (m6.arr64 EREC) (old + 9))
  m7.set64 EREC (q + 10) (rdW (m7.arr64 EREC) (old + 10))

/-- **The model of `tgt_rule_nested`.** -/
def trnW (m : Mem) (old flo fll fpo fpl : Word) : Option (List Word × Mem) :=
  match erAllocW m 11 with
  | none => none
  | some (q, m1) => some ([q], rmMem m1 q old flo fll fpo fpl)

theorem trn_spec (p : Prog) (L : TsrLook p) (n : Nat) (s₀ : St) (old flo fll fpo fpl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "tgt_rule_nested" [old, flo, fll, fpo, fpl]
    ⦃fun r s' => LocEq s' s₀ ∧ trnW s₀.mem old flo fll fpo fpl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.trn]
  simp only [callFn, tgtRuleNested]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        erecAlloc_specW p L.ea n] <;>
      finish [trnW, rmMem]

l_model tsrm_spec (p : Prog) (hL : TsrLook p)
  fns [hL.tsrm ↦ tsrmW]
  specs [trn_spec p hL n, slCons_specW p hL.rc.rx.ha hL.ic hL.sc n]
  grind [arena_grind] simp [getElem_rdW']

/-! ## The rebuilt record under the stage relation -/

set_option maxHeartbeats 2000000 in
theorem rmMem_eq {m1 : Mem} {q old flo fll fpo fpl : Word} (hlt : old.toNat + 11 ≤ q.toNat)
    (hq : q.toNat + 11 < 2 ^ 64) :
    rmMem m1 q old flo fll fpo fpl = wrER m1 q [rdW (m1.arr64 EREC) old, rdW (m1.arr64 EREC) (old + 1),
      rdW (m1.arr64 EREC) (old + 2), 1, flo, fll, fpo, fpl, rdW (m1.arr64 EREC) (old + 8),
      rdW (m1.arr64 EREC) (old + 9), rdW (m1.arr64 EREC) (old + 10)] := by
  have t1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have t2 : (q + 2).toNat = q.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have t3 : (q + 3).toNat = q.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have t4 : (q + 4).toNat = q.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have t5 : (q + 5).toNat = q.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
  have t6 : (q + 6).toNat = q.toNat + 6 := by rw [UInt64.toNat_add]; simp; omega
  have t7 : (q + 7).toNat = q.toNat + 7 := by rw [UInt64.toNat_add]; simp; omega
  have t8 : (q + 8).toNat = q.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have t9 : (q + 9).toNat = q.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have t10 : (q + 10).toNat = q.toNat + 10 := by rw [UInt64.toNat_add]; simp; omega
  have c1 : (old + 1).toNat = old.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have c2 : (old + 2).toNat = old.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have c8 : (old + 8).toNat = old.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have c9 : (old + 9).toNat = old.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have c10 : (old + 10).toNat = old.toNat + 10 := by rw [UInt64.toNat_add]; simp; omega
  simp only [rmMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl, show q + 6 + 1 = q + 7 by ac_rfl, show q + 7 + 1 = q + 8 by ac_rfl,
    show q + 8 + 1 = q + 9 by ac_rfl, show q + 9 + 1 = q + 10 by ac_rfl]
  simp (disch := ((try simp only [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, c1, c2, c8, c9, c10]); omega)) only
    [rdW_set64_ne_er]

theorem erRec_mfr {m m1 : Mem} {k q : Word} (h : erAllocW m k = some (q, m1)) (ws : List Word) :
    MFr [] [] m (wrER m1 q ws) := by
  rw [erAllocW_mem h]
  have f1 : MemFrame [EREC] [129] m (erAllocMem m k) :=
    (MemFrame.setCtl m 129 _).mono (by simp) (by simp)
  have f2 : MemFrame [EREC] [129] (erAllocMem m k) (wrER (erAllocMem m k) q ws) :=
    (wrER_frame ws _ q).mono (by simp) (by simp)
  exact MFr.of_frame (f1.trans f2) (by simp [EREC]) (by simp)

theorem rdW_some {arr : Array Word} {x : Word} {j : Nat} (hj : x.toNat = j) (hlt : j < arr.size) :
    arr[j]? = some (rdW arr x) := by
  simp [rdW, hj, Array.getElem?_eq_getElem hlt]

set_option maxRecDepth 4000 in
/-- **One rebuilt rule record under the stage relation**: a fresh 11-word record, the old record's
plain fields, the NESTED fire at the given record-pool slices. -/
theorem rmRec_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m1 : Mem} {q old flo fll fpo fpl : Word} {rl : IRecRule} {lvls : List LIdx} {pins : List EIdx}
    (h : erAllocW m 11 = some (q, m1)) (hS : StageR dn vis fe m a) (hold : rlDec m old.toNat = some rl)
    (hl : hslice? (erecP m) flo.toNat fll.toNat = some lvls) (hp : hslice? (erecP m) fpo.toNat fpl.toNat = some pins) :
    StageR dn vis fe (rmMem m1 q old flo fll fpo fpl) a ∧ IWGrow m (rmMem m1 q old flo fll fpo fpl) ∧
      MFr [] [] m (rmMem m1 q old flo fll fpo fpl) ∧
      rlDec (rmMem m1 q old flo fll fpo fpl) q.toNat = some { rl with fire := .nested lvls pins } := by
  -- the old record lies below the record pool's top
  have hold10 : old.toNat + 10 < erTop m := by
    obtain ⟨-, -, -, -, -, h10⟩ := decRule_fields (b := erecP m) (q' := old.toNat) hold (fun _ _ => rfl)
    simp only [bool?, Option.map_eq_some_iff] at h10
    obtain ⟨v, hv, -⟩ := h10
    exact erecP_lt hv
  have hEt : erTop m ≤ (m.arr64 EREC).size := hS.2.2.1
  have hEs : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  have hE1 : m1.arr64 EREC = m.arr64 EREC := by rw [erAllocW_mem h]; exact erAllocMem_arr _ _ (by decide)
  have hc : ∀ k : Nat, k ≤ 10 → (old + UInt64.ofNat k).toNat = old.toNat + k := fun k hk => by
    rw [UInt64.toNat_add]; simp; omega
  have hwi : ∀ k : Nat, k ≤ 10 → (erecP m)[old.toNat + k]? = some (rdW (m1.arr64 EREC) (old + UInt64.ofNat k)) :=
    fun k hk => by
      rw [erecP_getE (by omega), hE1]; exact rdW_some (hc k hk) (by omega)
  generalize hws : [rdW (m1.arr64 EREC) old, rdW (m1.arr64 EREC) (old + 1),
      rdW (m1.arr64 EREC) (old + 2), 1, flo, fll, fpo, fpl, rdW (m1.arr64 EREC) (old + 8),
      rdW (m1.arr64 EREC) (old + 9), rdW (m1.arr64 EREC) (old + 10)] = ws
  have hlen : ws.length = 11 := by rw [← hws]; rfl
  obtain ⟨hS', hg, hqt, htop, hget⟩ := erRec_stage h hS ws (by rw [hlen]; rfl)
  rw [hlen] at htop
  have hroom : q.toNat + 11 < 2 ^ 64 := by
    obtain ⟨-, h2, -, h4, -⟩ := hS'.2; omega
  rw [rmMem_eq (by omega) hroom, hws]
  refine ⟨hS', hg, erRec_mfr h ws, ?_⟩
  generalize hM : wrER m1 q ws = M at hS' hg htop hget
  have hP : ∀ j, j < 11 → (erecP M)[q.toNat + j]? = ws[j]? := fun j hj => by
    rw [erecP_getE (by omega)]; exact hget j (by omega)
  have hw : ∀ i, i < 3 ∨ (8 ≤ i ∧ i < 11) → (erecP M)[q.toNat + i]? = (erecP m)[old.toNat + i]? := by
    intro i hi
    rw [hP i (by omega)]
    rcases hi with hi | ⟨hi1, hi2⟩
    · rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · rw [hwi 0 (by omega), ← hws]; simp
      · rw [hwi 1 (by omega), ← hws]; rfl
      · rw [hwi 2 (by omega), ← hws]; rfl
    · rcases (show i = 8 ∨ i = 9 ∨ i = 10 by omega) with rfl | rfl | rfl
      · rw [hwi 8 (by omega), ← hws]; rfl
      · rw [hwi 9 (by omega), ← hws]; rfl
      · rw [hwi 10 (by omega), ← hws]; rfl
  have hext := IWGrow.erecPExtR hg
  have n3 : nat? (erecP M) (q.toNat + 3) = some 1 := by simp [nat?, hP 3 (by omega), ← hws]
  have n4 : nat? (erecP M) (q.toNat + 4) = some flo.toNat := by simp [nat?, hP 4 (by omega), ← hws]
  have n5 : nat? (erecP M) (q.toNat + 5) = some fll.toNat := by simp [nat?, hP 5 (by omega), ← hws]
  have n6 : nat? (erecP M) (q.toNat + 6) = some fpo.toNat := by simp [nat?, hP 6 (by omega), ← hws]
  have n7 : nat? (erecP M) (q.toNat + 7) = some fpl.toNat := by simp [nat?, hP 7 (by omega), ← hws]
  exact decRule_nested hold hw n3 n4 n5 n6 n7 (hext.hslice? hl) (hext.hslice? hp)

/-- A rule pointer consed onto a rule-pointer slice (`sl_cons`). -/
theorem consW_rl {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {rules : List IRecRule} {rl : IRecRule}
    (h : consW n m x o l = some (r, m')) (hS : StageR dn vis fe m a) (hb : o.toNat + l.toNat ≤ iwTop m)
    (hd : decPL m (rlDec m) o.toNat l.toNat = some rules) (hx : rlDec m x.toNat = some rl) :
    decPL m' (rlDec m') (r.headD 0).toNat (r.tail.headD 0).toNat = some (rl :: rules) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' ∧ StageR dn vis fe m' a ∧ IWGrow m m' ∧
      MFr [] [] m m' := by
  rw [decPL_eq_bind] at hd
  rcases hps : decNL m o.toNat l.toNat with _ | ps <;> rw [hps] at hd
  · cases hd
  simp only [Option.bind_some] at hd
  obtain ⟨hS', hg, hd', ht'⟩ := consW_stageN h hS hb hps
  have hext := IWGrow.erecPExtR hg
  refine ⟨?_, ht', hS', hg, consW_mfr h⟩
  rw [decPL_eq_bind, hd']
  simp only [Option.bind_some, List.mapM_cons]
  rw [show rlDec m' x.toNat = some rl from hext.decRule hx,
    ArrExt.mapM (f := rlDec m) (g := rlDec m') (fun _ _ hy => hext.decRule hy) _ _ hd]
  rfl

theorem decPL_rl_grow {m m' : Mem} (hg : IWGrow m m') {o l : Nat} {rules : List IRecRule}
    (hb : o + l ≤ iwTop m) (hd : decPL m (rlDec m) o l = some rules) : decPL m' (rlDec m') o l = some rules := by
  rw [decPL_eq_bind] at hd ⊢
  rcases hps : decNL m o l with _ | ps <;> rw [hps] at hd
  · cases hd
  have hps' : decNL m' o l = some ps := by
    rw [← hps]; simp only [decNL]; apply mapM_opt_congr; intro j hj
    simp only [iwN, nat?, iwA]; rw [hg.2.2.1 _ (by simp at hj; omega)]
  rw [hps']
  simp only [Option.bind_some] at hd ⊢
  exact ArrExt.mapM (fun _ _ hy => (IWGrow.erecPExtR hg).decRule hy) _ _ hd

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (a : AState)

theorem tsrmW_ok (n : Nat) : ∀ {m m' : Mem} {ro rl flo fll fpo fpl : Word} {r : List Word}
    {rules : List IRecRule} {lvls : List LIdx} {pins : List EIdx},
    tsrmW n m ro rl flo fll fpo fpl = some (r, m') → StageR dn vis fe m a →
    decPL m (rlDec m) ro.toNat rl.toNat = some rules → ro.toNat + rl.toNat ≤ iwTop m →
    hslice? (erecP m) flo.toNat fll.toNat = some lvls → hslice? (erecP m) fpo.toNat fpl.toNat = some pins →
    decPL m' (rlDec m') (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (rules.map fun rl => { rl with fire := .nested lvls pins }) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR dn vis fe m' a ∧ IWGrow m m' ∧
      MFr [] [] m m' := by
  induction n with
  | zero => intro m m' ro rl flo fll fpo fpl r rules lvls pins h; simp [tsrmW] at h
  | succ n ih =>
  intro m m' ro rl flo fll fpo fpl r rules lvls pins h hS hd hb hl hp
  by_cases h0 : rl = 0
  · rw [tsrmW.arm1 (hc1 := h0)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst h0
    have : rules = [] := by have := decPL_length _ hd; simpa using this
    subst this
    exact ⟨by simp [decPL], by simp, hS, IWGrow.refl _, MFr.refl _ _ _⟩
  have hb64 := hS.lt64 hb
  obtain ⟨eo, el, hl0⟩ := slice_step h0 hb64
  obtain ⟨l', hl'⟩ : ∃ l', rl.toNat = l' + 1 := ⟨rl.toNat - 1, by omega⟩
  rw [hl'] at hd
  obtain ⟨pp, rl0, rest, rfl, hpp, hrl0, hrest⟩ := decPL_cons hd
  have hrd := iwN_rdW hpp (by omega)
  rw [UInt64.ofNat_toNat] at hrd
  rw [tsrmW.arm2 (hc1 := h0)] at h
  cases ha : erAllocW m 11 with
  | none => rw [show trnW m (rdW (m.arr64 IW) ro) flo fll fpo fpl = none by simp [trnW, ha], tsrmW.k_tgt_rule_nested.none] at h; cases h
  | some x =>
  obtain ⟨q, m1⟩ := x
  rw [show trnW m (rdW (m.arr64 IW) ro) flo fll fpo fpl = some ([q], rmMem m1 q (rdW (m.arr64 IW) ro) flo fll fpo fpl)
    by simp [trnW, ha], tsrmW.k_tgt_rule_nested.arm1] at h
  simp only [List.headD_cons] at h
  rw [hrd.1] at h
  have hold : rlDec m (UInt64.ofNat pp : Word).toNat = some rl0 := by
    rw [UInt64.toNat_ofNat_of_lt' hrd.2]; exact hrl0
  obtain ⟨hS1, hg1, hf1, hq1⟩ := rmRec_stage ha hS hold hl hp
  generalize hM : rmMem m1 q (UInt64.ofNat pp) flo fll fpo fpl = M at h hS1 hg1 hf1 hq1
  rcases h2 : tsrmW n M (ro + 1) (rl - 1) flo fll fpo fpl with _ | ⟨rr, m2⟩ <;> simp only [h2, tsrmW.k_tgt_stored_rules_remap, reduceCtorEq] at h
  have hext := IWGrow.erecPExtR hg1
  obtain ⟨hd2, hb2, hS2, hg2, hf2⟩ := ih h2 hS1
    (decPL_rl_grow hg1 (by rw [eo, el]; omega) (by rw [eo, el, hl']; simpa using hrest))
    (by rw [eo, el]; have := hg1.1; omega) (hext.hslice? hl) (hext.hslice? hp)
  rcases h3 : consW n m2 q (rr.headD 0) (rr.tail.headD 0) with _ | ⟨rc, m3⟩ <;> simp only [h3, tsrmW.k_sl_cons, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hd3, ht3, hS3, hg3, hf3⟩ := consW_rl h3 hS2 hb2 hd2
    ((IWGrow.erecPExtR hg2).decRule hq1)
  exact ⟨by simpa using hd3, Nat.le_of_eq ht3, hS3, (hg1.trans hg2).trans hg3, (hf1.trans hf2).trans hf3⟩

end rel

/-! ## The `abstract1` memo across the rules' writers -/

theorem ruleMem_afr (m : Mem) (q a b c d e f : Word) : AFr m (ruleMem m q a b c d e f) := by
  rw [ruleMem_eq]; exact wrER_afr _ m q

theorem rgoW_afr : ∀ (n : Nat) (m m' : Mem) (vis nP cO cL rO rL o : Word) (r : List Word),
    rgoW n m vis nP cO cL rO rL o = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [rgoW] at h
  | n + 1, m, m', vis, nP, cO, cL, rO, rL, o, r, h => by
    simp only [rgoW] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    · rcases h1 : rrbF m [vis, rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO))] with _ | ⟨kr, m1⟩ <;> simp only [h1, rgoK1, reduceCtorEq] at h
      rcases h2 : erAllocW m1 11 with _ | ⟨q, m2⟩ <;> simp only [h2, rgoK2, reduceCtorEq] at h
      cases h3 : rgoW n ((ruleMem m2 q _ _ nP _ (kr.headD 0) (kr.tail.headD 0)).set64 IW o q) vis nP
          (cO + 1) (cL - 1) (rO + 1) (rL - 1) (o + 1) with
      | none => rw [h3] at h; cases h
      | some z =>
      obtain ⟨r3, m3⟩ := z
      rw [h3, rgoK3] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      exact (AFr.of_frame (rrbF_frame h1)).trans ((erAllocW_afr h2).trans
        (((ruleMem_afr _ _ _ _ _ _ _ _).trans (set64IW_afr _ _ _)).trans (rgoW_afr n _ _ _ _ _ _ _ _ _ _ h3)))

theorem rulesW_afr {n : Nat} {m m' : Mem} {vis nP cO cL rO rL : Word} {r : List Word}
    (h : rulesW n m vis nP cO cL rO rL = some (r, m')) : AFr m m' := by
  simp only [rulesW] at h
  generalize hk : (if rL < cL then rL else cL) = k at h
  rcases h1 : allocW m k with _ | ⟨o, m1⟩ <;> simp only [h1, rulesK1, reduceCtorEq] at h
  rcases h2 : rgoW n m1 vis nP cO cL rO rL o with _ | ⟨r2, m2⟩ <;> simp only [h2, rulesK2, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (allocW_afr h1).trans (rgoW_afr n _ _ _ _ _ _ _ _ _ _ h2)

theorem tsrmW_afr : ∀ (n : Nat) {m m' : Mem} {ro rl flo fll fpo fpl : Word} {r : List Word},
    tsrmW n m ro rl flo fll fpo fpl = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [tsrmW] at h
  | n + 1, m, m', ro, rl, flo, fll, fpo, fpl, r, h => by
    by_cases h0 : rl = 0
    · rw [tsrmW.arm1 (hc1 := h0)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [tsrmW.arm2 (hc1 := h0)] at h
    cases ha : erAllocW m 11 with
    | none => rw [show trnW m (rdW (m.arr64 IW) ro) flo fll fpo fpl = none by simp [trnW, ha], tsrmW.k_tgt_rule_nested.none] at h; cases h
    | some x =>
    obtain ⟨q, m1⟩ := x
    rw [show trnW m (rdW (m.arr64 IW) ro) flo fll fpo fpl =
      some ([q], rmMem m1 q (rdW (m.arr64 IW) ro) flo fll fpo fpl) by simp [trnW, ha], tsrmW.k_tgt_rule_nested.arm1] at h
    have f1 : AFr m1 (rmMem m1 q (rdW (m.arr64 IW) ro) flo fll fpo fpl) := by
      simp only [rmMem]
      exact AFr.of_frame (((((((((((MemFrame.set64 _ EREC (by decide) _ _).trans
        (MemFrame.set64 _ EREC (by decide) _ _)).trans (MemFrame.set64 _ EREC (by decide) _ _)).trans
        (MemFrame.set64 _ EREC (by decide) _ _)).trans (MemFrame.set64 _ EREC (by decide) _ _)).trans
        (MemFrame.set64 _ EREC (by decide) _ _)).trans (MemFrame.set64 _ EREC (by decide) _ _)).trans
        (MemFrame.set64 _ EREC (by decide) _ _)).trans (MemFrame.set64 _ EREC (by decide) _ _)).trans
        (MemFrame.set64 _ EREC (by decide) _ _)).trans (MemFrame.set64 _ EREC (by decide) _ _))
    generalize rmMem m1 q (rdW (m.arr64 IW) ro) flo fll fpo fpl = M at h f1
    cases h2 : tsrmW n M (ro + 1) (rl - 1) flo fll fpo fpl with
    | none => simp only [List.headD_cons, h2] at h; simp [tsrmW.k_tgt_stored_rules_remap] at h
    | some x =>
    obtain ⟨rr, m2⟩ := x
    simp only [List.headD_cons, h2, tsrmW.k_tgt_stored_rules_remap.arm1] at h
    rcases h3 : consW n m2 q (rr.headD 0) (rr.tail.headD 0) with _ | ⟨rc, m3⟩ <;> simp only [h3, tsrmW.k_sl_cons, reduceCtorEq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact (erAllocW_afr ha).trans (f1.trans ((tsrmW_afr n h2).trans (consW_afr h3)))

/-! ## `tgt_stored_rules` -/

theorem rcPoolSmall {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    (h : StageR dn vis fe m a) : PoolSmall m := by
  have := h.1.arena.1.lit.1.2.2.1
  unfold PoolSmall; omega

def efF : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, o, l => efW n m o l

def rulesF : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, nP, cO, cL, rO, rL => rulesW n m vis nP cO cL rO rL

theorem rulesF_spec (p : Prog) (L : TsrLook p) (n : Nat) (s₀ : St) (vis recName nP cO cL rO rL : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "sum_rules" [vis, recName, nP, cO, cL, rO, rL]
    ⦃fun r s' => LocEq s' s₀ ∧ rulesF n s₀.mem vis nP cO cL rO rL = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact rulesW_spec p L.ea L.srg L.rc.rx.ha L.sr L.rrb n s₀ vis recName nP cO cL rO rL

theorem efF_spec (p : Prog) (L : TsrLook p) (n : Nat) (s₀ : St) (o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "er_from_iw" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ efF n s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact efW_spec p L.ea L.efg L.ef n s₀ o l

l_model tsr_spec (p : Prog) (hL : TsrLook p)
  fns [hL.tsr ↦ tsrW]
  specs [rulesF_spec p hL n, auxRuleFire_spec p hL.arf n, efF_spec p hL n, tsrm_spec p hL n]
  grind [arena_grind] simp [getElem_rdW']

/-- A pointer-slice field `(off, len)` of a record decoded in the cut pools, at its word addresses. -/
theorem truncPl {α : Type} {f : Mem → Nat → Option α} {m : Mem} {w : Word} {i o l : Nat} {xs : List α}
    (ho : iwN (truncM m) (w.toNat + i) = some o) (hl : iwN (truncM m) (w.toNat + i + 1) = some l)
    (hd : decPL (truncM m) (f (truncM m)) o l = some xs) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    DecB (fun m' => decPL m' (f m') (rdW (m.arr64 IW) (w + UInt64.ofNat i)).toNat
      (rdW (m.arr64 IW) (w + UInt64.ofNat (i + 1))).toNat) m xs := by
  obtain ⟨-, hom⟩ := rec2IwN_trunc ho
  obtain ⟨-, hlm⟩ := rec2IwN_trunc hl
  obtain ⟨eo, to⟩ := rec2RdN (w := w) (k := i) hom hsz
  obtain ⟨el, tl⟩ := rec2RdN (w := w) (k := i + 1) (by simpa [Nat.add_assoc] using hlm) hsz
  show decPL (truncM m) (f (truncM m)) _ _ = some xs
  rw [eo, el, to, tl]; exact hd

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem tsrW_ok (n : Nat) {m m' : Mem} {a : AState} {cv rP M rhso rhsl : Word} {r : List Word}
    {cvv : IConstantVal} {TM : TargetMajor} {rhss : List EIdx}
    (h : tsrW n m vis cv rP M rhso rhsl = some (r, m')) (hS : StageR dn vis fe m a)
    (hM : DecB (fun m => decTM m M.toNat) m TM) (hrh : DecB (fun m => decHL m rhso.toNat rhsl.toNat) m rhss)
    (hA : AbsOK m) :
    ∃ rules a', (ConRon.Arena.tgtStoredRules fe cvv rP.toNat TM rhss).run a = .ok (rules, a') ∧
      decPL m' (rlDec m') (r.headD 0).toNat (r.tail.headD 0).toNat = some rules ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      AbsOK m' := by
  obtain _ | n := n
  · simp [tsrW] at h
  rw [tsrW.arm1] at h
  have hsz := hS.2.2.2.1
  have hM0 : decTM (truncM m) M.toNat = some TM := hM
  -- the constructors' slice, the parameter count, the member word
  have hT := hM0
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hT
  obtain ⟨i0, -, l0, -, ds0, -, nP, hnP, nI, -, cs, hcs, k8, hk8, nfs0, -, pf0, -, hTM⟩ := hT
  have eCs : TM.ctors = cs := by rw [← hTM]
  have eNP : TM.nPc = nP := by rw [← hTM]
  have eMem : TM.member = decON k8 := by rw [← hTM]
  obtain ⟨co, cl, hco, hcl, hcsd⟩ := decAt_some hcs
  have hctors := truncPl (f := fun m => decCN m) (w := M) (i := 6) hco (by simpa [Nat.add_assoc] using hcl) hcsd hsz
  simp only [show UInt64.ofNat 6 = (6 : Word) from rfl, show UInt64.ofNat (6 + 1) = (7 : Word) from rfl] at hctors
  obtain ⟨-, hnPm⟩ := rec2IwN_trunc hnP
  obtain ⟨e4, t4⟩ := rec2RdN (w := M) (k := 4) hnPm hsz
  simp only [show UInt64.ofNat 4 = (4 : Word) from rfl] at e4
  obtain ⟨hM8, hk8m⟩ := rec2IwN_trunc hk8
  obtain ⟨e8, t8⟩ := rec2RdN (w := M) (k := 8) hk8m hsz
  simp only [show UInt64.ofNat 8 = (8 : Word) from rfl] at e8
  cases n with
  | zero => simp [rulesF, tsrW.k_sum_rules] at h
  | succ k =>
  cases h1 : rulesW k m vis (rdW (m.arr64 IW) (M + 4)) (rdW (m.arr64 IW) (M + 6)) (rdW (m.arr64 IW) (M + 7))
      rhso rhsl with
  | none => simp only [rulesF] at h; rw [h1] at h; simp [tsrW.k_sum_rules] at h
  | some x =>
  obtain ⟨rs, m1⟩ := x
  simp only [rulesF] at h; rw [h1] at h
  obtain ⟨rules, a1, run1, hS1, hg1, hd1, hb1⟩ := rulesW_ok cvv.name k m a _ _ _ rhso rhsl _ rhss hS hctors hrh
    rs m1 h1
  rw [e4, t4] at run1
  have hA1 := rulesW_afr h1 hA
  have e8' : rdW (m1.arr64 IW) (M + 8) = UInt64.ofNat k8 := by
    rw [rdW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega), e8]
  by_cases hmem : rdW (m1.arr64 IW) (M + 8) ≠ 0
  · rw [tsrW.k_sum_rules.arm1 (hc1 := hmem)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hk0 : k8 ≠ 0 := by intro e; apply hmem; rw [e8', e]; rfl
    refine ⟨rules, a1, ?_, by simpa using hd1, by simpa using hb1, hS1, hg1, hA1⟩
    simp only [ConRon.Arena.tgtStoredRules, StateT.run_bind, eCs, eNP, run1, except_ok_bind, eMem, decON, hk0,
      ite_false]
    rfl
  rw [tsrW.k_sum_rules.arm2 (hc1 := Decidable.of_not_not hmem)] at h
  have hk0 : k8 = 0 := by
    have : rdW (m1.arr64 IW) (M + 8) = 0 := by simpa using hmem
    rw [e8'] at this; have := congrArg UInt64.toNat this; rwa [t8] at this
  rcases h2 : arfW (k + 1) m1 M rP with _ | ⟨rf, m2⟩ <;> simp only [h2, tsrW.k_aux_rule_fire, reduceCtorEq] at h
  obtain ⟨f, a2, run2, ⟨hS2, hg2, hdf⟩, hA2⟩ := arfW_sim dn vis fe (k + 1) m1 a1 M rP TM hS1
    (hM.grow (decTM_mono _) hg1) (rcPoolSmall hS1) hA1 (rf, m2) h2
  cases f with
  | plain => exact absurd hdf (by simp [decFire])
  | nested lvls pins =>
  obtain ⟨-, ⟨hdl, hbl⟩, ⟨hdp, hbp⟩⟩ := hdf
  simp only [getD_one, getD_two, getD_three, getD_four, show (1 + 1 : Nat) = 2 from rfl,
    show (3 + 1 : Nat) = 4 from rfl] at hdl hbl hdp hbp
  rcases h3 : efF (k + 1) m2 (rf.tail.headD 0) (rf.tail.tail.headD 0) with _ | ⟨re, m3⟩ <;> simp only [h3, tsrW.k_er_from_iw, reduceCtorEq] at h
  obtain ⟨hS3, hg3, hre1, hre0, hsl3, -⟩ := efW_stage k h3 hS2 hdl hbl
  rcases h4 : efF (k + 1) m3 (rf.tail.tail.tail.headD 0) (rf.tail.tail.tail.tail.headD 0) with _ | ⟨rp, m4⟩ <;> simp only [h4, tsrW.k_er_from_iw_2, reduceCtorEq] at h
  obtain ⟨hS4, hg4, hrp1, hrp0, hsl4, -⟩ := efW_stage k h4 hS3
    (by rw [decHL_grow hg3 hbp]; exact hdp) (by have := hg3.1; omega)
  rcases h5 : tsrmW (k + 1) m4 (rs.headD 0) (rs.tail.headD 0) (re.headD 0) (re.tail.headD 0) (rp.headD 0)
      (rp.tail.headD 0) with _ | ⟨r5, m5⟩ <;> simp only [h5, tsrW.k_tgt_stored_rules_remap, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  have hg24 := (hg2.trans hg3).trans hg4
  rw [← hre1] at hsl3; rw [← hrp1] at hsl4
  obtain ⟨hd5, hb5, hS5, hg5, -⟩ := tsrmW_ok dn fe vis a2 (k + 1) h5 hS4
    (decPL_rl_grow hg24 (by have := hg1.2; omega) (by simpa using decPL_rl_grow (IWGrow.refl _) (by simpa using hb1) hd1))
    (by have := hg24.1; simpa using (by omega : (rs.headD 0).toNat + (rs.tail.headD 0).toNat ≤ iwTop m4))
    ((IWGrow.erecPExtR hg4).hslice? hsl3) hsl4
  refine ⟨_, a2, ?_, by simpa using hd5, by simpa using hb5, hS5, (((hg1.trans hg2).trans hg3).trans hg4).trans hg5,
    tsrmW_afr _ h5 (efW_afr h4 (efW_afr h3 hA2))⟩
  simp only [ConRon.Arena.tgtStoredRules, StateT.run_bind, eCs, eNP, run1, except_ok_bind, eMem, decON, hk0,
    ite_true]
  rw [run2]; rfl

end rel

end L.Ind

end

end
