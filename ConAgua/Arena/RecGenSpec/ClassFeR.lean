import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.RecClassSpec.ClassGenRecTy
import ConAgua.Arena.RecClassSpec.ClassNPcOf
import ConAgua.Arena.RecGenSpec.Rec3CVX
import ConAgua.Arena.RecGenSpec.RgW
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# ClassFeR: `ConRon.Arena.classFeR`

The refinement theorems `classFeR_refines` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A constant record below the top decodes in the record pool in use. -/
theorem rec2DecCV_erecP {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp m q = some cv) (hq : CVExt m q) :
    decCV (erecP m) q = some cv := by
  rw [rec2DecCV_agree (a := erA m) (T := erTop m) (fun i hi => ?_) hq.1 hq.2]
  · exact h
  · simp only [erecP, erA, Array.getElem?_extract, erecTop, erTop] at hi ⊢
    simp only [Nat.zero_add]
    split <;> simp_all <;> omega

def rtoK1 (cR : CallM) (n : Nat) (vis g rc cvRi c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => rtoK2 cR n vis rc cvRi (gtW n m1 g c)

/-- **The model of `class_rec_ty_ok`.** -/
def rtoW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, g, k, rc, cvRi, c => rtoK1 cR n vis g rc cvRi c (rgW n m g k rc c)

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

theorem rec3SPL_uncons {m : Mem} {o l : Nat} {cvs : List IConstantVal} (h : SPL decCVX m o (l + 1) cvs) :
    ∃ p cv cvs', cvs = cv :: cvs' ∧ iwN m o = some p ∧ o < iwTop m ∧
      StabD (fun m => decCVX m p) m cv ∧ SPL decCVX m (o + 1) l cvs' := by
  obtain ⟨hb, ps, hps, hf⟩ := h
  rw [decNL_succ] at hps
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hps
  obtain ⟨p, hp, ps', hps', rfl⟩ := hps
  cases hf with
  | cons h1 h2 => exact ⟨p, _, _, rfl, hp, by omega, h1, by omega, ps', hps', h2⟩

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

/-! ## `class_fe_r_rec` -/

/-- The memory after `class_fe_r_rec`'s nine writes (each copy reads the memory of its time). -/
def cfrMem (m1 : Mem) (q cv mi rp3 : Word) : Mem :=
  let m2 := m1.set64 EREC q 5
  let m3 := m2.set64 EREC (q + 1) (rdW (m2.arr64 EREC) cv)
  let m4 := m3.set64 EREC (q + 2) (rdW (m3.arr64 EREC) (cv + 1))
  let m5 := m4.set64 EREC (q + 3) (rdW (m4.arr64 EREC) (cv + 2))
  let m6 := m5.set64 EREC (q + 4) (rdW (m5.arr64 EREC) (cv + 3))
  ((((m6.set64 EREC (q + 5) mi).set64 EREC (q + 6) rp3).set64 EREC (q + 7) 0).set64 EREC (q + 8) 0)

/-- The model of `class_fe_r_rec(cv, mi, rp3)`. -/
def cfrRecW (m : Mem) (cv mi rp3 : Word) : Option (Word × Mem) :=
  match erAllocW m 9 with
  | none => none
  | some (q, m1) =>
    if 4294967296 ≤ rdW ((cfrMem m1 q cv mi rp3).arr64 EREC) (q + 1) then none
    else some (q, cfrMem m1 q cv mi rp3)

theorem cfrRec_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hp : p.lookup "class_fe_r_rec" = some classFeRRec) (n : Nat) (s₀ : St) (cv mi rp3 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fe_r_rec" [cv, mi, rp3]
    ⦃fun r s' => LocEq s' s₀ ∧ cfrRecW s₀.mem cv mi rp3 = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, classFeRRec]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        erecAlloc_specW p ha n] <;>
      finish [cfrRecW, cfrMem]

/-! ## `class_fe_r_go`: the word model -/

/-- The recursor record's major index and rule prefix (`0`, `0` off the list). -/
def ferMi (m : Mem) (ro rl M : Word) : Word :=
  if M < rl then rdW (m.arr64 IW) (rdW (m.arr64 IW) (ro + M) + 2) else 0
def ferRp (m : Mem) (ro rl M : Word) : Word :=
  if M < rl then rdW (m.arr64 IW) (rdW (m.arr64 IW) (ro + M) + 1) else 0

def ferK5 (v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => some ([v, r5.headD 0, r5.tail.headD 0], m5)

def ferK4 (n : Nat) (y : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => ferK5 (r4.headD 0) (consW n m4 y (r4.tail.headD 0) (r4.tail.tail.headD 0))

mutual
/-- **The model of `class_fe_r_go`.** -/
def ferW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, cvo, cvl, rcl, ro, rl, vis, M =>
    if cvl = 0 then some ([vis, 0, 0], m)
    else if rcl = 0 then some ([vis, 0, 0], m)
    else if 2 < tagW (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo)) then none
    else ferK1 p n cvo cvl rcl ro rl M (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo))
      (rowCW m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo))) (rowPW m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo)))
      vis (cfrRecW m (rdW (m.arr64 IW) cvo) (ferMi m ro rl M) (ferRp m ro rl M))
def ferK1 (p : Prog) (n : Nat) (cvo cvl rcl ro rl M nm c q vis : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (kq, m1) => ferK2 p n cvo cvl rcl ro rl M nm c q (callW p n "env_push" [vis, kq] m1)
def ferK2 (p : Prog) (n : Nat) (cvo cvl rcl ro rl M nm c q : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rv, m2) => ferK3 p n cvo cvl rcl ro rl M (rv.headD 0) (recW m2 3 [nm, c, q])
def ferK3 (p : Prog) (n : Nat) (cvo cvl rcl ro rl M v : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (re, m3) => ferK4 n (re.headD 0) (ferW p n m3 (cvo + 1) (cvl - 1) (rcl - 1) ro rl v (M + 1))
end

section arms
variable (p : Prog) (n : Nat) (m m1 m2 m3 m4 m5 : Mem)
  (cvo cvl rcl ro rl vis M nm c q kq v y pp cgo cgl rco : Word) (r1 r2 r3 r4 r5 : List Word)
theorem ferMi_hit (h : M < rl) : ferMi m ro rl M = rdW (m.arr64 IW) (rdW (m.arr64 IW) (ro + M) + 2) := by
  simp [ferMi, h]
theorem ferMi_miss (h : ¬ M < rl) : ferMi m ro rl M = 0 := by simp [ferMi, h]
theorem ferRp_hit (h : M < rl) : ferRp m ro rl M = rdW (m.arr64 IW) (rdW (m.arr64 IW) (ro + M) + 1) := by
  simp [ferRp, h]
theorem ferRp_miss (h : ¬ M < rl) : ferRp m ro rl M = 0 := by simp [ferRp, h]
theorem ferW_nil1 (h : cvl = 0) : ferW p (n + 1) m cvo cvl rcl ro rl vis M = some ([vis, 0, 0], m) := by
  simp [ferW, h]
theorem ferW_nil2 (h1 : ¬ cvl = 0) (h : rcl = 0) :
    ferW p (n + 1) m cvo cvl rcl ro rl vis M = some ([vis, 0, 0], m) := by
  simp only [ferW]; rw [ite_eq_right h1, ite_eq_left h]
theorem ferW_tag (h1 : ¬ cvl = 0) (h2 : ¬ rcl = 0) (h : 2 < tagW (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo))) :
    ferW p (n + 1) m cvo cvl rcl ro rl vis M = none := by
  simp only [ferW]; rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h]
theorem ferW_cons (h1 : ¬ cvl = 0) (h2 : ¬ rcl = 0) (h : ¬ 2 < tagW (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo))) :
    ferW p (n + 1) m cvo cvl rcl ro rl vis M =
      ferK1 p n cvo cvl rcl ro rl M (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo))
        (rowCW m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo))) (rowPW m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo)))
        vis (cfrRecW m (rdW (m.arr64 IW) cvo) (ferMi m ro rl M) (ferRp m ro rl M)) := by
  simp only [ferW]; rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h]
theorem ferK1_some : ferK1 p n cvo cvl rcl ro rl M nm c q vis (some (kq, m1)) =
    ferK2 p n cvo cvl rcl ro rl M nm c q (callW p n "env_push" [vis, kq] m1) := by rw [ferK1]
theorem ferK2_some : ferK2 p n cvo cvl rcl ro rl M nm c q (some (r2, m2)) =
    ferK3 p n cvo cvl rcl ro rl M (r2.headD 0) (recW m2 3 [nm, c, q]) := by rw [ferK2]
theorem ferK3_some : ferK3 p n cvo cvl rcl ro rl M v (some (r3, m3)) =
    ferK4 n (r3.headD 0) (ferW p n m3 (cvo + 1) (cvl - 1) (rcl - 1) ro rl v (M + 1)) := by rw [ferK3]
theorem ferK4_some : ferK4 n y (some (r4, m4)) =
    ferK5 (r4.headD 0) (consW n m4 y (r4.tail.headD 0) (r4.tail.tail.headD 0)) := rfl
theorem ferK5_some : ferK5 v (some (r5, m5)) = some ([v, r5.headD 0, r5.tail.headD 0], m5) := rfl
end arms
attribute [ind_grind] ferMi_hit ferMi_miss ferRp_hit ferRp_miss ferW_nil1 ferW_nil2 ferW_tag ferW_cons
  ferK1_some ferK2_some ferK3_some ferK4_some ferK5_some

/-- The lookups of `class_fe_r`. -/
structure CfrProg (p : Prog) : Prop where
  rp : RecProg p
  ix : p.lookup "env_ix" = some envIxL
  rg : p.lookup "env_row_get" = some envRowGetL
  ia : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  rec3 : p.lookup "rec3" = some rec3
  frec : p.lookup "class_fe_r_rec" = some classFeRRec
  go : p.lookup "class_fe_r_go" = some classFeRGo
  top : p.lookup "class_fe_r" = some classFeRL

set_option maxHeartbeats 1000000 in
theorem classFeRGo_spec (p : Prog) (h : CfrProg p) (n : Nat) :
    ∀ (s₀ : St) (cvo cvl rcl ro rl vis M : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fe_r_go" [cvo, cvl, rcl, ro, rl, vis, M]
    ⦃fun r s' => LocEq s' s₀ ∧ ferW p n s₀.mem cvo cvl rcl ro rl vis M = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ cvo cvl rcl ro rl vis M
    rw [invoke_eq _ h.go]; simp only [callFn, classFeRGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ cvo cvl rcl ro rl vis M
    rw [invoke_eq _ h.go]
    simp only [callFn, classFeRGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        rowGet_specW p h.ix h.rg n, cfrRec_specW p h.rp.alloc h.frec n, callW_spec p n "env_push",
        rec3_specW p h.ia n h.rec3, slCons_specW p h.ia h.copy h.cons n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, loc_init4, loc_init5, loc_init6]

l_model classFeR_spec (p : Prog) (h : CfrProg p)
  fns [h.top ↦ ferAW]
  specs [classFeRGo_spec p h n]
  grind [arena_grind] simp [getElem_rdW']

/-! ## `class_fe_r_rec` under the stage relation -/

theorem cfrMem_eq {m1 : Mem} {q cq mi rp3 : Word} (hlt : cq.toNat + 4 ≤ q.toNat) (hq : q.toNat + 9 < 2 ^ 64) :
    cfrMem m1 q cq mi rp3 = wrER m1 q [5, rdW (m1.arr64 EREC) cq, rdW (m1.arr64 EREC) (cq + 1),
      rdW (m1.arr64 EREC) (cq + 2), rdW (m1.arr64 EREC) (cq + 3), mi, rp3, 0, 0] := by
  have t1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have t2 : (q + 2).toNat = q.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have t3 : (q + 3).toNat = q.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have c1 : (cq + 1).toNat = cq.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have c2 : (cq + 2).toNat = cq.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have c3 : (cq + 3).toNat = cq.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  simp only [cfrMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl, show q + 6 + 1 = q + 7 by ac_rfl, show q + 7 + 1 = q + 8 by ac_rfl]
  simp (disch := ((try simp only [t1, t2, t3, c1, c2, c3]); omega)) only [rdW_set64_ne_er]

/-- **`class_fe_r_rec` under the stage relation**: a fresh rule-less `.recInfo` record of the constant
at `cq`. -/
theorem cfrRec_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cq mi rp3 q : Word} {cv : IConstantVal} (h : cfrRecW m cq mi rp3 = some (q, m'))
    (hS : StageR dn vis fe m a) (hcv : decCV (erecP m) cq.toNat = some cv) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') dn q.toNat = some (.recInfo cv mi.toNat rp3.toNat []) := by
  rcases h1 : erAllocW m 9 with _ | ⟨q1, m1⟩
  · simp [cfrRecW, h1] at h
  have e : cfrRecW m cq mi rp3 = if 4294967296 ≤ rdW ((cfrMem m1 q1 cq mi rp3).arr64 EREC) (q1 + 1)
      then none else some (q1, cfrMem m1 q1 cq mi rp3) := by simp [cfrRecW, h1]
  rw [e] at h
  split at h
  · cases h
  obtain ⟨rfl, rfl⟩ : q1 = q ∧ cfrMem m1 q1 cq mi rp3 = m' := by simpa using h
  have h3 : (erecP m)[cq.toNat + 3]? ≠ none := by
    have := decCV_type hcv; intro e; simp [hd?, e] at this
  have hcq : cq.toNat + 4 ≤ erTop m := by
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h3; have := erecP_lt hv; omega
  have ⟨hq1, hE1⟩ : q1.toNat = erTop m ∧ m1.arr64 EREC = m.arr64 EREC := by
    simp only [erAllocW] at h1; split at h1; · cases h1
    split at h1; · cases h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h1)
    exact ⟨rfl, by simp only [erAllocMem]; exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)⟩
  obtain ⟨-, hEtop, -, hEsz, -⟩ := hS.2
  obtain ⟨hS', hg, -, htop', hget⟩ := erRec_stage h1 hS [5, rdW (m.arr64 EREC) cq,
    rdW (m.arr64 EREC) (cq + 1), rdW (m.arr64 EREC) (cq + 2), rdW (m.arr64 EREC) (cq + 3), mi, rp3, 0, 0]
    (by simp)
  have hroom : q1.toNat + 9 < 2 ^ 64 := by
    obtain ⟨-, h2, -, h4, -⟩ := hS'.2; simp only [List.length_cons, List.length_nil] at htop'; omega
  rw [cfrMem_eq (by omega) hroom, hE1]
  refine ⟨hS', hg, ?_⟩
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
        rdW (m.arr64 EREC) (cq + 3), mi, rp3, 0, 0] : List Word)[j]'(by simpa using hj)).toNat := by
    intro j hj
    simp only [nat?, hP j hj, hget j (by simpa using hj)]
    rw [List.getElem?_eq_getElem (by simp; omega)]; rfl
  have n0 := nk 0 (by decide)
  have n5 := nk 5 (by decide)
  have n6 := nk 6 (by decide)
  have n7 := nk 7 (by decide)
  have n8 := nk 8 (by decide)
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at n0 n5 n6 n7 n8
  simp only [decCI, Option.bind_eq_bind, n0, Option.bind_some, hcv', n5, n6, n7, n8, Option.pure_def]
  simp [decRules]

/-! ## The twin's accumulator, the displaced rows -/

theorem rec3FerGo_acc (P : BlockShape) : ∀ (L : List (IConstantVal × Nat)) (k : Nat) (fe : IFEnv)
    (prevs : List (NIdx × Option (Nat × IConstantInfo))),
    ConRon.Arena.classFeR.go P k L fe prevs =
      ((ConRon.Arena.classFeR.go P k L fe []).1, prevs ++ (ConRon.Arena.classFeR.go P k L fe []).2)
  | [], k, fe, prevs => by rw [ConRon.Arena.classFeR.go.eq_1, ConRon.Arena.classFeR.go.eq_1]; simp
  | (cv, c) :: rest, k, fe, prevs => by
    rw [ConRon.Arena.classFeR.go.eq_2, ConRon.Arena.classFeR.go.eq_2]
    rw [rec3FerGo_acc P rest _ _ (prevs ++ _), rec3FerGo_acc P rest _ _ ([] ++ _)]
    simp

/-- The row of a name handle, as `env_pop_temp` takes it back, is the twin's `idx` entry. -/
theorem rec3PrevD {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}
    (h : EnvR dn m vis fe) {w : Word} (hw : w.toNat < 2 ^ 32) (ht : rowTag w ≤ 2) :
    prevD dn m (rowC m w) (rowP m w) = some (fe.idx[(decI w : NIdx)]?) := by
  have hk := h.keys (decI w) (by rwa [decI_word_self w hw])
  have hv := h.vals (decI w) (by rwa [decI_word_self w hw])
  rw [decI_word_self w hw] at hk hv
  unfold prevD
  by_cases h0 : rowC m w = 0
  · simp only [L.Arena.rowW, h0, ite_true, Option.map_none] at hk
    have : fe.idx[(decI w : NIdx)]? = none := by cases e : fe.idx[(decI w : NIdx)]? <;> simp_all
    simp [this, h0]
  · simp only [L.Arena.rowW, h0, ite_false, Option.map_some] at hk
    have hv := hv h0
    rw [ite_eq_right h0]
    cases e : fe.idx[(decI w : NIdx)]? with
    | none => simp [e] at hk
    | some r =>
      obtain ⟨c, ci⟩ := r
      simp only [e, Option.map_some, Option.some.injEq] at hk hv
      rw [← hv]; simp [hk]

theorem rec3PrevD_grow {dn : NIdx → Option ConLeche.Name} {m m' : Mem} (hg : IWGrow m m') {c q : Word}
    {x : Option (Nat × IConstantInfo)} (h : prevD dn m c q = some x) : prevD dn m' c q = some x := by
  unfold prevD at h ⊢
  split
  · rename_i h0; rw [ite_eq_left h0] at h; exact h
  · rename_i h0; rw [ite_eq_right h0] at h
    obtain ⟨ci, hci, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [ArrExt.decCI (IWGrow.erecPExtR hg) hci]; rfl

/-- A displaced row `[name, c, q]` (a `rec3` record). -/
def decPrev (dn : NIdx → Option ConLeche.Name) (m : Mem) (p : Nat) :
    Option (NIdx × Option (Nat × IConstantInfo)) := do
  let nm ← (iwH m p : Option NIdx)
  let c ← (iwA m)[p + 1]?
  let q ← (iwA m)[p + 2]?
  let pv ← prevD dn m c q
  pure (nm, pv)

theorem rec3DecPrev_stab {dn : NIdx → Option ConLeche.Name} {m : Mem} {p : Nat}
    {x : NIdx × Option (Nat × IConstantInfo)} (h : decPrev dn m p = some x) (hp : p + 3 ≤ iwTop m) :
    StabD (fun m => decPrev dn m p) m x := by
  intro m' hg
  have e : ∀ i, i < iwTop m → (iwA m')[i]? = (iwA m)[i]? := fun i hi => hg.2.2.1 i hi
  simp only [decPrev, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h ⊢
  obtain ⟨nm, hnm, c, hc, q, hq, pv, hpv, rfl⟩ := h
  refine ⟨nm, ?_, c, by rw [e _ (by omega)]; exact hc, q, by rw [e _ (by omega)]; exact hq, pv,
    rec3PrevD_grow hg hpv, rfl⟩
  simp only [iwH, hd?] at hnm ⊢; rw [e _ (by omega)]; exact hnm

/-! ## `class_fe_r_go`: the relation to the twin -/

/-- The record's major index and rule prefix are the twin's. -/
theorem rec3FerMiRp {m : Mem} {ro rl M : Word} {P : BlockShape}
    (hrecs : DecB (fun m => decPL m (decRS m) ro.toNat rl.toNat) m P.recs) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (ferMi m ro rl M).toNat = P.majorIdxAt M.toNat ∧ (ferRp m ro rl M).toNat = P.rulePrefixAt M.toNat := by
  have hlen := decPL_length _ hrecs
  by_cases hM : M < rl
  · rw [ferMi_hit (h := hM), ferRp_hit (h := hM)]
    have hM' : M.toNat < rl.toNat := UInt64.lt_iff_toNat_lt.mp hM
    obtain ⟨v, hv, hRS⟩ := decPL_getH (truncM m) hrecs M.toNat hM'
    obtain ⟨-, -, -, hrP, hmI, -⟩ := rec2DecRS_parts hRS
    obtain ⟨ev, tv⟩ := rec2RdN (w := ro) (k := M.toNat) (rec2IwN_trunc hv).2 hsz
    rw [UInt64.ofNat_toNat] at ev
    obtain ⟨e2, t2⟩ := rec2RdN (w := UInt64.ofNat v) (k := 2) (by rw [tv]; exact (rec2IwN_trunc hmI).2) hsz
    obtain ⟨e1, t1⟩ := rec2RdN (w := UInt64.ofNat v) (k := 1) (by rw [tv]; exact (rec2IwN_trunc hrP).2) hsz
    simp only [show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 1 = (1 : Word) from rfl] at e1 e2
    rw [ev, e2, e1, t2, t1]
    simp [ConRon.Arena.BlockShape.majorIdxAt, ConRon.Arena.BlockShape.rulePrefixAt,
      List.getElem?_eq_getElem (show M.toNat < P.recs.length by omega)]
  · rw [ferMi_miss (h := hM), ferRp_miss (h := hM)]
    have hM' : ¬ M.toNat < rl.toNat := fun x => hM (UInt64.lt_iff_toNat_lt.mpr x)
    simp [ConRon.Arena.BlockShape.majorIdxAt, ConRon.Arena.BlockShape.rulePrefixAt,
      List.getElem?_eq_none (show P.recs.length ≤ M.toNat by omega)]

theorem ferW_ok (p : Prog) (hp : CfrProg p) (dn : NIdx → Option ConLeche.Name) (P : BlockShape)
    (ro rl : Word) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (vis : Word) (fe : IFEnv) (cvo cvl rcl M : Word) (cvs : List IConstantVal)
      (rcs : List Nat) (r : List Word),
    ferW p k m cvo cvl rcl ro rl vis M = some (r, m') → StageR dn vis fe m a →
    DecB (fun m => decPL m (decRS m) ro.toNat rl.toNat) m P.recs →
    SPL decCVX m cvo.toNat cvl.toNat cvs → rcs.length = rcl.toNat → M.toNat + cvl.toNat < 2 ^ 64 →
    StageR dn (r.headD 0) (ConRon.Arena.classFeR.go P M.toNat (cvs.zip rcs) fe []).1 m' a ∧ IWGrow m m' ∧
      SPL (decPrev dn) m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat
        (ConRon.Arena.classFeR.go P M.toNat (cvs.zip rcs) fe []).2 := by
  induction k with
  | zero => intro m m' a vis fe cvo cvl rcl M cvs rcs r h; simp [ferW] at h
  | succ k ih =>
  intro m m' a vis fe cvo cvl rcl M cvs rcs r h hS hrecs hcvs hrcs hMb
  have hsz := hS.2.2.2.1
  by_cases hz : cvl = 0 ∨ rcl = 0
  · have hz' : cvs.zip rcs = [] := by
      rcases hz with hvl | hcl
      · have := hcvs.length; rw [hvl] at this; simp [List.eq_nil_of_length_eq_zero (by simpa using this)]
      · simp [List.eq_nil_of_length_eq_zero (show rcs.length = 0 by rw [hrcs, hcl]; rfl)]
    rw [show ferW p (k + 1) m cvo cvl rcl ro rl vis M = some ([vis, 0, 0], m) by
      by_cases hvl : cvl = 0
      · exact ferW_nil1 p k m cvo cvl rcl ro rl vis M hvl
      · exact ferW_nil2 p k m cvo cvl rcl ro rl vis M hvl (hz.resolve_left hvl)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); rw [hz']
    exact ⟨by simpa [ConRon.Arena.classFeR.go.eq_1] using hS, IWGrow.refl m,
      by simpa [ConRon.Arena.classFeR.go.eq_1] using SPL.nil (dec := decPrev dn) (m := m) 0 (by omega)⟩
  obtain ⟨hvl, hcl⟩ := not_or.mp hz
  obtain ⟨jv, hjv⟩ : ∃ j, cvl.toNat = j + 1 :=
    ⟨cvl.toNat - 1, by have : cvl.toNat ≠ 0 := fun e => hvl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  obtain ⟨p0, cv, cvs', rfl, hp0, hp0t, hcvS, hcvsT⟩ := rec3SPL_uncons (by rw [← hjv]; exact hcvs)
  obtain _ | ⟨rc0, rcs'⟩ := rcs
  · exact absurd (UInt64.toNat_inj.mp (by simpa using hrcs.symm)) hcl
  obtain ⟨e0, t0⟩ := rec2RdN (w := cvo) (k := 0) (by simpa using hp0) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at e0
  obtain ⟨hcvp, hcvx⟩ := rec3CVX hcvS
  obtain ⟨w, hw, hwH, hwnm⟩ := decCV_name (show decCV (erA m) p0 = some cv from hcvp)
  have ew : rdW (m.arr64 EREC) (UInt64.ofNat p0) = w := rdW_of_get? t0.symm hw
  by_cases htg : 2 < tagW (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo))
  · rw [ferW_tag (h1 := hvl) (h2 := hcl) (h := htg)] at h; cases h
  rw [ferW_cons (h1 := hvl) (h2 := hcl) (h := htg)] at h
  rw [e0, ew] at h htg
  have ht2 : tagW w ≤ 2 := by
    have : ¬ (2 : Word).toNat < (tagW w).toNat := fun e => htg (UInt64.lt_iff_toNat_lt.mpr e)
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have htag : rowTag w ≤ 2 := by rw [← tagW_toNat]; exact UInt64.le_iff_toNat_le.mp ht2
  rw [rowCW_eq m w hwH ht2, rowPW_eq m w hwH ht2] at h
  have hprev := rec3PrevD hS.1.env hwH htag
  obtain ⟨hmi, hrp⟩ := rec3FerMiRp (M := M) hrecs hsz
  -- the record
  obtain ⟨⟨kq, m1⟩, h1, h⟩ := of_K h (by simp only [ferK1])
  rw [ferK1_some] at h
  obtain ⟨hS1, hg1, hci⟩ := cfrRec_stage h1 hS (by rw [t0]; exact rec2DecCV_erecP hcvp hcvx)
  rw [hmi, hrp] at hci
  -- the push
  obtain ⟨wn, hwn, hwnl, -⟩ := decCI_name hci
  have hwn' : (rdW (m1.arr64 EREC) (kq + 1)).toNat < 2 ^ 32 := by
    have hq1 : (kq + 1).toNat = kq.toNat + 1 := by
      have := erecP_lt hwn; obtain ⟨-, h2, -, h4, -⟩ := hS1.2; rw [UInt64.toNat_add]; simp; omega
    rw [rdW_of_get? hq1.symm (erecP_get hwn)]; exact hwnl
  obtain ⟨⟨rv, m2⟩, h2, h⟩ := of_K h (by simp only [ferK2])
  rw [ferK2_some] at h
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (envPush_specW p hp.rp k ⟨m1, Locals.init []⟩ vis kq hwn') h2
  obtain ⟨hS2, hg2⟩ := envPushW_ok hW2 hS1 hci
  -- the displaced row
  obtain ⟨⟨re, m3⟩, h3, h⟩ := of_K h (by simp only [ferK3])
  rw [ferK3_some] at h
  obtain ⟨hS3, hg3, hre, hget3, htop3⟩ := recW_stage h3 hS2 rfl
  have hg03 := (hg1.trans hg2).trans hg3
  have hent : decPrev dn m3 (re.headD 0).toNat = some (cv.name, fe.idx[cv.name]?) := by
    rw [hre]
    simp only [List.headD_cons, decPrev, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
    have g0 := hget3 0 (by simp); have g1 := hget3 1 (by simp); have g2 := hget3 2 (by simp)
    simp only [Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ] at g0 g1 g2
    refine ⟨decI w, ?_, rowC m w, g1, rowP m w, g2, _, rec3PrevD_grow hg03 hprev, by rw [hwnm]⟩
    simp only [iwH, hd?, iwA, g0]; simp [hwH]
  have hentS := rec3DecPrev_stab hent (by
    have := htop3; simp only [List.length_cons, List.length_nil, iwTop] at this
    rw [hre]; simp only [List.headD_cons, iwTop]; omega)
  -- the rest
  have hcvo1 := rec2ToNat_succ (o := cvo) (i := cvo.toNat) (Nat.le_refl _) (by have := hS.2.1; omega)
  have hcvl1 := rec2ToNat_pred hvl
  have hrcl1 := rec2ToNat_pred hcl
  have hM1 : (M + 1).toNat = M.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h rfl
  rw [ferK4_some] at h
  obtain ⟨hS4, hg4, hsp4⟩ := ih m3 m4 a (rv.headD 0) _ (cvo + 1) (cvl - 1) (rcl - 1) (M + 1) cvs' rcs' r4 h4 hS3
    (hrecs.grow (OMono.decPL (fun q => decRS_mono q) _ _) hg03)
    (by rw [hcvo1, hcvl1, hjv]; exact hcvsT.grow hg03) (by simp at hrcs; omega) (by omega)
  obtain ⟨⟨r5, m5⟩, h5, h⟩ := of_K h rfl
  rw [ferK5_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS5, hg5, hsp5⟩ := SPL.cons h5 hS4 hsp4 (hentS.grow hg4)
  have htw : ConRon.Arena.classFeR.go P M.toNat ((cv :: cvs').zip (rc0 :: rcs')) fe [] =
      ((ConRon.Arena.classFeR.go P (M.toNat + 1) (cvs'.zip rcs')
        (fe.push (.recInfo cv (P.majorIdxAt M.toNat) (P.rulePrefixAt M.toNat) [])) []).1,
       (cv.name, fe.idx[cv.name]?) :: (ConRon.Arena.classFeR.go P (M.toNat + 1) (cvs'.zip rcs')
        (fe.push (.recInfo cv (P.majorIdxAt M.toNat) (P.rulePrefixAt M.toNat) [])) []).2) := by
    simp only [List.zip_cons_cons, ConRon.Arena.classFeR.go]
    rw [rec3FerGo_acc]; simp
  rw [hM1] at hS4 hS5 hsp5
  rw [htw]
  refine ⟨by simpa using hS5, (hg03.trans hg4).trans hg5, by simpa using hsp5⟩

/-- **`class_fe_r` refines `classFeR`**: the rule-less generated recursors pushed (the stage relation
at the returned view of the twin's environment), the displaced rows a stable slice of `rec3`
records, in push order. -/
@[refines ConRon.Arena.classFeR]
theorem classFeR_refines (p : Prog) (hp : CfrProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (pp cgo cgl rco rcl : Word) (P : BlockShape)
    (cvGs : List IConstantVal) (recCls : List Nat) (hS : StageR dn vis fe s₀.mem a₀)
    (hP : DecB (fun m => decBS m pp.toNat) s₀.mem P) (hcg : SPL decCVX s₀.mem cgo.toNat cgl.toNat cvGs)
    (hrc : DecB (fun m => decNL m rco.toNat rcl.toNat) s₀.mem recCls) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fe_r" [pp, cgo, cgl, rco, rcl, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn (r.headD 0) (ConRon.Arena.classFeR P cvGs recCls fe).1 s'.mem a₀ ∧
      IWGrow s₀.mem s'.mem ∧
      SPL (decPrev dn) s'.mem (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat
        (ConRon.Arena.classFeR P cvGs recCls fe).2; ⊤⦄ := by
  refine triple_post (classFeR_spec p hp n s₀ pp cgo cgl rco rcl vis) ?_
  rintro r s' ⟨hl, hm⟩
  cases n with
  | zero => simp [ferAW] at hm
  | succ n =>
  rw [ferAW.arm1] at hm
  obtain ⟨⟨r1, m1⟩, h1, hm⟩ := of_K hm rfl
  rw [ferAW.k_class_fe_r_go.arm1] at hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
  have hP' : decBS (truncM s₀.mem) pp.toNat = some P := hP
  simp only [decBS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hP'
  obtain ⟨_m1, _hm1, rs, hrs, _x2, _h2, _x3, _h3, _x4, _h4, _x5, _h5, _x6, _h6, hPe⟩ := hP'
  obtain ⟨ro, rl, hro, hrl, hrecs⟩ := decAt_some hrs
  have hrsP : rs = P.recs := by rw [← hPe]
  rw [hrsP] at hrecs
  have hsz := hS.2.2.2.1
  obtain ⟨e2, t2⟩ := rec2RdN (w := pp) (k := 2) (rec2IwN_trunc hro).2 hsz
  obtain ⟨e3, t3⟩ := rec2RdN (w := pp) (k := 3) (by simpa using (rec2IwN_trunc hrl).2) hsz
  simp only [show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl] at e2 e3
  rw [e2, e3] at h1
  obtain ⟨hS1, hg1, hsp1⟩ := ferW_ok p hp dn P _ _ n _ _ a₀ vis fe cgo cgl rcl 0 cvGs recCls r1 h1 hS
    (by rw [t2, t3]; exact hrecs) hcg (decNL_length _ (hrc.get (OMono.decNL _ _))) (by simp; exact cgl.toNat_lt)
  exact ⟨hl, by simpa [ConRon.Arena.classFeR] using hS1, hg1, by simpa [ConRon.Arena.classFeR] using hsp1⟩

end L.Ind

end

end
