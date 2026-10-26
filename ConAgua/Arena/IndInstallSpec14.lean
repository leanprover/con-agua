import ConAgua.Arena.IndInstallSpec13

/-!
# Refinements of `IndInstall`, part 14 (lane `indproofs2`, helper `install`): `consBlockInds`

`ind_info_rec` (the `.indInfo` record: the constant's four words, the capability record's 15, all
read before the allocation and written at once, `wrER`), `env_push` (lane `decls2`'s), by recursion
as the twin's.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `ind_info_rec` -/

/-- The record's words, read in the memory before the allocation. -/
def iirWs (m : Mem) (cv caps : Word) : List Word :=
  [3, rdW (m.arr64 EREC) cv, rdW (m.arr64 EREC) (cv + 1), rdW (m.arr64 EREC) (cv + 2), rdW (m.arr64 EREC) (cv + 3), rdW (m.arr64 IW) caps, rdW (m.arr64 IW) (caps + 1), rdW (m.arr64 IW) (caps + 2), rdW (m.arr64 IW) (caps + 3), rdW (m.arr64 IW) (caps + 4), rdW (m.arr64 IW) (caps + 5), rdW (m.arr64 IW) (caps + 6), rdW (m.arr64 IW) (caps + 7), rdW (m.arr64 IW) (caps + 8), rdW (m.arr64 IW) (caps + 9), rdW (m.arr64 IW) (caps + 10), rdW (m.arr64 IW) (caps + 11), rdW (m.arr64 IW) (caps + 12), rdW (m.arr64 IW) (caps + 13), rdW (m.arr64 IW) (caps + 14)]

theorem erPut5_spec (p : Prog) (hp : p.lookup "er_put5" = some erPut5) (n : Nat) (s₀ : St)
    (d x0 x1 x2 x3 x4 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "er_put5" [d, x0, x1, x2, x3, x4]
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = wrER s₀.mem d [x0, x1, x2, x3, x4]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, erPut5]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
    finish [wrER, UInt64.add_assoc]

theorem wrER_append : ∀ (xs ys : List Word) (m : Mem) (q : Word),
    wrER m q (xs ++ ys) = wrER (wrER m q xs) (q + UInt64.ofNat xs.length) ys
  | [], ys, m, q => by simp [wrER]
  | x :: xs, ys, m, q => by
    simp only [List.cons_append, wrER]
    rw [wrER_append xs ys]
    congr 1
    simp only [List.length_cons]
    rw [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm (UInt64.ofNat xs.length)]; rfl

/-- The model of `ind_info_rec(cv, caps)`. -/
def iirW (m : Mem) (cv caps : Word) : Option (Word × Mem) :=
  match erAllocW m 20 with
  | none => none
  | some (q, m1) => some (q, wrER m1 q (iirWs m cv caps))

/-- The four writes, one continuation each. -/
def iirK5 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m5) => some ([q], m5)
def iirK4 (p : Prog) (n : Nat) (caps q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m4) => iirK5 q (callW p n "er_put5" [q + 15, rdW (m4.arr64 IW) (caps + 10),
      rdW (m4.arr64 IW) (caps + 11), rdW (m4.arr64 IW) (caps + 12), rdW (m4.arr64 IW) (caps + 13),
      rdW (m4.arr64 IW) (caps + 14)] m4)
def iirK3 (p : Prog) (n : Nat) (caps q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m3) => iirK4 p n caps q (callW p n "er_put5" [q + 10, rdW (m3.arr64 IW) (caps + 5),
      rdW (m3.arr64 IW) (caps + 6), rdW (m3.arr64 IW) (caps + 7), rdW (m3.arr64 IW) (caps + 8),
      rdW (m3.arr64 IW) (caps + 9)] m3)
def iirK2 (p : Prog) (n : Nat) (caps q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) => iirK3 p n caps q (callW p n "er_put5" [q + 5, rdW (m2.arr64 IW) caps,
      rdW (m2.arr64 IW) (caps + 1), rdW (m2.arr64 IW) (caps + 2), rdW (m2.arr64 IW) (caps + 3),
      rdW (m2.arr64 IW) (caps + 4)] m2)
/-- After the allocation: the four writes. -/
def iirK (p : Prog) (n : Nat) (cv caps : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m1) => iirK2 p n caps q (callW p n "er_put5" [q, 3, rdW (m1.arr64 EREC) cv,
      rdW (m1.arr64 EREC) (cv + 1), rdW (m1.arr64 EREC) (cv + 2), rdW (m1.arr64 EREC) (cv + 3)] m1)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (cv caps q : Word) (r : List Word)
theorem iirK5_some : iirK5 q (some (r, m)) = some ([q], m) := rfl
theorem iirK4_some : iirK4 p n caps q (some (r, m)) = iirK5 q (callW p n "er_put5" [q + 15,
    rdW (m.arr64 IW) (caps + 10), rdW (m.arr64 IW) (caps + 11), rdW (m.arr64 IW) (caps + 12),
    rdW (m.arr64 IW) (caps + 13), rdW (m.arr64 IW) (caps + 14)] m) := rfl
theorem iirK3_some : iirK3 p n caps q (some (r, m)) = iirK4 p n caps q (callW p n "er_put5" [q + 10,
    rdW (m.arr64 IW) (caps + 5), rdW (m.arr64 IW) (caps + 6), rdW (m.arr64 IW) (caps + 7),
    rdW (m.arr64 IW) (caps + 8), rdW (m.arr64 IW) (caps + 9)] m) := rfl
theorem iirK2_some : iirK2 p n caps q (some (r, m)) = iirK3 p n caps q (callW p n "er_put5" [q + 5,
    rdW (m.arr64 IW) caps, rdW (m.arr64 IW) (caps + 1), rdW (m.arr64 IW) (caps + 2),
    rdW (m.arr64 IW) (caps + 3), rdW (m.arr64 IW) (caps + 4)] m) := rfl
theorem iirK_some : iirK p n cv caps (some (q, m)) = iirK2 p n caps q (callW p n "er_put5" [q, 3,
    rdW (m.arr64 EREC) cv, rdW (m.arr64 EREC) (cv + 1), rdW (m.arr64 EREC) (cv + 2),
    rdW (m.arr64 EREC) (cv + 3)] m) := rfl
end arms
attribute [ind_grind] iirK5_some iirK4_some iirK3_some iirK2_some iirK_some

theorem iir_specK (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hp : p.lookup "ind_info_rec" = some indInfoRec) (n : Nat) (s₀ : St) (cv caps : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ind_info_rec" [cv, caps]
    ⦃fun r s' => LocEq s' s₀ ∧ iirK p n cv caps (erAllocW s₀.mem 20) = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, indInfoRec]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      erecAlloc_specW p ha n, callW_spec p n "er_put5"] <;>
    finish (gen := 40) (instances := 20000) [rdW_eq]

theorem wrER_IW (m : Mem) (q : Word) (ws : List Word) : (wrER m q ws).arr64 IW = m.arr64 IW :=
  (wrER_frame ws m q).1 IW (by simp [EREC, IW]) (by decide)

theorem erAllocW_arr {m m1 : Mem} {k q : Word} (h : erAllocW m k = some (q, m1)) :
    m1.arr64 IW = m.arr64 IW ∧ m1.arr64 EREC = m.arr64 EREC := by
  simp only [erAllocW] at h; split at h; · cases h
  split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  simp only [erAllocMem]
  exact ⟨Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)⟩

/-- `ind_info_rec`'s four writes are the record written at once. -/
theorem iirK_eq {p : Prog} (hp : p.lookup "er_put5" = some erPut5) {n : Nat} {m m' : Mem}
    {cv caps : Word} {r : List Word} (h : iirK p (n + 1) cv caps (erAllocW m 20) = some (r, m')) :
    ∃ q, r = [q] ∧ iirW m cv caps = some (q, m') := by
  have put : ∀ (mm : Mem) (d x0 x1 x2 x3 x4 : Word) (rr : List Word) (mm' : Mem),
      callW p (n + 1) "er_put5" [d, x0, x1, x2, x3, x4] mm = some (rr, mm') →
      mm' = wrER mm d [x0, x1, x2, x3, x4] := by
    intro mm d x0 x1 x2 x3 x4 rr mm' hc
    obtain ⟨s', rfl, -, h2⟩ := triple_of_callW (s₀ := ⟨mm, Locals.init []⟩)
      (erPut5_spec p hp n _ d x0 x1 x2 x3 x4) hc
    exact h2
  unfold iirW
  rcases h1 : erAllocW m 20 with _ | ⟨q, m1⟩
  · rw [h1] at h; cases h
  obtain ⟨hI1, hE1⟩ := erAllocW_arr h1
  rw [h1, iirK_some] at h
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl; rw [iirK2_some] at h
  have e2 := put _ _ _ _ _ _ _ _ _ h2
  have i2 : m2.arr64 IW = m.arr64 IW := by rw [e2, wrER_IW, hI1]
  rw [i2] at h
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h rfl; rw [iirK3_some] at h
  have e3 := put _ _ _ _ _ _ _ _ _ h3
  have i3 : m3.arr64 IW = m.arr64 IW := by rw [e3, wrER_IW, i2]
  rw [i3] at h
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h rfl; rw [iirK4_some] at h
  have e4 := put _ _ _ _ _ _ _ _ _ h4
  have i4 : m4.arr64 IW = m.arr64 IW := by rw [e4, wrER_IW, i3]
  rw [i4] at h
  obtain ⟨⟨r5, m5⟩, h5, h⟩ := of_K h rfl; rw [iirK5_some] at h
  have e5 := put _ _ _ _ _ _ _ _ _ h5
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  refine ⟨q, rfl, ?_⟩
  rw [hE1] at e2
  subst e2 e3 e4 e5
  have hw : iirWs m cv caps = [3, rdW (m.arr64 EREC) cv, rdW (m.arr64 EREC) (cv + 1),
      rdW (m.arr64 EREC) (cv + 2), rdW (m.arr64 EREC) (cv + 3)] ++
      ([rdW (m.arr64 IW) caps, rdW (m.arr64 IW) (caps + 1), rdW (m.arr64 IW) (caps + 2),
        rdW (m.arr64 IW) (caps + 3), rdW (m.arr64 IW) (caps + 4)] ++
      ([rdW (m.arr64 IW) (caps + 5), rdW (m.arr64 IW) (caps + 6), rdW (m.arr64 IW) (caps + 7),
        rdW (m.arr64 IW) (caps + 8), rdW (m.arr64 IW) (caps + 9)] ++
       [rdW (m.arr64 IW) (caps + 10), rdW (m.arr64 IW) (caps + 11), rdW (m.arr64 IW) (caps + 12),
        rdW (m.arr64 IW) (caps + 13), rdW (m.arr64 IW) (caps + 14)])) := rfl
  dsimp only
  rw [hw, wrER_append, wrER_append, wrER_append]
  simp only [List.length_cons, List.length_nil]
  rw [show q + UInt64.ofNat 5 + UInt64.ofNat 5 = q + 10 by rw [UInt64.add_assoc]; rfl,
    show q + UInt64.ofNat 5 = q + 5 from rfl,
    show q + 10 + UInt64.ofNat 5 = q + 15 by rw [UInt64.add_assoc]; rfl]

/-- **`ind_info_rec` under the stage relation**: a fresh `.indInfo` record of the constant at `cv`
(decoded below the tops) and the capability record at `caps`; its name word a handle. -/
theorem iirW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cv caps q : Word} {cvv : IConstantVal} {c : IIndCaps}
    (h : iirW m cv caps = some (q, m')) (hS : StageR dn vis fe m a)
    (hcv : DecB (fun m => decCVp m cv.toNat) m cvv) (hcp : CapsAt dn m caps.toNat c) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') dn q.toNat = some (.indInfo cvv c) ∧ H (rdW (m'.arr64 EREC) (q + 1)) := by
  unfold iirW at h
  rcases h1 : erAllocW m 20 with _ | ⟨q1, m1⟩
  · rw [h1] at h; cases h
  rw [h1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS', hg, hq, htop, hget⟩ := erRec_stage h1 hS (iirWs m cv caps) (by simp [iirWs])
  have hlen : (iirWs m cv caps).length = 20 := by simp [iirWs]
  rw [hlen] at htop hget
  generalize hM : wrER m1 q1 (iirWs m cv caps) = M at hS' hg htop hget
  obtain ⟨-, hEtop, -, hEsz, -⟩ := hS.2
  obtain ⟨-, hEtop', -, hEsz', -⟩ := hS'.2
  have hP : ∀ j, j < 20 → (erecP M)[q1.toNat + j]? = (iirWs m cv caps)[j]? := fun j hj => by
    rw [erecP_getE (by omega)]; exact hget j hj
  -- the constant's words
  have hcvE : decCV (erecP m) cv.toNat = some cvv := decCVp_truncM hcv
  have h3 : (erecP m)[cv.toNat + 3]? ≠ none := by
    have := decCV_type hcvE; intro e; simp [hd?, e] at this
  have hcq : cv.toNat + 4 ≤ erTop m := by
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h3; have := erecP_lt hv; omega
  have c1 : (cv + 1).toNat = cv.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have c2 : (cv + 2).toNat = cv.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have c3 : (cv + 3).toNat = cv.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have hw : ∀ i, i < 4 → (erecP M)[q1.toNat + 1 + i]? = (erecP M)[cv.toNat + i]? := by
    intro i hi
    rw [show q1.toNat + 1 + i = q1.toNat + (i + 1) by omega, hP (i + 1) (by omega),
      erecP_getE (by omega), hg.2.2.2 _ (by omega)]
    have hlt : cv.toNat + i < (m.arr64 EREC).size := by simp only [erTop] at hEtop hcq; omega
    rcases i with _ | _ | _ | _ | i
    all_goals first
      | omega
      | (simp only [Nat.add_zero, Nat.zero_add] at hlt ⊢
         simp only [iirWs, List.getElem?_cons_succ, List.getElem?_cons_zero, rdW, c1, c2, c3,
          Array.getElem?_eq_getElem hlt, Option.getD_some])
  have hcv' : decCV (erecP M) (q1.toNat + 1) = some cvv := by
    rw [decCV_shift (by simpa using hw 0 (by decide)) (by simpa using hw 1 (by decide))
      (by simpa [Nat.add_assoc] using hw 2 (by decide)) (by simpa [Nat.add_assoc] using hw 3 (by decide))]
    exact ArrExt.decCV (IWGrow.erecPExtR hg) hcvE
  -- the capability record's words
  have hc15 := hcp.1
  have hIsz : iwTop m ≤ (m.arr64 IW).size := hS.2.1
  have hcaps : decCaps (erecP M) dn (q1.toNat + 5) = some c := by
    refine hcp.2 (erecP M) (q1.toNat + 5) (fun i hi => ?_) (fun i hi => ?_)
    · rw [show q1.toNat + 5 + i = q1.toNat + (5 + i) by omega, hP (5 + i) (by omega)]
      have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
      have gen : ∀ w : Word, w.toNat = caps.toNat + i →
          (iirWs m cv caps)[5 + i]? = some (rdW (m.arr64 IW) w) →
          (iirWs m cv caps)[5 + i]? = (iwA m)[caps.toNat + i]? := fun w hw h => by
        rw [h, ← hw]; simp only [iwA, rdW]; rw [Array.getElem?_eq_getElem (by omega)]; simp
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
      all_goals first
        | omega
        | exact gen _ rfl rfl
        | exact gen _ (by rw [UInt64.toNat_add]; simp; omega) rfl
    · rw [erecP_getE (by omega)]; simp only [erA]; exact hg.2.2.2 i hi
  have n0 : nat? (erecP M) q1.toNat = some 3 := by
    have := hP 0 (by decide); simp only [Nat.add_zero] at this
    simp [nat?, this, iirWs]
  refine ⟨hS', hg, ?_, ?_⟩
  · simp only [decCI, Option.bind_eq_bind, n0, Option.bind_some, hcv', hcaps, Option.pure_def]
  · have hq1 : (q1 + 1).toNat = q1.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have := hget 1 (by decide)
    rw [rdW_of_get? hq1.symm this]
    have := (partsCVName (IWGrow.refl m) hcv cv.toNat_lt).1
    simpa [iirWs] using this

/-! ## `cons_block_inds` -/

/-- After the rest. -/
def icbiK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

mutual
/-- **The model of `cons_block_inds(p1, is_rec, o, l, vis, i)`** at exec fuel `n`. -/
def icbiW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, p1, isRec, o, l, vis, i =>
    if l = 0 then some ([vis], m)
    else icbiK1 p n p1 isRec o l vis i (callW p n "block_caps_at" [p1, i, isRec] m)
/-- After the capability record: the `.indInfo` record. -/
def icbiK1 (p : Prog) (n : Nat) (p1 isRec o l vis i : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbiK2 p n p1 isRec o l vis i
      (callW p n "ind_info_rec" [rdW (m.arr64 IW) o, r.headD 0] m)
/-- After the record: the push. -/
def icbiK2 (p : Prog) (n : Nat) (p1 isRec o l vis i : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbiK3 p n p1 isRec o l i (callW p n "env_push" [vis, r.headD 0] m)
/-- After the push: the rest. -/
def icbiK3 (p : Prog) (n : Nat) (p1 isRec o l i : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbiK4 (icbiW p n m p1 isRec (o + 1) (l - 1) (r.headD 0) (i + 1))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (p1 isRec o l vis i : Word) (r : List Word)
theorem icbiW_zero : icbiW p 0 m p1 isRec o l vis i = none := by simp [icbiW]
theorem icbiW_nil (h : l = 0) : icbiW p (n + 1) m p1 isRec o l vis i = some ([vis], m) := by
  simp [icbiW, h]
theorem icbiW_cons (h : l ≠ 0) : icbiW p (n + 1) m p1 isRec o l vis i =
    icbiK1 p n p1 isRec o l vis i (callW p n "block_caps_at" [p1, i, isRec] m) := by simp [icbiW, h]
theorem icbiK1_some : icbiK1 p n p1 isRec o l vis i (some (r, m)) = icbiK2 p n p1 isRec o l vis i
    (callW p n "ind_info_rec" [rdW (m.arr64 IW) o, r.headD 0] m) := by simp [icbiK1]
theorem icbiK2_some : icbiK2 p n p1 isRec o l vis i (some (r, m)) =
    icbiK3 p n p1 isRec o l i (callW p n "env_push" [vis, r.headD 0] m) := by simp [icbiK2]
theorem icbiK3_some : icbiK3 p n p1 isRec o l i (some (r, m)) =
    icbiK4 (icbiW p n m p1 isRec (o + 1) (l - 1) (r.headD 0) (i + 1)) := by simp [icbiK3]
theorem icbiK4_some : icbiK4 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms
attribute [ind_grind] icbiW_nil icbiW_cons icbiK1_some icbiK2_some icbiK3_some icbiK4_some

theorem icbi_spec (p : Prog) (hp : p.lookup "cons_block_inds" = some consBlockInds) (n : Nat) :
    ∀ (s₀ : St) (p1 isRec o l vis i : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "cons_block_inds" [p1, isRec, o, l, vis, i]
    ⦃fun r s' => LocEq s' s₀ ∧ icbiW p n s₀.mem p1 isRec o l vis i = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ p1 isRec o l vis i; rw [invoke_eq _ hp]; simp only [callFn, consBlockInds]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ p1 isRec o l vis i
    rw [invoke_eq _ hp]
    simp only [callFn, consBlockInds]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "block_caps_at", callW_spec p n "ind_info_rec", callW_spec p n "env_push", ih] <;>
      finish (gen := 20) [rdW_eq]

/-- The lookups of `cons_block_inds`. -/
structure ConsIndsProg (p : Prog) : Prop extends CapsProg p where
  recP : RecProg p
  iir : p.lookup "ind_info_rec" = some indInfoRec
  put5 : p.lookup "er_put5" = some erPut5
  cbi : p.lookup "cons_block_inds" = some consBlockInds

/-- `ind_info_rec`'s run, at any fuel. -/
theorem installIirRun {p : Prog} (hP : ConsIndsProg p) {n : Nat} {m m' : Mem} {cv caps : Word}
    {r : List Word} (h : callW p n "ind_info_rec" [cv, caps] m = some (r, m')) :
    ∃ q, r = [q] ∧ iirW m cv caps = some (q, m') := by
  rcases n with _ | k
  · rw [callW_zero] at h; cases h
  obtain ⟨s', rfl, -, hK⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iir_specK p hP.erAlloc hP.iir k _ cv caps) h
  rcases k with _ | j
  · exfalso
    cases h1 : erAllocW m 20 with
    | none => simp only [h1] at hK; cases hK
    | some x => obtain ⟨q, m1⟩ := x; simp only [h1, iirK_some, callW_zero] at hK; cases hK
  exact iirK_eq hP.put5 hK

/-- **`cons_block_inds`' model refines `consBlockInds`**, from a refinement `hLZ` of the
`lv_zero_caps` call of each member's `block_caps_at` at every state of the loop's invariant `T`
(`T` holds after it). -/
theorem icbiW_simG {p : Prog} (hP : ConsIndsProg p) (dn : NIdx → Option ConLeche.Name)
    (p1 isRec : Word) (bs : BlockShape) (b : Bool) (hb : (isRec != 0) = b) {T : AState → Prop}
    (hLZ : ∀ (k : Nat) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv), StageR dn vis fe m a → T a →
      DecB (fun m => decBS m p1.toNat) m bs → ShapeSrc m p1 →
      Sim (callW p k "lv_zero_caps" [rdW (m.arr64 IW) (p1 + 6)] m) (readLevelM bs.resSort) a
        (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decZC dn m' r x) ∧ T a'))
    (n : Nat) :
    ∀ (m : Mem) (a : AState) (vis : Word) (fe : IFEnv) (o l i : Word) (cvs : List IConstantVal),
    StageR dn vis fe m a → T a → DecB (fun m => decBS m p1.toNat) m bs → ShapeSrc m p1 →
    PSlR decCVp cvs o l m → i.toNat + l.toNat < 2 ^ 64 →
    Sim (icbiW p n m p1 isRec o l vis i) (ConRon.Arena.consBlockInds bs b cvs i.toNat fe) a
      (fun r x m' a' => (StageR dn (r.headD 0) x m' a' ∧ IWGrow m m') ∧ T a') := by
  induction n with
  | zero => intro m a vis fe o l i cvs _ _ _ _ _ _; rw [icbiW_zero]; exact Sim.of_none
  | succ n ih =>
  intro m a vis fe o l i cvs hS hT0 hq hsrc hcvs hil
  by_cases hl : l = 0
  · rw [icbiW_nil p n m p1 isRec o l vis i hl]
    have : cvs = [] := by
      have h := hcvs.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact Sim.ret ⟨⟨hS, IWGrow.refl m⟩, hT0⟩
  obtain ⟨q, cv, rest, rfl, hw, hqb, hdcv, hrest⟩ := partsPSl_cons hcvs hl
  rw [icbiW_cons p n m p1 isRec o l vis i hl]
  simp only [ConRon.Arena.consBlockInds]
  refine Sim.bindK (K := icbiK1 p n p1 isRec o l vis i) (body := fun r1 m1 => icbiK2 p n p1 isRec o l vis i
      (callW p n "ind_info_rec" [rdW (m1.arr64 IW) o, r1.headD 0] m1)) (by simp [icbiK1])
      (fun r m₁ => icbiK1_some p n m₁ p1 isRec o l vis i r)
    (blockCapsAt_simG hP.toCapsProg n hq hsrc hb (fun k => hLZ k m a vis fe hS hT0 hq hsrc)) ?_
  rintro r1 caps m1 a1 ⟨⟨hS1, hg1, hca⟩, hT1⟩
  refine Sim.mstep (K := icbiK2 p n p1 isRec o l vis i) (by simp [icbiK2])
    (fun r m₁ => icbiK2_some p n m₁ p1 isRec o l vis i r) fun r2 m2 h2 => ?_
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hlpos : 0 < l.toNat := Nat.pos_of_ne_zero fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  have hol : o.toNat < iwTop m := by have := hcvs.2; omega
  have hw1 : rdW (m1.arr64 IW) o = UInt64.ofNat q := by
    rw [← hw]; simp only [rdW]; rw [hg1.2.2.1 _ hol]
  rw [hw1] at h2
  obtain ⟨q2, rfl, hW2⟩ := installIirRun hP h2
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  obtain ⟨hS2, hg2, hci, hname⟩ := iirW_stage hW2 hS1 (by rw [hq']; exact hdcv.grow (OMono.decCVp _) hg1) hca
  refine Sim.mstep (K := icbiK3 p n p1 isRec o l i) (by simp [icbiK3])
    (fun r m₁ => icbiK3_some p n m₁ p1 isRec o l i r) fun r3 m3 h3 => ?_
  simp only [List.headD_cons] at h3
  obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (envPush_specW p hP.recP n _ vis q2 hname) h3
  obtain ⟨hS3, hg3⟩ := envPushW_ok hW3 hS2 hci
  have hg13 := (hg1.trans hg2).trans hg3
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hl1 : (l - 1).toNat = l.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  have hrec := ih s3.mem a1 (r3.headD 0) (fe.push (.indInfo cv caps)) (o + 1) (l - 1) (i + 1) rest hS3 hT1
    (hq.grow (decBS_mono _) hg13) (partsHsrc_grow hg13 hq9 hsrc)
    (hrest.grow (fun q => OMono.decCVp q) hg13) (by omega)
  rw [hi1] at hrec
  refine Sim.post (K := icbiK4) rfl (fun _ _ => rfl) hrec ?_
  rintro r x m' a' ⟨⟨hS', hg'⟩, hT'⟩
  exact ⟨⟨hS', hg13.trans hg'⟩, hT'⟩

end L.Ind
