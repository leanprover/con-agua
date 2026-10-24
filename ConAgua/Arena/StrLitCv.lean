import ConAgua.Arena.StrLitBase

/-!
# `str_cv`: `IConstantInfo.toConstantVal` under `CoreS` (helper `defeq2-str`)

`str_cv(q)` answers `(lo, ll, ty)`: a record of kind `≤ 5` holds its constant value at `q + 1`
(`decCV`), a projection table (kind `6`) its level parameters at `q + 3`, `q + 4` (`decTbl`) and
the type `Sort 1`, interned as the twin interns it (`intern_zero`, `intern_succ`, `intern_sort`,
which leave `EREC` alone). `cv_call`: the twin's run, the relation after it, and the words.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace L.Arena

theorem strNatD {a : Array Word} {i n : Nat} (h : nat? a i = some n) : ∃ w, a[i]? = some w ∧ n = w.toNat := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h; exact ⟨w, hw, rfl⟩

theorem strRdW {a : Array Word} {q w : Word} (h : a[q.toNat]? = some w) : rdW a q = w := by simp [rdW, h]

theorem strErecRd {m : Mem} {j : Nat} {w : Word} (h : (erecP m)[j]? = some w) :
    (m.arr64 EREC)[j]? = some w := erecP_ext m _ _ h

/-- The kinds of a decoded record (lane `decls3`'s `ciD`, `DeclCanonEq.lean`, which this file does
not import: it pulls in the declaration arms). -/
theorem strCiD {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat} {x : IConstantInfo}
    (h : decCI a dn p = some x) :
    ∃ wk, a[p]? = some wk ∧
      ((wk.toNat = 0 ∧ ∃ cv, decCV a (p + 1) = some cv ∧ x = .axiomInfo cv) ∨
       (wk.toNat = 1 ∧ ∃ cv v hi, decCV a (p + 1) = some cv ∧ hd? a (p + 5) = some v ∧
          decHint a (p + 6) = some hi ∧ x = .defnInfo cv v hi) ∨
       (wk.toNat = 2 ∧ ∃ cv, decCV a (p + 1) = some cv ∧ x = .thmInfo cv) ∨
       (wk.toNat = 3 ∧ ∃ cv caps, decCV a (p + 1) = some cv ∧ decCaps a dn (p + 5) = some caps ∧
          x = .indInfo cv caps) ∨
       (wk.toNat = 4 ∧ ∃ cv np nf, decCV a (p + 1) = some cv ∧ nat? a (p + 5) = some np ∧
          nat? a (p + 6) = some nf ∧ x = .ctorInfo cv np nf) ∨
       (wk.toNat = 5 ∧ ∃ cv mi rp o c rules, decCV a (p + 1) = some cv ∧ nat? a (p + 5) = some mi ∧
          nat? a (p + 6) = some rp ∧ nat? a (p + 7) = some o ∧ nat? a (p + 8) = some c ∧
          decRules a o c = some rules ∧ x = .recInfo cv mi rp rules) ∨
       (wk.toNat = 6 ∧ ∃ tbl, decTbl a p = some tbl ∧ x = .projInfo tbl)) := by
  unfold decCI at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨k, hk, h⟩ := h
  obtain ⟨wk, e, rfl⟩ := strNatD hk
  refine ⟨wk, e, ?_⟩
  split at h
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    exact .inl ⟨hh, cv, hcv, rfl⟩
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, v, hv, hi, hhi, rfl⟩ := h
    exact .inr (.inl ⟨hh, cv, v, hi, hcv, hv, hhi, rfl⟩)
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    exact .inr (.inr (.inl ⟨hh, cv, hcv, rfl⟩))
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, caps, hc, rfl⟩ := h
    exact .inr (.inr (.inr (.inl ⟨hh, cv, caps, hcv, hc, rfl⟩)))
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, np, hnp, nf, hnf, rfl⟩ := h
    exact .inr (.inr (.inr (.inr (.inl ⟨hh, cv, np, nf, hcv, hnp, hnf, rfl⟩))))
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, mi, hmi, rp, hrp, o, ho, c, hc, rules, hr, rfl⟩ := h
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨hh, cv, mi, rp, o, c, rules, hcv, hmi, hrp, ho, hc, hr, rfl⟩)))))
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tbl, ht, rfl⟩ := h
    exact .inr (.inr (.inr (.inr (.inr (.inr ⟨hh, tbl, ht, rfl⟩)))))
  · simp at h

/-- The model of `str_cv`. -/
def strCvW (p : Prog) (n : Nat) (m : Mem) (q : Word) : Option (List Word × Mem) :=
  if rdW (m.arr64 EREC) q ≤ 5 then
    some ([rdW (m.arr64 EREC) (q + 2), rdW (m.arr64 EREC) (q + 3), rdW (m.arr64 EREC) (q + 4)], m)
  else if rdW (m.arr64 EREC) q ≠ 6 then none
  else match callW p n "intern_zero" [] m with
    | none => none
    | some (z, m₁) =>
      match callW p n "intern_succ" [z.headD 0] m₁ with
      | none => none
      | some (o, m₂) =>
        match callW p n "intern_sort" [o.headD 0] m₂ with
        | none => none
        | some (t, m₃) =>
          some ([rdW (m₃.arr64 EREC) (q + 3), rdW (m₃.arr64 EREC) (q + 4), t.headD 0], m₃)

theorem strCv_spec (p : Prog) (hp : p.lookup "str_cv" = some strCvL) (n : Nat) (s₀ : St)
    (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "str_cv" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ strCvW p n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, strCvL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "intern_zero", callW_spec p n "intern_succ", callW_spec p n "intern_sort"] <;>
    finish [strCvW]

/-- A projection table's level parameters, read at `q + 3`, `q + 4`. -/
theorem decTbl_lps {a b : Array Word} {q : Word} {tbl : IProjTable} (hab : ArrExt a b)
    (hsz : b.size < 2 ^ 63) (h : decTbl a q.toNat = some tbl) :
    hslice? b (rdW b (q + 3)).toNat (rdW b (q + 4)).toNat = some tbl.levelParams ∧
    tbl.levelParams.length = (rdW b (q + 4)).toNat := by
  simp only [decTbl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨_, _, _, _, lps, hl, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc⟩ := h
  cases hc
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hl
  obtain ⟨o, ho, c, hc', hs⟩ := hl
  obtain ⟨w3, hw3, rfl⟩ := strNatD ho
  obtain ⟨w4, hw4, rfl⟩ := strNatD hc'
  have e3 : rdW b (q + 3) = w3 := rdW_off (hab _ _ hw3) (by simp <;> omega) hsz
  have e4 : rdW b (q + 4) = w4 := rdW_off (hab _ _ hw4) (by simp <;> omega) hsz
  rw [e3, e4]
  exact ⟨hab.hslice? hs, hslice?_length hs⟩

section calls
variable (p : Prog) (hp : StrLitProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem}
  {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
include hp

theorem zero_erec (h : callW p n "intern_zero" [] m = some (r, m')) :
    m'.arr64 EREC = m.arr64 EREC := by
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internZero_spec p hp.zeroFind hp.zeroPush hp.internZero n _) h
  rw [hs'] at hI
  exact (consInternM_frame zeroCS_wf hI).1 EREC (by simp [ConsSch.wset, zeroCS, zeroSch, EREC, ZREC, ZSLOT]) (by decide)

theorem succ_erec {u : Word} (h : callW p n "intern_succ" [u] m = some (r, m')) :
    m'.arr64 EREC = m.arr64 EREC := by
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internSucc_spec p hp.succFind hp.succPush hp.internSucc n _ u) h
  rw [hs'] at hI
  exact (sinternW_frame (hI := hI)).1 EREC (by simp [succSch, EREC, SREC, SSLOT, SHP]) (by decide)

theorem sort_erec {u : Word} (h : callW p n "intern_sort" [u] m = some (r, m')) :
    m'.arr64 EREC = m.arr64 EREC := by
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internSort_spec p hp.sortFind hp.sortPush hp.internSort n _ u) h
  rw [hs'] at hI
  exact (sointernW_frame (hI := hI)).1 EREC (by simp [sortSch, EREC, SOREC, SOSLOT, SOLP]) (by decide)

/-- **`str_cv` under `CoreS`**: the twin's `toConstantVal` at the decoded record, the relation
after it, the record pool unchanged, and the words of the constant value. -/
theorem cv_call (hS : CoreS dn m a vis fe M eb) {q : Word} {ci : IConstantInfo}
    (hci : decCI (erecP m) dn q.toNat = some ci)
    (h : callW p n "str_cv" [q] m = some (r, m')) :
    ∃ cv a', ci.toConstantVal.run a = .ok (cv, a') ∧ CoreAfter dn m m' a' vis fe M eb ∧
      m'.arr64 EREC = m.arr64 EREC ∧
      hslice? (m.arr64 EREC) (r.headD 0).toNat (r.tail.headD 0).toNat = some cv.levelParams ∧
      cv.levelParams.length = (r.tail.headD 0).toNat ∧
      cv.type = decI (r.tail.tail.headD 0) ∧ HW (r.tail.tail.headD 0) := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (strCv_spec p hp.strCv n _ q) h
  obtain ⟨wk, e, hk⟩ := strCiD hci
  have hrd : rdW (m.arr64 EREC) q = wk := strRdW (strErecRd e)
  have hsmall : ∀ cv, decCV (erecP m) (q.toNat + 1) = some cv → ci.toConstantVal = pure cv →
      rdW (m.arr64 EREC) q ≤ 5 → ∃ cv a', ci.toConstantVal.run a = .ok (cv, a') ∧
        CoreAfter dn m s'.mem a' vis fe M eb ∧ s'.mem.arr64 EREC = m.arr64 EREC ∧
        hslice? (m.arr64 EREC) (r.headD 0).toNat (r.tail.headD 0).toNat = some cv.levelParams ∧
        cv.levelParams.length = (r.tail.headD 0).toNat ∧
        cv.type = decI (r.tail.tail.headD 0) ∧ HW (r.tail.tail.headD 0) := by
    intro cv hcv hpure h5
    simp only [strCvW, h5, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, hm⟩ := hW
    rw [← hm]
    obtain ⟨hsl, hlen, hty, hhw⟩ := decCV_rd (erecP_ext m) hS.erec hcv
    exact ⟨cv, a, by rw [hpure]; rfl, ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, rfl, hsl, hlen,
      hty, hhw⟩
  have h5 : ∀ k : Nat, wk.toNat = k → k ≤ 5 → rdW (m.arr64 EREC) q ≤ 5 := by
    intro k hk hk5; rw [hrd, UInt64.le_iff_toNat_le, hk]; simp; omega
  rcases hk with ⟨k0, cv, hcv, rfl⟩ | ⟨k0, cv, v, hi, hcv, -, -, rfl⟩ | ⟨k0, cv, hcv, rfl⟩ |
      ⟨k0, cv, caps, hcv, -, rfl⟩ | ⟨k0, cv, np, nf, hcv, -, -, rfl⟩ |
      ⟨k0, cv, mi, rp, o, c, rules, hcv, -, -, -, -, -, rfl⟩ | ⟨k6, tbl, ht, rfl⟩
  · exact hsmall cv hcv rfl (h5 0 k0 (by decide))
  · exact hsmall cv hcv rfl (h5 1 k0 (by decide))
  · exact hsmall cv hcv rfl (h5 2 k0 (by decide))
  · exact hsmall cv hcv rfl (h5 3 k0 (by decide))
  · exact hsmall cv hcv rfl (h5 4 k0 (by decide))
  · exact hsmall cv hcv rfl (h5 5 k0 (by decide))
  -- a projection table
  have hn5 : ¬ rdW (m.arr64 EREC) q ≤ 5 := by
    rw [hrd, UInt64.le_iff_toNat_le, k6]; simp
  have h6 : rdW (m.arr64 EREC) q = 6 := by rw [hrd]; exact UInt64.toNat_inj.mp (by rw [k6]; rfl)
  obtain ⟨hsl, hlen⟩ := decTbl_lps (erecP_ext m) hS.erec ht
  simp only [strCvW, hn5, h6, ↓reduceIte, ne_eq, not_true_eq_false] at hW
  cases h1 : callW p n "intern_zero" [] m with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨z, m₁⟩ := q₁
  rw [h1] at hW; dsimp only at hW
  cases h2 : callW p n "intern_succ" [z.headD 0] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨o, m₂⟩ := q₂
  rw [h2] at hW; dsimp only at hW
  cases h3 : callW p n "intern_sort" [o.headD 0] m₂ with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨t, m₃⟩ := q₃
  rw [h3] at hW
  rw [if_neg (show ¬ ((6 : Word) ≤ 5) by decide)] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  subst hr
  rw [← hm]
  have e₃ : m₃.arr64 EREC = m.arr64 EREC :=
    ((sort_erec p hp h3).trans (succ_erec p hp h2)).trans (zero_erec p hp h1)
  have R₁ := zero_call p hp hS h1
  obtain ⟨M₁, hS₁, hK₁, hT₁⟩ := R₁.2.1
  have hd₁ : ∃ l, denoteL (AM.st (internLNode .zero) a).store.ls (decI (z.headD 0)) = some l := by
    have hd := internLNode_res_den (v := .zero) hS (fun c hc => by simp [LNodeView.lchildren] at hc)
      (fun n hn => by simp [LNodeView.nchildren] at hn) R₁.1
    rw [R₁.2.2.1] at hd; exact hd
  have R₂ := succ_call p hp hS₁ R₁.2.2.2 h2 hd₁
  obtain ⟨M₂, hS₂, hK₂, hT₂⟩ := R₂.2.1
  have hd₂ : ∃ l, denoteL (AM.st (internLNode (.succ (decI (z.headD 0))))
      (AM.st (internLNode .zero) a)).store.ls (decI (o.headD 0)) = some l := by
    have hd := internLNode_res_den (v := .succ (decI (z.headD 0))) hS₁
      (fun c hc => by
        simp only [LNodeView.lchildren, List.mem_cons, List.mem_nil_iff, or_false] at hc
        subst hc; exact hd₁)
      (fun n hn => by simp [LNodeView.nchildren] at hn) R₂.1
    rw [R₂.2.2.1] at hd; exact hd
  have R₃ := sort_call p hp hS₂ R₂.2.2.2 h3 hd₂
  have hrun : (IConstantInfo.projInfo tbl).toConstantVal.run a =
      .ok (⟨tbl.tableName, tbl.levelParams, decH t⟩,
        AM.st (internE (.sort (decI (o.headD 0))))
          (AM.st (internLNode (.succ (decI (z.headD 0)))) (AM.st (internLNode .zero) a))) := by
    have r1 := AM.run_of_ok _ _ R₁.1
    have r2 := AM.run_of_ok _ _ R₂.1
    have r3 := AM.run_of_ok _ _ R₃.1
    rw [R₁.2.2.1] at r1
    rw [R₂.2.2.1] at r2
    rw [R₃.2.2.1] at r3
    simp only [decLv] at r1 r2
    simp only [IConstantInfo.toConstantVal, StateT.run_bind, r1, except_ok_bind, r2, r3]
    rfl
  refine ⟨_, _, hrun, ?_, by rw [e₃], ?_, ?_, rfl, R₃.2.2.2⟩
  · exact CoreAfter.comp hK₁ hT₁ (CoreAfter.comp hK₂ hT₂ R₃.2.1)
  · simp only [List.headD_cons, List.tail_cons, e₃]; exact hsl
  · simp only [List.headD_cons, List.tail_cons, e₃]; exact hlen

end calls

end L.Arena
