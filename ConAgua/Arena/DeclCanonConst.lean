import ConAgua.Arena.DeclCanonNames

/-!
# Constants: `cv_lps`, the renaming context, `cv_canon_eq` (lane `decls3`, helper `decls3-canon`)
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem decRL_two {k : IdxKind} {m : Mem} {r : List Word} {xs : List (Idx k)}
    (h2 : r = [r.headD 0, r.tail.headD 0])
    (hd : decHL m (r.headD 0).toNat (r.tail.headD 0).toNat = some xs)
    (hb : (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m) :
    decRL (fun m => decHL m) 0 m r xs := by
  simpa only [decRL, getD0, getD1] using (⟨hd, hb⟩ : _ ∧ _)

theorem allocW_mem' {m m1 : Mem} {q k : Word} (h : allocW m k = some (q, m1)) :
    m1 = allocMem m k := by
  simp only [allocW] at h
  by_cases h1 : m.len64 IW < rdW (m.arr64 CTL) 200
  · simp [h1] at h
  by_cases h2 : m.len64 IW - rdW (m.arr64 CTL) 200 < k
  · simp [h1, h2] at h
  simp only [h1, h2, if_false, Option.some.injEq, Prod.mk.injEq] at h
  exact h.2.symm

theorem erCopyW_size (n : Nat) : ∀ (m m' : Mem) (d s l : Word), erCopyW n m d s l = some m' →
    ∀ b, (m'.arr64 b).size = (m.arr64 b).size := by
  induction n with
  | zero => intro m m' d s l h; simp [erCopyW] at h
  | succ n ih =>
    intro m m' d s l h b
    by_cases hl : l = 0
    · rw [erCopyW_nil n m d s l hl] at h; cases h; rfl
    · rw [erCopyW_step n m d s l hl] at h
      rw [ih _ _ _ _ _ h b]
      exact size_set64 _ _ _ _ _

theorem erToIwW_size {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : erToIwW n m o l = some (r, m')) : ∀ b, (m'.arr64 b).size = (m.arr64 b).size := by
  simp only [erToIwW] at h
  cases hal : allocW m l with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  simp only [hal] at h
  cases hcp : erCopyW (n - 1) m1 q o l with
  | none => simp [hcp] at h
  | some m2 =>
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  intro b
  have hm1 : m1 = allocMem m l := allocW_mem' hal
  rw [erCopyW_size _ _ _ _ _ _ hcp b, hm1]
  exact (allocMem_frame m l).2.2.1 b

/-- `cv_lps` under the stage relation: the level parameters as a fresh `IW` slice. -/
theorem cvLpsW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal}
    (h : L.Arena.cvLpsW n m q = some (r, m')) (hS : StageR dn vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ decRL (fun m => decHL m) 0 m' r cv.levelParams ∧
      (∀ b, (m'.arr64 b).size = (m.arr64 b).size) := by
  cases n with
  | zero => simp [L.Arena.cvLpsW] at h
  | succ n =>
  rw [L.Arena.cvLpsW_step] at h
  have hq0 : decCV (erA m) q.toNat = some cv := ArrExt.decCV (erecP_ext m) hq
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_words hq0
  have hsz : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  have e1 : rdW (m.arr64 EREC) (q + 1) = w1 := by
    have := rdW_off (a := erA m) (q := q) (k := 1) hsz (w := w1) (by simpa using hw1)
    simpa [erA] using this
  have e2 : rdW (m.arr64 EREC) (q + 2) = w2 := by
    have := rdW_off (a := erA m) (q := q) (k := 2) hsz (w := w2) (by simpa using hw2)
    simpa [erA] using this
  rw [e1, e2] at h
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (hslice?_bound _ _ _ _ hsl h0)
  obtain ⟨h2, hl, hdec, hS', hg, hb⟩ := erToIwW_stage h hS hsrc
  refine ⟨hS', hg, decRL_two h2 ?_ (by rw [hl]; exact hb), erToIwW_size h⟩
  rw [hl, hdec]; exact hsl


/-! ## `canon_ctx` -/

mutual
/-- **The model of `canon_ctx(cp, cq)`**. -/
def ctxW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, cp, cq => ctxK1 k cp cq (cnW k m (rdW (m.arr64 EREC) (cp + 2)))

/-- After `canon_names`. -/
def ctxK1 (k : Nat) (cp cq : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, m1) => ctxK2 k cq rc (L.Arena.cvLpsW k m1 cp)

/-- After the first `cv_lps`. -/
def ctxK2 (k : Nat) (cq : Word) (rc : List Word) : Option (List Word × Mem) →
    Option (List Word × Mem)
  | none => none
  | some (rp, m2) => ctxK3 rc rp (L.Arena.cvLpsW k m2 cq)

/-- After the second. -/
def ctxK3 (rc rp : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rq, m3) =>
    some ([rp.headD 0, rp.tail.headD 0, rq.headD 0, rq.tail.headD 0, rc.headD 0, rc.tail.headD 0], m3)
end

section arms
variable (k : Nat) (m m1 m2 m3 : Mem) (cp cq : Word) (rc rp rq : List Word)
theorem ctxW_succ : ctxW (k + 1) m cp cq = ctxK1 k cp cq (cnW k m (rdW (m.arr64 EREC) (cp + 2))) := by
  rw [ctxW]
theorem ctxK1_some : ctxK1 k cp cq (some (rc, m1)) = ctxK2 k cq rc (L.Arena.cvLpsW k m1 cp) := by
  rw [ctxK1]
theorem ctxK2_some : ctxK2 k cq rc (some (rp, m2)) = ctxK3 rc rp (L.Arena.cvLpsW k m2 cq) := by
  rw [ctxK2]
theorem ctxK3_some : ctxK3 rc rp (some (rq, m3)) =
    some ([rp.headD 0, rp.tail.headD 0, rq.headD 0, rq.tail.headD 0, rc.headD 0, rc.tail.headD 0],
      m3) := by
  rw [ctxK3]
end arms

grind_pattern [ind_grind] ctxW_succ => ctxW (k + 1) m cp cq
grind_pattern [ind_grind] ctxK1_some => ctxK1 k cp cq (some (rc, m1))
grind_pattern [ind_grind] ctxK2_some => ctxK2 k cq rc (some (rp, m2))
grind_pattern [ind_grind] ctxK3_some => ctxK3 rc rp (some (rq, m3))

theorem canonCtx_spec (p : Prog) (hp : CanonProg p) (n : Nat) (s₀ : St) (cp cq : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "canon_ctx" [cp, cq]
    ⦃fun r s' => LocEq s' s₀ ∧ ctxW n s₀.mem cp cq = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.canon_ctx]
  simp only [callFn, canonCtx]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        canonNames_spec p hp n,
        cvLps_specW p hp.iw_alloc hp.er_copy hp.er_to_iw hp.cv_lps n] <;>
      finish (gen := 20) [ctxW]


theorem ctxW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} (k : Nat)
    {m m' : Mem} {cp cq : Word} {r : List Word} {cv cv' : IConstantVal}
    (h : ctxW k m cp cq = some (r, m')) (hS : StageR dn vis fe m a)
    (hcv : decCV (erecP m) cp.toNat = some cv) (hcv' : decCV (erecP m) cq.toNat = some cv')
    (hP : PoolSmall m) (hL : LitInj a) :
    ∃ (cs : List NIdx) (a' : AState) (po pl qo ql co cl : Word),
      r = [po, pl, qo, ql, co, cl] ∧
      (ConRon.Arena.canonNames cv.levelParams.length).run a = .ok (cs, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PoolSmall m' ∧ LitInj a' ∧
      CtxR m' po pl qo ql co cl cv.levelParams cv'.levelParams cs := by
  cases k with
  | zero => simp [ctxW] at h
  | succ k =>
  rw [ctxW_succ] at h
  have hcv0 : decCV (erA m) cp.toNat = some cv := ArrExt.decCV (erecP_ext m) hcv
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_words hcv0
  have hsz : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  have e2 : rdW (m.arr64 EREC) (cp + 2) = w2 := by
    have := rdW_off (a := erA m) (q := cp) (k := 2) hsz (w := w2) (by simpa using hw2)
    simpa [erA] using this
  have hlen : w2.toNat = cv.levelParams.length := (hslice_len hsl).symm
  rw [e2] at h
  cases h1 : cnW k m w2 with
  | none => rw [h1] at h; simp [ctxK1] at h
  | some x1 =>
  obtain ⟨rc, m1⟩ := x1
  rw [h1, ctxK1_some] at h
  obtain ⟨cs, a1, hrun1, hS1, hg1, hd1, hv1, hP1⟩ := cnW_ok h1 hS hP
  cases h2 : L.Arena.cvLpsW k m1 cp with
  | none => rw [h2] at h; simp [ctxK2] at h
  | some x2 =>
  obtain ⟨rp, m2⟩ := x2
  rw [h2, ctxK2_some] at h
  have hcv1 : decCV (erecP m1) cp.toNat = some cv := ArrExt.decCV (IWGrow.erecPExtR hg1) hcv
  obtain ⟨hS2, hg2, hd2, hz2⟩ := cvLpsW_ok h2 hS1 hcv1
  cases h3 : L.Arena.cvLpsW k m2 cq with
  | none => rw [h3] at h; simp [ctxK3] at h
  | some x3 =>
  obtain ⟨rq, m3⟩ := x3
  rw [h3, ctxK3_some] at h
  have hcv2 : decCV (erecP m2) cq.toNat = some cv' :=
    ArrExt.decCV (IWGrow.erecPExtR (hg1.trans hg2)) hcv'
  obtain ⟨hS3, hg3, hd3, hz3⟩ := cvLpsW_ok h3 hS2 hcv2
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hu1 := decRL_unpack hd1
  have hu2 := decRL_unpack hd2
  have hu3 := decRL_unpack hd3
  have hgg := hg2.trans hg3
  have hgg' : IWGrow m1 m3 := hgg
  refine ⟨cs, a1, _, _, _, _, _, _, rfl, ?_, hS3, (hg1.trans hg2).trans hg3, ?_, ?_, ?_⟩
  · rw [← hlen]; exact hrun1
  · unfold PoolSmall; rw [hz3 POOL, hz2 POOL]; exact hP1
  · exact hL.of_view hv1
  · exact ⟨by rw [decHL_grow hg3 hu2.2]; exact hu2.1, hu3.1,
      by rw [decHL_grow hgg' hu1.2]; exact hu1.1, Nat.le_trans hu2.2 hg3.1, hu3.2,
      Nat.le_trans hu1.2 hgg'.1⟩

end L.Ind
