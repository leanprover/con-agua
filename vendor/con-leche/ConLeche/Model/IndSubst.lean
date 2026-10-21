module

public import ConLeche.Model.IndFrame
import ConLeche.Verify.Denote.Inst

public section

/-!
# The reading's substitution algebra (task #161)

The absorption laws at `Term`, and the `Term.instSeq`
corollaries (`instSeqAV_*`).

**Why they are cheap.**  `ConLeche/Term/Subst.lean` keeps only the
definitions and their clause equations; each law here is one structural
induction on `Term`, and each clause is one `simp only` plus the
inductive hypothesis.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory


universe w

namespace AVExprSubst

open ConLeche.Term.Term ConLeche.SetModel

/-! ## Absorption -/

/-- Two nested lifts with overlapping cuts collapse
(`Term.liftN_liftN_absorb`). -/
theorem liftN_liftN_absorb : ∀ (e : Term) {j k m : Nat}, k ≤ j →
    j ≤ k + m → ∀ n : Nat, liftN n (liftN m e k) j = liftN (m + n) e k := by
  intro e
  induction e with
  | bvar i =>
    intro j k m hkj hjk n
    by_cases h1 : i < k
    · simp only [liftN_bvar, ite_eq_left h1, ite_eq_left (show i < j by omega)]
    · simp only [liftN_bvar, ite_eq_right h1,
        ite_eq_right (show ¬ i + m < j by omega)]
      congr 1
      omega
  | sort u => intro _ _ _ _ _ _; rfl
  | const c us => intro _ _ _ _ _ _; rfl
  | prf => intro _ _ _ _ _ _; rfl
  | app f a ihf iha =>
    intro j k m hkj hjk n
    simp only [liftN_app, ihf hkj hjk n, iha hkj hjk n]
  | lam A b ihA ihb =>
    intro j k m hkj hjk n
    simp only [liftN_lam, ihA hkj hjk n,
      ihb (show k + 1 ≤ j + 1 by omega) (show j + 1 ≤ k + 1 + m by omega) n]
  | pi A B ihA ihB =>
    intro j k m hkj hjk n
    simp only [liftN_pi, ihA hkj hjk n,
      ihB (show k + 1 ≤ j + 1 by omega) (show j + 1 ≤ k + 1 + m by omega) n]
  | letE v b ihv ihb =>
    intro j k m hkj hjk n
    simp only [liftN_letE, ihv hkj hjk n,
      ihb (show k + 1 ≤ j + 1 by omega) (show j + 1 ≤ k + 1 + m by omega) n]
  | eqE a b iha ihb =>
    intro j k m hkj hjk n
    simp only [liftN_eqE, iha hkj hjk n, ihb hkj hjk n]
  | fst e ihe =>
    intro j k m hkj hjk n
    simp only [liftN_fst, ihe hkj hjk n]
  | snd e ihe =>
    intro j k m hkj hjk n
    simp only [liftN_snd, ihe hkj hjk n]

/-- Instantiating inside the range a lift just created absorbs one
unit of it (`Term.inst_liftN_absorb`). -/
theorem inst_liftN_absorb : ∀ (e : Term) {j k m : Nat}, j ≤ k →
    k ≤ j + m → ∀ a : Term, inst (liftN (m + 1) e j) a k = liftN m e j := by
  intro e
  induction e with
  | bvar i =>
    intro j k m hjk hkj a
    by_cases h1 : i < j
    · simp only [liftN_bvar, inst_bvar, ite_eq_left h1,
        ite_eq_left (show i < k by omega)]
    · simp only [liftN_bvar, inst_bvar, ite_eq_right h1,
        ite_eq_right (show ¬ i + (m + 1) < k by omega),
        ite_eq_right (show ¬ i + (m + 1) = k by omega)]
      congr 1
  | sort u => intro _ _ _ _ _ _; rfl
  | const c us => intro _ _ _ _ _ _; rfl
  | prf => intro _ _ _ _ _ _; rfl
  | app f b ihf ihb =>
    intro j k m hjk hkj a
    simp only [liftN_app, inst_app, ihf hjk hkj a, ihb hjk hkj a]
  | lam A b ihA ihb =>
    intro j k m hjk hkj a
    simp only [liftN_lam, inst_lam, ihA hjk hkj a,
      ihb (show j + 1 ≤ k + 1 by omega) (show k + 1 ≤ j + 1 + m by omega) a]
  | pi A B ihA ihB =>
    intro j k m hjk hkj a
    simp only [liftN_pi, inst_pi, ihA hjk hkj a,
      ihB (show j + 1 ≤ k + 1 by omega) (show k + 1 ≤ j + 1 + m by omega) a]
  | letE v b ihv ihb =>
    intro j k m hjk hkj a
    simp only [liftN_letE, inst_letE, ihv hjk hkj a,
      ihb (show j + 1 ≤ k + 1 by omega) (show k + 1 ≤ j + 1 + m by omega) a]
  | eqE b c ihb ihc =>
    intro j k m hjk hkj a
    simp only [liftN_eqE, inst_eqE, ihb hjk hkj a,
      ihc hjk hkj a]
  | fst e ihe =>
    intro j k m hjk hkj a
    simp only [liftN_fst, inst_fst, ihe hjk hkj a]
  | snd e ihe =>
    intro j k m hjk hkj a
    simp only [liftN_snd, inst_snd, ihe hjk hkj a]

/-- Instantiating strictly above a lift moves under it, with the cut
shrunk by the lift amount (`Term.inst_liftN_comm`). -/
theorem inst_liftN_comm : ∀ (e : Term) {j k m : Nat}, j + m ≤ k →
    ∀ a : Term, inst (liftN m e j) a k = liftN m (inst e a (k - m)) j := by
  intro e
  induction e with
  | bvar i =>
    intro j k m hjk a
    by_cases h1 : i < j
    · simp only [liftN_bvar, inst_bvar, ite_eq_left h1,
        ite_eq_left (show i < k by omega), ite_eq_left (show i < k - m by omega)]
    · by_cases h2 : i < k - m
      · simp only [liftN_bvar, inst_bvar, ite_eq_right h1, ite_eq_left h2,
          ite_eq_left (show i + m < k by omega)]
      · by_cases h3 : i = k - m
        · simp only [liftN_bvar, inst_bvar, ite_eq_right h1, ite_eq_right h2,
            ite_eq_left h3, ite_eq_right (show ¬ i + m < k by omega),
            ite_eq_left (show i + m = k by omega)]
          rw [liftN_liftN_absorb a (Nat.zero_le j)
              (show j ≤ 0 + (k - m) by omega) m,
            show k - m + m = k by omega]
        · simp only [liftN_bvar, inst_bvar, ite_eq_right h1, ite_eq_right h2,
            ite_eq_right h3, ite_eq_right (show ¬ i + m < k by omega),
            ite_eq_right (show ¬ i + m = k by omega),
            ite_eq_right (show ¬ i - 1 < j by omega)]
          congr 1
          omega
  | sort u => intro _ _ _ _ _; rfl
  | const c us => intro _ _ _ _ _; rfl
  | prf => intro _ _ _ _ _; rfl
  | app f b ihf ihb =>
    intro j k m hjk a
    simp only [liftN_app, inst_app, ihf hjk a, ihb hjk a]
  | lam A b ihA ihb =>
    intro j k m hjk a
    simp only [liftN_lam, inst_lam, ihA hjk a,
      ihb (show j + 1 + m ≤ k + 1 by omega) a]
    rw [show k + 1 - m = k - m + 1 by omega]
  | pi A B ihA ihB =>
    intro j k m hjk a
    simp only [liftN_pi, inst_pi, ihA hjk a,
      ihB (show j + 1 + m ≤ k + 1 by omega) a]
    rw [show k + 1 - m = k - m + 1 by omega]
  | letE v b ihv ihb =>
    intro j k m hjk a
    simp only [liftN_letE, inst_letE, ihv hjk a,
      ihb (show j + 1 + m ≤ k + 1 by omega) a]
    rw [show k + 1 - m = k - m + 1 by omega]
  | eqE b c ihb ihc =>
    intro j k m hjk a
    simp only [liftN_eqE, inst_eqE, ihb hjk a, ihc hjk a]
  | fst e ihe =>
    intro j k m hjk a
    simp only [liftN_fst, inst_fst, ihe hjk a]
  | snd e ihe =>
    intro j k m hjk a
    simp only [liftN_snd, inst_snd, ihe hjk a]

/-- Two instantiations commute, with the cuts adjusted
(`Term.inst_inst_comm`). -/
theorem inst_inst_comm : ∀ (e : Term) {j k : Nat}, j ≤ k →
    ∀ a b : Term,
    inst (inst e b j) a k = inst (inst e a (k + 1)) (inst b a (k - j)) j := by
  intro e
  induction e with
  | bvar i =>
    intro j k hjk a b
    by_cases h1 : i < j
    · simp only [inst_bvar, ite_eq_left h1, ite_eq_left (show i < k by omega),
        ite_eq_left (show i < k + 1 by omega)]
    · by_cases h2 : i = j
      · simp only [inst_bvar, ite_eq_right h1, ite_eq_left h2,
          ite_eq_left (show i < k + 1 by omega)]
        rw [inst_liftN_comm b (show 0 + j ≤ k by omega) a]
      · by_cases h3 : i < k + 1
        · simp only [inst_bvar, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3,
            ite_eq_left (show i - 1 < k by omega)]
        · by_cases h4 : i = k + 1
          · simp only [inst_bvar, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
              ite_eq_left h4, ite_eq_right (show ¬ i - 1 < k by omega),
              ite_eq_left (show i - 1 = k by omega)]
            rw [inst_liftN_absorb a (Nat.zero_le j)
              (show j ≤ 0 + k by omega)]
          · simp only [inst_bvar, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
              ite_eq_right h4, ite_eq_right (show ¬ i - 1 < k by omega),
              ite_eq_right (show ¬ i - 1 = k by omega),
              ite_eq_right (show ¬ i - 1 < j by omega),
              ite_eq_right (show ¬ i - 1 = j by omega)]
  | sort u => intro _ _ _ _ _; rfl
  | const c us => intro _ _ _ _ _; rfl
  | prf => intro _ _ _ _ _; rfl
  | app f c ihf ihc =>
    intro j k hjk a b
    simp only [inst_app, ihf hjk, ihc hjk]
  | lam A c ihA ihc =>
    intro j k hjk a b
    simp only [inst_lam, ihA hjk, ihc (show j + 1 ≤ k + 1 by omega)]
    rw [show k + 1 - (j + 1) = k - j by omega]
  | pi A B ihA ihB =>
    intro j k hjk a b
    simp only [inst_pi, ihA hjk, ihB (show j + 1 ≤ k + 1 by omega)]
    rw [show k + 1 - (j + 1) = k - j by omega]
  | letE v b ihv ihb =>
    intro j k hjk a b
    simp only [inst_letE, ihv hjk, ihb (show j + 1 ≤ k + 1 by omega)]
    rw [show k + 1 - (j + 1) = k - j by omega]
  | eqE c d ihc ihd =>
    intro j k hjk a b
    simp only [inst_eqE, ihc hjk, ihd hjk]
  | fst e ihe =>
    intro j k hjk a b
    simp only [inst_fst, ihe hjk]
  | snd e ihe =>
    intro j k hjk a b
    simp only [inst_snd, ihe hjk]

/-- A reading closed in the lifting sense is fixed by any
instantiation.  The `Term` closedness currency is the lifting
equation the carrier stores (`EnvModel.acval_closed`,
`denote_closed`), not a `bvarsBelow` predicate — so this is
`inst_liftN_absorb` at `m = 0` rather than a `bvarsBelow` induction. -/
theorem inst_eq_self_of_closed {X : Term} (h : ∀ k, liftN 1 X k = X)
    (a : Term) (k : Nat) : inst X a k = X := by
  have h1 : inst (liftN 1 X k) a k = liftN 0 X k :=
    inst_liftN_absorb X (m := 0) (Nat.le_refl k) (Nat.le_refl k) a
  rw [h k, Term.liftN_zero] at h1
  exact h1

end AVExprSubst

/-! ## `instSeq` corollaries -/

open ConLeche.Term.Term in
/-- Instantiating the variables a lift just introduced, one per
argument. -/
theorem instSeqAV_liftN : ∀ (as : List Term) (t : Nat) (a : Term),
    as.length ≤ t + 1 →
    Term.instSeq as t (liftN (t + 1) a 0)
      = liftN (t + 1 - as.length) a 0 := by
  intro as
  induction as with
  | nil => intro t a _; simp
  | cons x xs ih =>
    intro t a hlen
    simp only [List.length_cons] at hlen
    rw [Term.instSeq_cons,
      AVExprSubst.inst_liftN_absorb a (Nat.zero_le t) (by omega) x]
    cases xs with
    | nil => simp
    | cons y ys =>
      simp only [List.length_cons] at hlen
      have ht : t - 1 + 1 = t := by omega
      have h := ih (t - 1) a (by simp only [List.length_cons]; omega)
      rw [ht] at h
      rw [h]
      simp only [List.length_cons]
      congr 1
      omega

open ConLeche.Term.Term in
/-- **Resolving a variable in the substituted range**:
with `k` arguments at cuts `c + k - 1 … c`,
the variable `c + i` becomes the `i`-th argument counted from the
innermost, lifted past the `c` binders the residual sits under. -/
theorem instSeqAV_bvar_hit : ∀ (as : List Term) (c i : Nat) (x : Term),
    as[as.length - 1 - i]? = some x → i < as.length →
    Term.instSeq as (c + as.length - 1) (.bvar (c + i))
      = liftN c x 0 := by
  intro as
  induction as with
  | nil => intro c i x _ h; simp at h
  | cons a as ih =>
    intro c i x hx hi
    simp only [List.length_cons] at hi
    have hlen : c + (as.length + 1) - 1 = c + as.length := by omega
    by_cases hin : i = as.length
    · subst hin
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      rw [List.length_cons, hlen, Term.instSeq_cons, inst_bvar,
        ite_eq_right (by omega), ite_eq_left rfl]
      rcases Nat.eq_zero_or_pos (c + as.length) with h0 | h0
      · have hc : c = 0 := by omega
        have hl : as.length = 0 := by omega
        rw [hc, List.eq_nil_of_length_eq_zero hl]
        simp
      · obtain ⟨m, hm⟩ : ∃ m, c + as.length = m + 1 :=
          ⟨c + as.length - 1, by omega⟩
        rw [hm, show m + 1 - 1 = m from by omega,
          instSeqAV_liftN as m a (by omega)]
        congr 1
        omega
    · have hilt : i < as.length := by omega
      rw [List.length_cons, hlen, Term.instSeq_cons, inst_bvar,
        ite_eq_left (by omega)]
      refine ih c i x ?_ hilt
      simp only [List.length_cons] at hx
      rw [show as.length + 1 - 1 - i = (as.length - 1 - i) + 1 from by
        omega] at hx
      simpa using hx

/-! ## What the stages read -/

open ConLeche.Term.Term in
/-- `instSeq` past an innermost instantiation. -/
theorem instSeqAV_inst0 : ∀ (as : List Term) (t : Nat) (X b : Term),
    as.length ≤ t + 1 →
    Term.instSeq as t (X.inst b 0)
      = (Term.instSeq as (t + 1) X).inst
          (Term.instSeq as t b) 0 := by
  intro as
  induction as with
  | nil => intro t X b _; rfl
  | cons w as ih =>
    intro t X b hlen
    simp only [List.length_cons] at hlen
    rw [Term.instSeq_cons (e := X.inst b 0),
      AVExprSubst.inst_inst_comm X (Nat.zero_le t) w b, Nat.sub_zero]
    cases as with
    | nil =>
      simp only [Term.instSeq_nil]
      rw [Term.instSeq_cons, Term.instSeq_cons, Nat.add_sub_cancel]
      simp
    | cons y ys =>
      have h := ih (t - 1) (X.inst w (t + 1)) (b.inst w t)
        (by simp only [List.length_cons] at hlen ⊢; omega)
      rw [h, Term.instSeq_cons (t := t + 1) (e := X),
        Term.instSeq_cons (t := t) (e := b), Nat.add_sub_cancel,
        show t - 1 + 1 = t from by
          simp only [List.length_cons] at hlen; omega]

open ConLeche.Term.Term in
/-- `instSeq` past a lift at the top. -/
theorem instSeqAV_liftN0 : ∀ (vs : List Term) (t m : Nat) (Y : Term),
    vs.length ≤ t + 1 →
    Term.instSeq vs (t + m) (liftN m Y 0)
      = liftN m (Term.instSeq vs t Y) 0 := by
  intro vs
  induction vs with
  | nil => intro t m Y _; rfl
  | cons a vs ih =>
    intro t m Y h
    show Term.instSeq vs (t + m - 1)
        ((liftN m Y 0).inst a (t + m)) = _
    rw [AVExprSubst.inst_liftN_comm Y (by omega) a, Nat.add_sub_cancel]
    cases t with
    | zero =>
      obtain rfl : vs = [] := by
        simp only [List.length_cons] at h
        exact List.eq_nil_of_length_eq_zero (by omega)
      rfl
    | succ t' =>
      rw [show t' + 1 + m - 1 = t' + m from by omega]
      exact ih t' m (Y.inst a (t' + 1))
        (by simp only [List.length_cons] at h; omega)

end ConLeche.Model
