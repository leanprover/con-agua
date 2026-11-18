module

meta import ConAgua.L.Semantics
import ConAgua.Census.Attr
public import ConAgua.L.Notation
public import ConAgua.Arena.NatShiftFacts
public import ConAgua.Arena.Word
import ConAgua.Arena.NatDivFacts
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.Logic
import ConAgua.L.For
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The word steps of `nat_divmod` (lane `bigdiv`)

Three register-only functions of the limb-wise long division (`NatDiv.lean`):

* `div_norm(x)`: the shift `s` that normalises a nonzero `x` (con-ron's `norm_shift`);
* `div_2by1(u1, u0, d, v)`: `⌊(u1 · 2^64 + u0) / d⌋` and the remainder, for `u1 < d` (con-ron's
  `u128` division in `dm_step`): Möller and Granlund's estimate with the reciprocal `v` (Möller and
  Granlund, "Improved division by invariant integers", IEEE TC 2011; GMP's
  `udiv_qrnnd_preinv`), then two correction loops that make the result exact whatever `v` is;
* `div_recip(d)`: that reciprocal, `⌊(2^128 - 1) / d⌋ - 2^64`, by Newton steps from a tangent.

Only the speed depends on `v`: with the exact reciprocal (tested, not proved, as con-ron tests
Knuth's "at most two corrections") neither correction loop of `div_2by1` runs.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- `div_norm`'s first halving step. -/
def nrmFirst : Stmt := lblk (x, s) {
  if x < 0x100000000 { x := x << 32; s := 32 }
}

/-- A middle halving step of `div_norm`: shift by `k` below `c = 2^(64 - k)`. -/
def nrmStep (c k : Word) : Stmt := lblk (x, s) {
  if x < ⟪c⟫ { x := x << ⟪k⟫; s := s + ⟪k⟫ }
}

/-- `div_norm`'s last step: count the top bit. -/
def nrmLast : Stmt := lblk (x, s) {
  if x < 0x8000000000000000 { s := s + 1 }
}

/-- `div_norm(x)`: the left shift `s ≤ 63` that sets the top bit of `x ≠ 0` (con-ron's
`norm_shift`), in six halving steps. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def divNorm : FunDecl := lfn (x) locals (s) {
  ⟪nrmFirst⟫;
  ⟪nrmStep 0x1000000000000 16⟫;
  ⟪nrmStep 0x100000000000000 8⟫;
  ⟪nrmStep 0x1000000000000000 4⟫;
  ⟪nrmStep 0x4000000000000000 2⟫;
  ⟪nrmLast⟫;
  return s
}

/-- `div_recip`'s start: the tangent of `1/x` at `3/4`. -/
def rcpInit : Stmt := lblk (d, v, t, l, h, e, j, k) {
  t := 0 - 1 - d;
  t := t + mulhi(t, 0xC71C71C71C71C71C);
  if 0x1C71C71C71C71C71 < t { v := t - 0x1C71C71C71C71C71 }
}

/-- `div_recip`'s five Newton steps. -/
def rcpLoop : Stmt := lblk (d, v, t, l, h, e, j, k) {
  for j < k {
    l := d * v;
    h := d + mulhi(d, v);
    e := 0 - h - u64(l != 0);
    v := v + e + mulhi(v, e)
  }
}

/-- `div_recip(d)`: the reciprocal `⌊(2^128 - 1) / d⌋ - 2^64` of a normalised `d` (Möller and
Granlund's `v`): the tangent of `1/x` at `3/4` (from below, about 3 bits), five Newton steps
`v := v + e + ⌊v e / 2^64⌋` with `e` the top word of `2^128 - d (2^64 + v)` (from below, at most
2 under), then `div_2by1` of `(2^64 - 1 - d) · 2^64 + 2^64 - 1` by `d` with that estimate. Only
the speed of `div_2by1` depends on the estimate. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def divRecip : FunDecl := lfn (d) locals (v, t, l, h, e, j, k) {
  t := 0 - 1 - d;
  t := t + mulhi(t, 0xC71C71C71C71C71C);
  if 0x1C71C71C71C71C71 < t { v := t - 0x1C71C71C71C71C71 };
  k := 5;
  ⟪rcpLoop⟫;
  (v, t) := call div_2by1(0 - 1 - d, 0 - 1, d, v);
  return v
}

/-- `div_recip` after the tangent. -/
def rcpTail : Stmt := lblk (d, v, t, l, h, e, j, k) {
  k := 5;
  ⟪rcpLoop⟫;
  (v, t) := call div_2by1(0 - 1 - d, 0 - 1, d, v);
  return v
}

/-- The body is the tangent then the rest (`rfl`: the function text stays as written). -/
private theorem divRecip_body : divRecip.body = rcpInit.snoc rcpTail := rfl

/-- `div_2by1`'s estimate (Möller and Granlund's, with two corrections). -/
def d2Est : Stmt := lblk (u1, u0, d, v, q, q0, r, plo, phi, t) {
  q0 := v * u1 + u0;
  q := mulhi(v, u1) + u1 + u64(q0 < u0) + 1;
  r := u0 - q * d;
  if q0 < r { q := q - 1; r := r + d };
  if d <= r { q := q + 1 }
}

/-- `div_2by1`'s down loop: `q := q - 1` while `q · d > u`. -/
def d2Down : Stmt := lblk (u1, u0, d, v, q, q0, r, plo, phi, t) {
  while u1 < phi || (phi == u1 && u0 < plo) {
    q := q - 1;
    phi := phi - u64(plo < d);
    plo := plo - d
  }
}

/-- `div_2by1`'s up loop: `q := q + 1` while the remainder is at least `d`. -/
def d2Up : Stmt := lblk (u1, u0, d, v, q, q0, r, plo, phi, t) {
  while t != 0 || d <= r {
    q := q + 1;
    t := t - u64(r < d);
    r := r - d
  }
}

/-- `div_2by1(u1, u0, d, v)`: `(q, r)` with `u1 · 2^64 + u0 = q · d + r`, `r < d`, for `u1 < d`
(con-ron's `u128` division in `dm_step`). The estimate is Möller and Granlund's
(`udiv_qrnnd_preinv`, with the reciprocal `v` of a normalised `d`); the two loops then step `q`
down while `q · d > u` and up while the remainder is at least `d`, so the result is exact
whatever `v` is (with the true reciprocal neither loop runs). -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def div2by1 : FunDecl := lfn (u1, u0, d, v) locals (q, q0, r, plo, phi, t) {
  q0 := v * u1 + u0;
  q := mulhi(v, u1) + u1 + u64(q0 < u0) + 1;
  r := u0 - q * d;
  if q0 < r { q := q - 1; r := r + d };
  if d <= r { q := q + 1 };
  plo := q * d;
  phi := mulhi(q, d);
  ⟪d2Down⟫;
  r := u0 - plo;
  t := u1 - phi - u64(u0 < plo);
  ⟪d2Up⟫;
  return (q, r)
}

/-- `div_2by1` after the estimate. -/
def d2Tail : Stmt := lblk (u1, u0, d, v, q, q0, r, plo, phi, t) {
  plo := q * d;
  phi := mulhi(q, d);
  ⟪d2Down⟫;
  r := u0 - plo;
  t := u1 - phi - u64(u0 < plo);
  ⟪d2Up⟫;
  return (q, r)
}

/-- The body is the estimate then the rest (`rfl`: the function text stays as written). -/
private theorem div2by1_body : div2by1.body = d2Est.snoc d2Tail := rfl

/-! ## `div_2by1`'s loops -/

section loops
variable (p : Prog)

/-- One step of the down loop keeps `phi · 2^64 + plo = q · d` (while that exceeds `u ≥ 0`). -/
theorem d2_down_step (u1 u0 phi plo q d : Word)
    (hinv : phi.toNat * 2 ^ 64 + plo.toNat = q.toNat * d.toNat)
    (hgt : u1.toNat * 2 ^ 64 + u0.toNat < phi.toNat * 2 ^ 64 + plo.toNat) :
    (phi - if plo < d then 1 else 0).toNat * 2 ^ 64 + (plo - d).toNat = (q - 1).toNat * d.toNat := by
  have hq : 1 ≤ q.toNat := by
    rcases Nat.eq_zero_or_pos q.toNat with h0 | h0
    · rw [h0] at hinv; omega
    · omega
  have hq1 : (q - 1).toNat = q.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by simpa [UInt64.le_iff_toNat_le] using hq)]; rfl
  have hd : d.toNat ≤ q.toNat * d.toNat := Nat.le_mul_of_pos_left _ hq
  rw [hq1, Nat.sub_mul, Nat.one_mul]
  generalize q.toNat * d.toNat = P at *
  have := plo.toNat_lt
  have := d.toNat_lt
  by_cases hlt : plo < d
  · have hlt' : plo.toNat < d.toNat := hlt
    have hphi : 1 ≤ phi.toNat := by omega
    simp only [hlt, ite_true]
    rw [UInt64.toNat_sub_of_le _ _ (by simpa [UInt64.le_iff_toNat_le] using hphi), UInt64.toNat_sub,
      show (1 : Word).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
    grind
  · have hlt' : d.toNat ≤ plo.toNat := Nat.le_of_not_lt hlt
    simp only [hlt, ite_false]
    rw [UInt64.toNat_sub_of_le _ _ hlt', show (0 : Word) = 0 from rfl, UInt64.sub_zero]
    omega

/-- The down loop's invariant: `phi · 2^64 + plo = q · d`, with `u = u1 · 2^64 + u0` and `u1 < d`. -/
def D2DownInv (m : Mem) (D U : Nat) (s : St) : Prop :=
  s.mem = m ∧ (s.loc 2).toNat = D ∧ (s.loc 0).toNat * 2 ^ 64 + (s.loc 1).toNat = U ∧
  (s.loc 0).toNat < D ∧ (s.loc 8).toNat * 2 ^ 64 + (s.loc 7).toNat = (s.loc 4).toNat * D

/-- After the down loop: the invariant, and `q · d ≤ u`. -/
def D2DownPost (m : Mem) (D U : Nat) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ D2DownInv m D U s' ∧ (s'.loc 8).toNat * 2 ^ 64 + (s'.loc 7).toNat ≤ U

theorem d2Down_spec (m : Mem) (D U : Nat) (n : Nat) (s₀ : St) (h : D2DownInv m D U s₀) :
    ⦃fun s => s = s₀⦄ exec p n d2Down ⦃fun r s' => D2DownPost m D U r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [D2DownInv, D2DownPost] at h ⊢
    rw [exec, step_while (w := d2Down) rfl]
    vcgen [step, evalE, evalC, setLoc, setLocs, ih]
    all_goals clear ih
    all_goals (try simp only [D2DownInv, D2DownPost, St.setLoc_loc, St.setLoc_mem, Cmp.eval, Cmp.evalW, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals try grind
    all_goals
      have := d2_down_step (s₀.loc 0) (s₀.loc 1) (s₀.loc 8) (s₀.loc 7) (s₀.loc 4) (s₀.loc 2)
        (by grind) (by grind)
      grind

/-- One step of the up loop keeps `t · 2^64 + r + q · d = u` (while `t · 2^64 + r ≥ d`); `q + 1`
does not wrap since `(q + 1) · d ≤ u < d · 2^64`. -/
theorem d2_up_step (t r q d : Word) (U : Nat)
    (hinv : t.toNat * 2 ^ 64 + r.toNat + q.toNat * d.toNat = U) (hU : U < d.toNat * 2 ^ 64)
    (hge : d.toNat ≤ t.toNat * 2 ^ 64 + r.toNat) :
    (t - if r < d then 1 else 0).toNat * 2 ^ 64 + (r - d).toNat + (q + 1).toNat * d.toNat = U := by
  have hq : q.toNat + 1 < 2 ^ 64 := by
    rcases Nat.lt_or_ge q.toNat (2 ^ 64 - 1) with h | h
    · omega
    · have : (2 ^ 64 - 1) * d.toNat ≤ q.toNat * d.toNat := Nat.mul_le_mul_right _ h
      rw [Nat.sub_mul] at this
      omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : Word).toNat = 1 from rfl, Nat.mod_eq_of_lt hq]
  rw [hq1, Nat.add_mul, Nat.one_mul]
  generalize q.toNat * d.toNat = P at *
  have := r.toNat_lt
  have := d.toNat_lt
  by_cases hlt : r < d
  · have hlt' : r.toNat < d.toNat := hlt
    have ht : 1 ≤ t.toNat := by omega
    simp only [hlt, ite_true]
    rw [UInt64.toNat_sub_of_le _ _ (by simpa [UInt64.le_iff_toNat_le] using ht), UInt64.toNat_sub,
      show (1 : Word).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
    grind
  · have hlt' : d.toNat ≤ r.toNat := Nat.le_of_not_lt hlt
    simp only [hlt, ite_false]
    rw [UInt64.toNat_sub_of_le _ _ hlt', show (0 : Word) = 0 from rfl, UInt64.sub_zero]
    omega

/-- The up loop's invariant: `t · 2^64 + r + q · d = u < d · 2^64`. -/
def D2UpInv (m : Mem) (D U : Nat) (s : St) : Prop :=
  s.mem = m ∧ (s.loc 2).toNat = D ∧ U < D * 2 ^ 64 ∧
  (s.loc 9).toNat * 2 ^ 64 + (s.loc 6).toNat + (s.loc 4).toNat * D = U

/-- After the up loop: `q · d + r = u`, `r < d`. -/
def D2UpPost (m : Mem) (D U : Nat) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ s'.mem = m ∧ (s'.loc 4).toNat * D + (s'.loc 6).toNat = U ∧ (s'.loc 6).toNat < D

theorem d2Up_spec (m : Mem) (D U : Nat) (n : Nat) (s₀ : St) (h : D2UpInv m D U s₀) :
    ⦃fun s => s = s₀⦄ exec p n d2Up ⦃fun r s' => D2UpPost m D U r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [D2UpInv, D2UpPost] at h ⊢
    rw [exec, step_while (w := d2Up) rfl]
    vcgen [step, evalE, evalC, setLoc, setLocs, ih]
    all_goals clear ih
    all_goals (try simp only [D2UpInv, D2UpPost, St.setLoc_loc, St.setLoc_mem, Cmp.eval, Cmp.evalW, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals try grind
    all_goals
      have := d2_up_step (s₀.loc 9) (s₀.loc 6) (s₀.loc 4) (s₀.loc 2) U (by grind) (by grind) (by grind)
      grind

theorem d2Down_step_spec (m : Mem) (D U : Nat) (n : Nat) (s₀ : St) (h : D2DownInv m D U s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) d2Down ⦃fun r s' => D2DownPost m D U r s'; ⊤⦄ :=
  Triple.step_exec (d2Down_spec p m D U (n + 1) s₀ h)

theorem d2Up_step_spec (m : Mem) (D U : Nat) (n : Nat) (s₀ : St) (h : D2UpInv m D U s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) d2Up ⦃fun r s' => D2UpPost m D U r s'; ⊤⦄ :=
  Triple.step_exec (d2Up_spec p m D U (n + 1) s₀ h)

/-- The estimate changes only `q`, `q0` and `r`. -/
theorem d2Est_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ step p (exec p n) d2Est
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
      s'.loc 2 = s₀.loc 2; ⊤⦄ := by
  unfold d2Est
  vcgen [step, evalE, evalC, setLoc] <;>
    simp only [St.setLoc_loc, St.setLoc_mem, Nat.reduceEqDiff, reduceIte] <;> trivial

/-- A call that keeps the memory returns the caller's state (`callFn` restores the locals). -/
theorem St.restore (s s₀ : St) (h : s.mem = s₀.mem) : ({ mem := s.mem, loc := s₀.loc } : St) = s₀ := by
  cases s₀; simp_all

/-- The Newton loop touches neither the memory nor `d`. -/
def RcpInv (m : Mem) (D : Word) (s : St) : Prop := s.mem = m ∧ s.loc 0 = D

def RcpPost (m : Mem) (D : Word) (r : Sig) (s' : St) : Prop := r = .normal ∧ s'.mem = m ∧ s'.loc 0 = D

theorem rcpLoop_spec (m : Mem) (D : Word) (n : Nat) (s₀ : St) (h : RcpInv m D s₀) :
    ⦃fun s => s = s₀⦄ exec p n rcpLoop ⦃fun r s' => RcpPost m D r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [RcpInv, RcpPost] at h ⊢
    rw [exec, step_while (w := rcpLoop) rfl]
    vcgen [step, evalE, evalC, setLoc, setLocs, ih]
    all_goals clear ih
    all_goals (try simp only [RcpInv, RcpPost, St.setLoc_loc, St.setLoc_mem, Nat.reduceEqDiff,
      reduceIte] at *)
    all_goals grind

/-- The tangent touches neither the memory nor `d`. -/
theorem rcpInit_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ step p (exec p n) rcpInit
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ s'.loc 0 = s₀.loc 0; ⊤⦄ := by
  unfold rcpInit
  vcgen [step, evalE, evalC, setLoc] <;>
    simp only [St.setLoc_loc, St.setLoc_mem, Nat.reduceEqDiff, reduceIte] <;> trivial

theorem rcpLoop_step_spec (m : Mem) (D : Word) (n : Nat) (s₀ : St) (h : RcpInv m D s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) rcpLoop ⦃fun r s' => RcpPost m D r s'; ⊤⦄ :=
  Triple.step_exec (rcpLoop_spec p m D (n + 1) s₀ h)

/-- `div_recip`'s final `div_2by1` divides `(2^64 - 1 - d) · 2^64 + 2^64 - 1` by `d ≥ 2^63`: its
high word is below `d`. -/
theorem recip_hi_lt (d : Word) (hd : 2 ^ 63 ≤ d.toNat) : (0 - 1 - d).toNat < d.toNat := by
  have h1 : (0 - 1 : Word).toNat = 2 ^ 64 - 1 := rfl
  have := d.toNat_lt
  rw [UInt64.toNat_sub_of_le _ _ (by simp only [UInt64.le_iff_toNat_le, h1]; omega), h1]
  omega

end loops

/-! ## `div_norm`'s steps -/

section norm
variable (p : Prog)

/-- After a step with threshold `2^a`: `x_cur = x · 2^s ≥ 2^a`, `s ≤ a`. -/
def NrmInv (X a : Nat) (s : St) : Prop :=
  (s.loc 0).toNat = X * 2 ^ (s.loc 1).toNat ∧ 2 ^ a ≤ (s.loc 0).toNat ∧ (s.loc 1).toNat ≤ a

/-- At the end: `x · 2^s` is a word with its top bit set, `s ≤ 63`. -/
def NrmFin (X : Nat) (s : St) : Prop :=
  (s.loc 1).toNat ≤ 63 ∧ X * 2 ^ (s.loc 1).toNat < 2 ^ 64 ∧ 2 ^ 63 ≤ X * 2 ^ (s.loc 1).toNat

/-- A shift by `b` of a word below `2^(64 - b)` does not wrap. -/
theorem shl_toNat_of_lt (x k : Word) (a b : Nat) (hk : k.toNat = b) (hab : a + b = 64)
    (hx : x.toNat < 2 ^ a) : (x <<< k).toNat = x.toNat * 2 ^ b := by
  have hb : b < 64 ∨ b = 64 := by omega
  rw [UInt64.toNat_shiftLeft, hk, Nat.shiftLeft_eq]
  rcases hb with hb | hb
  · rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt]
    calc x.toNat * 2 ^ b < 2 ^ a * 2 ^ b := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
      _ = 2 ^ 64 := by rw [← Nat.pow_add, hab]
  · subst hb
    have : a = 0 := by omega
    subst this
    have : x.toNat = 0 := by omega
    simp [this]

/-- The shifting arm of a middle step. -/
theorem nrm_shift (x s k : Word) (X a b : Nat) (hk : k.toNat = b) (hab : a + b = 64) (hba : b ≤ a)
    (hx : x.toNat = X * 2 ^ s.toNat) (hlo : 2 ^ (a - b) ≤ x.toNat) (hs : s.toNat ≤ a - b)
    (hlt : x.toNat < 2 ^ a) :
    (x <<< k).toNat = X * 2 ^ (s + k).toNat ∧ 2 ^ a ≤ (x <<< k).toNat ∧ (s + k).toNat ≤ a := by
  have hsk : (s + k).toNat = s.toNat + b := by
    rw [UInt64.toNat_add, hk, Nat.mod_eq_of_lt (by omega)]
  rw [shl_toNat_of_lt x k a b hk hab hlt, hsk, hx, Nat.pow_add, Nat.mul_assoc]
  refine ⟨rfl, ?_, by omega⟩
  rw [← Nat.mul_assoc, ← hx]
  calc 2 ^ a = 2 ^ (a - b) * 2 ^ b := by rw [← Nat.pow_add]; congr 1; omega
    _ ≤ x.toNat * 2 ^ b := Nat.mul_le_mul_right _ hlo

theorem nrmFirst_spec (n : Nat) (s₀ : St) (X : Nat) (h0 : s₀.loc 1 = 0) (hX : (s₀.loc 0).toNat = X)
    (hpos : 0 < X) :
    ⦃fun s => s = s₀⦄ step p (exec p n) nrmFirst
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ NrmInv X 32 s'; ⊤⦄ := by
  unfold nrmFirst
  vcgen [step, evalE, evalC, setLoc]
  all_goals (try simp only [NrmInv, St.setLoc_loc, St.setLoc_mem, Cmp.eval, BinOp.eval,
    Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
  · rename_i hlt
    have hlt' : (s₀.loc 0).toNat < 2 ^ 32 := UInt64.lt_iff_toNat_lt.mp hlt
    rw [shl_toNat_of_lt (s₀.loc 0) 32 32 32 rfl rfl hlt', show (32 : Word).toNat = 32 from rfl, hX]
    exact ⟨rfl, Nat.le_mul_of_pos_left _ hpos, Nat.le_refl _⟩
  · rename_i hge
    have hge' : 2 ^ 32 ≤ (s₀.loc 0).toNat := Nat.le_of_not_lt fun h => hge (UInt64.lt_iff_toNat_lt.mpr h)
    rw [h0, show (0 : Word).toNat = 0 from rfl, Nat.pow_zero, Nat.mul_one]
    exact ⟨hX, hge', Nat.zero_le _⟩

theorem nrmStep_spec (c k : Word) (a b : Nat) (hc : c.toNat = 2 ^ a) (hk : k.toNat = b)
    (hab : a + b = 64) (hba : b ≤ a) (X n : Nat) (s₀ : St) (h : NrmInv X (a - b) s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) (nrmStep c k)
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ NrmInv X a s'; ⊤⦄ := by
  unfold nrmStep
  vcgen [step, evalE, evalC, setLoc]
  all_goals (try simp only [NrmInv, St.setLoc_loc, St.setLoc_mem, Cmp.eval, BinOp.eval,
    Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
  · rename_i hlt
    exact nrm_shift _ _ _ X a b hk hab hba h.1 h.2.1 h.2.2 (hc ▸ UInt64.lt_iff_toNat_lt.mp hlt)
  · rename_i hge
    have hge' : 2 ^ a ≤ (s₀.loc 0).toNat :=
      hc ▸ Nat.le_of_not_lt fun h => hge (UInt64.lt_iff_toNat_lt.mpr h)
    exact ⟨h.1, hge', by omega⟩

theorem nrmLast_spec (n : Nat) (s₀ : St) (X : Nat) (h : NrmInv X 62 s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) nrmLast
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ NrmFin X s'; ⊤⦄ := by
  unfold nrmLast
  vcgen [step, evalE, evalC, setLoc]
  all_goals (try simp only [NrmInv, NrmFin, St.setLoc_loc, St.setLoc_mem, Cmp.eval, BinOp.eval,
    reduceIte, decide_eq_true_eq] at *)
  · rename_i hlt
    have hlt' : (s₀.loc 0).toNat < 2 ^ 63 := UInt64.lt_iff_toNat_lt.mp hlt
    obtain ⟨hx, hlo, hs⟩ := h
    have hs1 : (s₀.loc 1 + 1).toNat = (s₀.loc 1).toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : Word).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
    rw [hs1, Nat.pow_succ, ← Nat.mul_assoc, ← hx]
    omega
  · rename_i hge
    have hge' : 2 ^ 63 ≤ (s₀.loc 0).toNat := Nat.le_of_not_lt fun h => hge (UInt64.lt_iff_toNat_lt.mpr h)
    obtain ⟨hx, -, hs⟩ := h
    have := (s₀.loc 0).toNat_lt
    rw [← hx]
    omega

end norm

section specs
variable (p : Prog) (hpn : p.lookup "div_norm" = some divNorm)
  (hp2 : p.lookup "div_2by1" = some div2by1) (hpr : p.lookup "div_recip" = some divRecip)

include hpn in
/-- `div_norm(x)` for `x ≠ 0`: `x · 2^s` is a word with its top bit set, `s ≤ 63`. -/
theorem divNorm_spec (n : Nat) (s₀ : St) (x : Word) (hx : 0 < x.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_norm" [x]
    ⦃fun r s' => s' = s₀ ∧ (r.headD 0).toNat ≤ 63 ∧ x.toNat * sh (r.headD 0).toNat < 2 ^ 64 ∧
      2 ^ 63 ≤ x.toNat * sh (r.headD 0).toNat; ⊤⦄ := by
  rw [invoke_eq _ hpn]
  simp only [callFn, divNorm]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalArgs, nrmFirst_spec p n _ x.toNat,
      nrmStep_spec p 0x1000000000000 16 48 16 rfl rfl rfl (by decide) x.toNat n,
      nrmStep_spec p 0x100000000000000 8 56 8 rfl rfl rfl (by decide) x.toNat n,
      nrmStep_spec p 0x1000000000000000 4 60 4 rfl rfl rfl (by decide) x.toNat n,
      nrmStep_spec p 0x4000000000000000 2 62 2 rfl rfl rfl (by decide) x.toNat n,
      nrmLast_spec p n _ x.toNat]
    all_goals first
      | (apply St.restore; simp_all)
      | (simp only [NrmFin, sh, Sig.retVal, Sig.retOr, List.headD_cons] at *; grind)
      | rfl
      | exact hx

include hp2 in
/-- `div_2by1(u1, u0, d, v)` for `u1 < d`: `(q, r)` with `q d + r = u1 2^64 + u0`, `r < d`. -/
theorem div2by1_spec (n : Nat) (s₀ : St) (u1 u0 d v : Word) (hlt : u1.toNat < d.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_2by1" [u1, u0, d, v]
    ⦃fun r s' => s' = s₀ ∧
      (r.headD 0).toNat * d.toNat + (r.tail.headD 0).toNat = u1.toNat * 2 ^ 64 + u0.toNat ∧
      (r.tail.headD 0).toNat < d.toNat; ⊤⦄ := by
  rw [invoke_eq _ hp2]
  simp only [callFn, div2by1_body]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    simp only [exec, step_snoc]
    unfold d2Tail
    vcgen [ step, evalE, evalC, evalArgs, setLoc, setLocs, d2Est_spec p n,
      d2Down_step_spec p s₀.mem d.toNat (u1.toNat * 2 ^ 64 + u0.toNat) n,
      d2Up_step_spec p s₀.mem d.toNat (u1.toNat * 2 ^ 64 + u0.toNat) n]
    all_goals (try simp only [D2DownInv, D2DownPost, D2UpInv, D2UpPost, St.setLoc_loc, St.setLoc_mem,
      Cmp.eval, Cmp.evalW, BinOp.eval, Nat.reduceEqDiff, reduceIte, decide_eq_true_eq,
      List.headD_cons, List.tail_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ,
      Sig.retVal, Sig.retOr] at *)
    all_goals try (apply St.restore; grind)
    all_goals grind [arena_grind]

include hp2 hpr in
/-- `div_recip(d)` for a normalised `d` changes nothing (its result only steers `div_2by1`'s
speed). -/
theorem divRecip_spec (n : Nat) (s₀ : St) (d : Word) (hd : 2 ^ 63 ≤ d.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_recip" [d]
    ⦃fun _ s' => s' = s₀; ⊤⦄ := by
  rw [invoke_eq _ hpr]
  simp only [callFn, divRecip_body]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    simp only [exec, step_snoc]
    unfold rcpTail
    vcgen [ step, evalE, evalC, evalArgs, setLoc, setLocs, rcpInit_spec p n,
      rcpLoop_step_spec p s₀.mem d n,
      div2by1_spec p hp2 n]
    all_goals (try simp only [RcpInv, RcpPost, St.setLoc_loc, St.setLoc_mem, St.setLocs_cons,
      St.setLocs_nil, BinOp.eval, Nat.reduceEqDiff, reduceIte, Locals.init, List.getD_cons_zero] at *)
    all_goals first
      | (apply St.restore; simp_all)
      | (obtain ⟨-, -, h0⟩ := ‹_ = Sig.normal ∧ _ ∧ (_ : St).loc 0 = d›; rw [h0]; exact recip_hi_lt d hd)
      | simp_all

end specs

end L.Arena
