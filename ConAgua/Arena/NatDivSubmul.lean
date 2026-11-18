module

meta import ConAgua.L.Semantics
import ConAgua.Census.Attr
public import ConAgua.Arena.NatAdd
import ConAgua.Arena.NatDivFacts
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The in-place passes of `nat_divmod` (lane `bigdiv`)

`div_add(r, n, ob, lb)` adds `b` (zero-extended) to the `n` limbs at `r` in place and returns the
carry: the add-back of Knuth's step D6 (con-ron's `pp = sub(&pp, b)` in `dm_correct`).

`div_submul(r, n, ob, q)` subtracts `q · b` from the `n + 1` limbs at `r` in place (`b` the `n`
limbs at `ob`, below `r`), one multiply-accumulate per limb with the product's high word from
`mulhi`, and returns the borrow out of the top limb: Knuth's step D4, con-ron's `mul_u64` and the
comparison of `dm_correct` (`ron/nat.rs`) fused into one pass.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The in-place passes -/

def daddLoop : Stmt := lblk (r, n, ob, lb, i, c, x, y, rt, rb) {
  for i < n {
    x := POOL⦃r + i⦄;
    y := call nat_limb(ob, lb, i);
    POOL⟨rt⟩[rb + i] := x + y + c;
    c := call add_carry(x, y, c)
  }
}

/-- `div_add(r, n, ob, lb)`: `R := R + b` in place (`b` zero-extended); returns the carry. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def divAdd : FunDecl := lfn (r, n, ob, lb) locals (i, c, x, y, rt, rb) {
  rt := ⦃r⦄.tier;
  rb := ⦃r⦄.idx;
  ⟪daddLoop⟫;
  return c
}


section passes
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry) (P0 : Array Word) (C : Nat)

/-- The invariant of `div_add`'s pass. -/
def DAddInv (P0 : Array Word) (C : Nat) (s : St) : Prop :=
  C < 2 ^ 64 ∧ P0.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ C ∧ (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 0).toNat ∧
  s.loc 8 = s.loc 0 >>> 40 ∧ s.loc 9 = s.loc 0 &&& 1099511627775 ∧
  (s.mem.arr64 (tierA POOL (s.loc 8))).size ≤ 2 ^ 40 ∧ (s.loc 8).toNat ≤ 1 ∧ (s.loc 0).toNat < 2 ^ 41 ∧
  (s.loc 4).toNat ≤ (s.loc 1).toNat ∧ (s.loc 5).toNat ≤ 1 ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 4).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 4).toNat + (s.loc 5).toNat * wt (s.loc 4).toNat =
    pv P0 (s.loc 0).toNat (s.loc 4).toNat + xv P0 (s.loc 2).toNat (s.loc 3).toNat (s.loc 4).toNat

def DAddPost (P0 : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  (s'.loc 5).toNat ≤ 1 ∧ Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat + (s'.loc 5).toNat * wt (s₀.loc 1).toNat =
    pv P0 (s₀.loc 0).toNat (s₀.loc 1).toNat + xv P0 (s₀.loc 2).toNat (s₀.loc 3).toNat (s₀.loc 1).toNat

-- the virtual pool's extra `P0.size` conjunct pushes the step past the default budget
set_option maxHeartbeats 2000000 in
include hpl hpc in
theorem daddLoop_spec (n : Nat) (s₀ : St) (h : DAddInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ exec p n daddLoop ⦃fun r s' => DAddPost P0 C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [DAddInv, DAddPost] at h ⊢
    rw [exec, step_while (w := daddLoop) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih, natLimb_spec p hpl n,
      addCarry_spec p hpc n]
    all_goals clear ih
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Cmp.eval, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals grind (splits := 20) [arena_grind, lang_grind, DAddInv, DAddPost]

include hpl hpc in
theorem daddLoop_step_spec (n : Nat) (s₀ : St) (h : DAddInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) daddLoop ⦃fun r s' => DAddPost P0 C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (daddLoop_spec p hpl hpc P0 C (n + 1) s₀ h)

end passes

section passFns
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry)

include hpl hpc in
theorem divAdd_spec (hp : p.lookup "div_add" = some divAdd) (n : Nat) (s₀ : St)
    (r k ob lb : Word) (hs : pcap s₀.mem < 2 ^ 64)
    (hr : r.toNat + k.toNat ≤ pcap s₀.mem) (hb : ob.toNat + lb.toNat ≤ r.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_add" [r, k, ob, lb]
    ⦃fun res s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧ (res.headD 0).toNat ≤ 1 ∧
      Off (vpool s'.mem) (vpool s₀.mem) r.toNat k.toNat ∧
      pv (vpool s'.mem) r.toNat k.toNat + (res.headD 0).toNat * wt k.toNat =
        pv (vpool s₀.mem) r.toNat k.toNat + xv (vpool s₀.mem) ob.toNat lb.toNat k.toNat; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divAdd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc,
        daddLoop_step_spec p hpl hpc (vpool s₀.mem) (pcap s₀.mem) n] <;>
      finish [DAddInv, DAddPost]

end passFns

def dsmLoop : Stmt := lblk (r, n, ob, q, i, c, x, y, lo, rt, rb) {
  for i < n {
    x := POOL⦃r + i⦄;
    y := POOL⦃ob + i⦄;
    lo := q * y + c;
    c := mulhi(q, y) + u64(lo < c);
    POOL⟨rt⟩[rb + i] := x - lo;
    c := c + u64(x < lo)
  }
}

/-- `div_submul(r, n, ob, q)`: `R := R - q · b` in place, `R` the `n + 1` limbs at `r` and `b`
the `n` limbs at `ob`; returns the borrow out of the top limb (con-ron's `mul_u64` and the
comparison `blt(t, p)` of `dm_correct`). -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def divSubmul : FunDecl := lfn (r, n, ob, q) locals (i, c, x, y, lo, rt, rb) {
  rt := ⦃r⦄.tier;
  rb := ⦃r⦄.idx;
  ⟪dsmLoop⟫;
  x := POOL⦃r + n⦄;
  POOL⟨rt⟩[rb + n] := x - c;
  return u64(x < c)
}

/-- One step of `div_submul`'s pass, in the shape of its verification condition: the two loads
read the entry pool (`R`'s limb is not yet written, `b` lies below `R`), the store extends the
written prefix, and `submul_step` is the digit equation. -/
theorem dsm_step_goal (m : Mem) (P0 : Array Word) (r ob q c i rt rb : Word)
    (hrt : rt = r >>> 40) (hrb : rb = r &&& 1099511627775)
    (hT : r.toNat < 2 ^ 41) (hs : (m.arr64 (tierA POOL (r >>> 40))).size ≤ 2 ^ 40)
    (hst : ((r &&& 1099511627775) + i).toNat < (m.arr64 (tierA POOL (r >>> 40))).size)
    (hk : (r &&& 1099511627775).toNat + i.toNat < 2 ^ 40)
    (hlx : ((r + i) &&& 1099511627775).toNat < (m.arr64 (tierA POOL ((r + i) >>> 40))).size)
    (hly : ((ob + i) &&& 1099511627775).toNat < (m.arr64 (tierA POOL ((ob + i) >>> 40))).size)
    (hri : r.toNat + i.toNat < 2 ^ 41) (hob : ob.toNat + i.toNat < r.toNat)
    (hP0 : P0.size = 2 ^ 41) (hoff : Off (vpool m) P0 r.toNat i.toNat)
    (ih : pv (vpool m) r.toNat i.toNat + q.toNat * pv P0 ob.toNat i.toNat =
      pv P0 r.toNat i.toNat + c.toNat * wt i.toNat) :
    pv (vpool (m.set64 (tierA POOL rt) (rb + i)
        ((m.arr64 (tierA POOL ((r + i) >>> 40)))[((r + i) &&& 1099511627775).toNat] -
          (q * (m.arr64 (tierA POOL ((ob + i) >>> 40)))[((ob + i) &&& 1099511627775).toNat] + c))))
        r.toNat (i + 1).toNat +
      q.toNat * pv P0 ob.toNat (i + 1).toNat =
    pv P0 r.toNat (i + 1).toNat +
      (UInt64.ofNat (q.toNat *
          (m.arr64 (tierA POOL ((ob + i) >>> 40)))[((ob + i) &&& 1099511627775).toNat].toNat /
            2 ^ 64) +
        (if q * (m.arr64 (tierA POOL ((ob + i) >>> 40)))[((ob + i) &&& 1099511627775).toNat] + c <
            c then 1 else 0) +
        (if (m.arr64 (tierA POOL ((r + i) >>> 40)))[((r + i) &&& 1099511627775).toNat] <
            q * (m.arr64 (tierA POOL ((ob + i) >>> 40)))[((ob + i) &&& 1099511627775).toNat] + c
          then 1 else 0)).toNat * wt (i + 1).toNat := by
  subst hrt hrb
  have hvs := vpool_size m
  have hi1 : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
  have hri' : (r + i).toNat = r.toNat + i.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hobi : (ob + i).toNat = ob.toNat + i.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have ex : (m.arr64 (tierA POOL ((r + i) >>> 40)))[((r + i) &&& 1099511627775).toNat] =
      P0[r.toNat + i.toNat] := by
    rw [vpool_ld m (r + i) hlx (by omega)]
    simp only [hri']
    exact Off.get _ _ _ _ _ hoff (by omega) (by omega) (by omega)
  have ey : (m.arr64 (tierA POOL ((ob + i) >>> 40)))[((ob + i) &&& 1099511627775).toNat] =
      P0[ob.toNat + i.toNat] := by
    rw [vpool_ld m (ob + i) hly (by omega)]
    simp only [hobi]
    have := hoff (ob.toNat + i.toNat) (Or.inl hob)
    simp only [Array.getElem?_eq_getElem (by omega : ob.toNat + i.toNat < (vpool m).size),
      Array.getElem?_eq_getElem (by omega : ob.toNat + i.toNat < P0.size), Option.some.injEq] at this
    exact this
  rw [ex, ey, vpool_stidx m r i _ hT hst hs hk, hri', hi1,
    pv_set_succ (vpool m) r.toNat i.toNat (i.toNat + 1) (r.toNat + i.toNat) _ rfl rfl (by omega),
    pv_succ P0 ob.toNat i.toNat (i.toNat + 1) (ob.toNat + i.toNat) rfl rfl (by omega),
    pv_succ P0 r.toNat i.toNat (i.toNat + 1) (r.toNat + i.toNat) rfl rfl (by omega),
    wt_succ i.toNat (i.toNat + 1) rfl]
  have hsub := submul_step P0[r.toNat + i.toNat] P0[ob.toNat + i.toNat] q c
  generalize P0[r.toNat + i.toNat] = X at *
  generalize P0[ob.toNat + i.toNat] = Y at *
  generalize (UInt64.ofNat (q.toNat * Y.toNat / 2 ^ 64) + (if q * Y + c < c then 1 else 0) +
    (if X < q * Y + c then 1 else 0)) = c' at *
  generalize pv (vpool m) r.toNat i.toNat = A at *
  generalize pv P0 ob.toNat i.toNat = Bv at *
  generalize pv P0 r.toNat i.toNat = Cv at *
  generalize wt i.toNat = W at *
  generalize (X - (q * Y + c)).toNat = e at *
  have hW := congrArg (· * W) hsub
  clear hsub hT hs hst hk hlx hly hri hob hP0 hoff hvs hi1 hri' hobi ex ey
  generalize q.toNat = Q at *
  generalize c.toNat = C at *
  generalize X.toNat = Xn at *
  generalize Y.toNat = Yn at *
  generalize c'.toNat = Cn at *
  grind

/-- The top limb of `div_submul`: the carry left by the pass is subtracted from it, and the
borrow out is the sign of the result. -/
theorem dsm_top_goal (m : Mem) (P : Array Word) (r ob q c k rt rb r0 k0 : Word)
    (hr0 : r = r0) (hk0 : k = k0) (hrt : rt = r >>> 40) (hrb : rb = r &&& 1099511627775)
    (hT : r.toNat < 2 ^ 41) (hs : (m.arr64 (tierA POOL (r >>> 40))).size ≤ 2 ^ 40)
    (hst : ((r &&& 1099511627775) + k).toNat < (m.arr64 (tierA POOL (r >>> 40))).size)
    (hk : (r &&& 1099511627775).toNat + k.toNat < 2 ^ 40)
    (hlx : ((r0 + k0) &&& 1099511627775).toNat < (m.arr64 (tierA POOL ((r0 + k0) >>> 40))).size)
    (hrk : r.toNat + k.toNat < 2 ^ 41) (hP : P.size = 2 ^ 41) (hoff : Off (vpool m) P r.toNat k.toNat)
    (ih : pv (vpool m) r.toNat k.toNat + q.toNat * pv P ob.toNat k.toNat =
      pv P r.toNat k.toNat + c.toNat * wt k.toNat) :
    pv (vpool (m.set64 (tierA POOL rt) (rb + k0)
        ((m.arr64 (tierA POOL ((r0 + k0) >>> 40)))[((r0 + k0) &&& 1099511627775).toNat] - c)))
        r.toNat (k.toNat + 1) +
      q.toNat * pv P ob.toNat k.toNat =
    pv P r.toNat (k.toNat + 1) +
      (if (m.arr64 (tierA POOL ((r0 + k0) >>> 40)))[((r0 + k0) &&& 1099511627775).toNat] < c
        then (1 : Word) else 0).toNat * wt (k.toNat + 1) := by
  subst hrt hrb hr0 hk0
  have hvs := vpool_size m
  have hrk' : (r + k).toNat = r.toNat + k.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have ex : (m.arr64 (tierA POOL ((r + k) >>> 40)))[((r + k) &&& 1099511627775).toNat] =
      P[r.toNat + k.toNat] := by
    rw [vpool_ld m (r + k) hlx (by omega)]
    simp only [hrk']
    exact Off.get _ _ _ _ _ hoff (by omega) (by omega) (by omega)
  rw [ex, vpool_stidx m r k _ hT hst hs hk, hrk',
    pv_set_succ (vpool m) r.toNat k.toNat (k.toNat + 1) (r.toNat + k.toNat) _ rfl rfl (by omega),
    pv_succ P r.toNat k.toNat (k.toNat + 1) (r.toNat + k.toNat) rfl rfl (by omega),
    wt_succ k.toNat (k.toNat + 1) rfl]
  have hd : (P[r.toNat + k.toNat] - c).toNat + c.toNat =
      P[r.toNat + k.toNat].toNat + (if P[r.toNat + k.toNat] < c then (1 : Word) else 0).toNat * 2 ^ 64 := by
    have hlt : (P[r.toNat + k.toNat] < c) ↔ P[r.toNat + k.toNat].toNat < c.toNat :=
      UInt64.lt_iff_toNat_lt
    have := c.toNat_lt; have := P[r.toNat + k.toNat].toNat_lt
    by_cases h : P[r.toNat + k.toNat] < c <;> simp only [h, ite_true, ite_false] <;>
      simp only [hlt] at h <;> rw [UInt64.toNat_sub] <;> simp <;> omega
  have hW := congrArg (· * wt k.toNat) hd
  generalize P[r.toNat + k.toNat] = X at *
  generalize (if X < c then (1 : Word) else 0).toNat = b at *
  generalize (X - c).toNat = e at *
  generalize pv (vpool m) r.toNat k.toNat = A at *
  generalize pv P ob.toNat k.toNat = Bv at *
  generalize pv P r.toNat k.toNat = Cv at *
  generalize wt k.toNat = W at *
  generalize q.toNat = Q at *
  generalize c.toNat = C at *
  generalize X.toNat = Xn at *
  clear hoff hst hlx hs hk ex
  grind

section submul
variable (p : Prog) (P0 : Array Word) (C : Nat)

/-- The invariant of `div_submul`'s pass over the entry pool `P0`: the first `i` limbs of `R`
minus `q` times the first `i` limbs of `b`, with the carry `c` still to subtract. -/
def DSmInv (P0 : Array Word) (C : Nat) (s : St) : Prop :=
  C < 2 ^ 64 ∧ P0.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ C ∧ (s.loc 2).toNat + (s.loc 1).toNat ≤ (s.loc 0).toNat ∧
  s.loc 9 = s.loc 0 >>> 40 ∧ s.loc 10 = s.loc 0 &&& 1099511627775 ∧
  (s.mem.arr64 (tierA POOL (s.loc 9))).size ≤ 2 ^ 40 ∧ (s.loc 9).toNat ≤ 1 ∧ (s.loc 0).toNat < 2 ^ 41 ∧
  (s.loc 4).toNat ≤ (s.loc 1).toNat ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 4).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 4).toNat +
      (s.loc 3).toNat * pv P0 (s.loc 2).toNat (s.loc 4).toNat =
    pv P0 (s.loc 0).toNat (s.loc 4).toNat + (s.loc 5).toNat * wt (s.loc 4).toNat

def DSmPost (P0 : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
  s'.loc 9 = s₀.loc 9 ∧ s'.loc 10 = s₀.loc 10 ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat +
      (s₀.loc 3).toNat * pv P0 (s₀.loc 2).toNat (s₀.loc 1).toNat =
    pv P0 (s₀.loc 0).toNat (s₀.loc 1).toNat + (s'.loc 5).toNat * wt (s₀.loc 1).toNat

set_option maxHeartbeats 2000000 in
theorem dsmLoop_spec (n : Nat) (s₀ : St) (h : DSmInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ exec p n dsmLoop ⦃fun r s' => DSmPost P0 C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [DSmInv, DSmPost] at h ⊢
    rw [exec, step_while (w := dsmLoop) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [DSmInv, DSmPost] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem,
      Cmp.eval, Cmp.evalW, BinOp.eval, Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals (try and_intros)
    all_goals first
      | (with_reducible apply dsm_step_goal <;> grind)
      | grind (splits := 20) [arena_grind, lang_grind]

theorem dsmLoop_step_spec (n : Nat) (s₀ : St) (h : DSmInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) dsmLoop ⦃fun r s' => DSmPost P0 C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (dsmLoop_spec p P0 C (n + 1) s₀ h)

theorem divSubmul_spec (hp : p.lookup "div_submul" = some divSubmul) (n : Nat) (s₀ : St)
    (r k ob q : Word) (hs : pcap s₀.mem < 2 ^ 64)
    (hr : r.toNat + k.toNat + 1 ≤ pcap s₀.mem) (hb : ob.toNat + k.toNat ≤ r.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_submul" [r, k, ob, q]
    ⦃fun res s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧ (res.headD 0).toNat ≤ 1 ∧
      Off (vpool s'.mem) (vpool s₀.mem) r.toNat (k.toNat + 1) ∧
      pv (vpool s'.mem) r.toNat (k.toNat + 1) + q.toNat * pv (vpool s₀.mem) ob.toNat k.toNat =
        pv (vpool s₀.mem) r.toNat (k.toNat + 1) + (res.headD 0).toNat * wt (k.toNat + 1); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divSubmul]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalArgs, setLoc, setLocs, ld64, st64,
      dsmLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) n]
    all_goals (try simp only [DSmInv, DSmPost] at *)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem,
      List.headD_cons, L.Locals.init_nil, Locals.init_cons_zero,
      Locals.init_cons_succ, Cmp.eval, Cmp.evalW, BinOp.eval, Nat.reduceEqDiff, reduceIte,
      decide_eq_true_eq, Sig.retVal, Sig.retOr] at *)
    all_goals (try subst_vars)
    all_goals (try and_intros)
    all_goals first
      | (grind (splits := 20) [arena_grind, lang_grind]; done)
      | (apply dsm_top_goal <;> grind (splits := 20) [arena_grind, lang_grind])

end submul

end L.Arena
