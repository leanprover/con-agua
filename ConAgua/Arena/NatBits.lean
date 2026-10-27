module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatAdd
public import ConAgua.Arena.NatAdd
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# Bitwise `Nat` ops on the limb pool: `land`, `lor`, `xor`

`nat_land`/`nat_lor`/`nat_xor` (con-ron's `land`/`lor`/`xor` and their `*_from` loops,
`ron/nat.rs:658-703`): one pass combining limb `i` of each operand (zero-extended past the
shorter one, con-ron's `limb`, reused from `nat_add` as `nat_limb`), then `nat_trim`. `land`'s
result has `min la lb` limbs (reading only that far, so the loop never needs the zero
extension in practice, but uses the same callee for one shared loop shape); `lor`/`xor` have
`max la lb`. Inputs need not be normalised; the output is.

The model `bv` is `xv` with a combining function instead of a single read: `xv`'s own shape
(`DESIGN.md`, "Loop bodies must be straight-line") carries over, so the loop proof is the house
form, same as `nat_add`'s. Whether packing a limb-wise combine into the pool matches `Nat.land`/
`Nat.lor`/`Nat.xor` on the full value is `NatOpRefine.lean`'s job (deferred, as `Norm`/pv bounds
are for comparison).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- Limb `i` of the slice `(o, l)` as a WORD, `0` past its end (`lv`, but not converted to
`Nat`: `bv` needs to feed it to a word operator `f`). -/
def lvW (p : Array Word) (o l i : Nat) : Word := if i < l then p[o + i]?.getD 0 else 0

theorem lvW_toNat (p : Array Word) (o l i : Nat) : (lvW p o l i).toNat = lv p o l i := by
  simp only [lvW, lv]; split <;> rfl
grind_pattern [arena_grind] lvW_toNat => lvW p o l i, lv p o l i

/-- The value of combining the zero-extended slices `(oa, la)`/`(ob, lb)` limb by limb with `f`,
for the first `k` limbs (`xv` with a second slice and a combinator instead of one read). -/
def bv (f : Word → Word → Word) (p : Array Word) (oa la ob lb : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => bv f p oa la ob lb k + (f (lvW p oa la k) (lvW p ob lb k)).toNat * wt k

theorem bv_succ (f : Word → Word → Word) (p : Array Word) (oa la ob lb k k' : Nat)
    (hk : k' = k + 1) :
    bv f p oa la ob lb k' = bv f p oa la ob lb k + (f (lvW p oa la k) (lvW p ob lb k)).toNat * wt k := by
  subst hk; rfl
grind_pattern [arena_grind] bv_succ => bv f p oa la ob lb k', bv f p oa la ob lb k

@[arena_grind =] theorem bv_zero (f : Word → Word → Word) (p : Array Word) (oa la ob lb : Nat) :
    bv f p oa la ob lb 0 = 0 := rfl

/-- The three word combinators, as NAMED constants (not `(· &&& ·)`-style sections): a lambda
and its point-free `HAnd.hAnd`/… form are eta-equal but not syntactically equal, and `finish`'s
pattern matching saw both forms appear (one from the invariant as written, one from `BinOp.eval`
unfolding the code's own `&`/`|`/`^`) and failed to connect them. One rigid name avoids it. -/
def andF : Word → Word → Word := fun a b => a &&& b
def orF : Word → Word → Word := fun a b => a ||| b
def xorF : Word → Word → Word := fun a b => a ^^^ b

@[arena_grind =] theorem andF_eq (a b : Word) : andF a b = a &&& b := rfl
@[arena_grind =] theorem orF_eq (a b : Word) : orF a b = a ||| b := rfl
@[arena_grind =] theorem xorF_eq (a b : Word) : xorF a b = a ^^^ b := rfl

/-- One pass: limb `i` of the result is the operand limbs (zero-extended) combined bitwise. The
three loops are the same shape (`AddInv`'s, without a carry); only the combining operator
differs, so each needs its own `Stmt` (L has no higher-order operator parameter). -/
def andLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, x, y, pt, pb) {
  while i < n {
    x := call nat_limb(oa, la, i);
    y := call nat_limb(ob, lb, i);
    POOL⟨pt⟩[pb + i] := x & y;
    i += 1
  }
}

def orLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, x, y, pt, pb) {
  while i < n {
    x := call nat_limb(oa, la, i);
    y := call nat_limb(ob, lb, i);
    POOL⟨pt⟩[pb + i] := x | y;
    i += 1
  }
}

def xorLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, x, y, pt, pb) {
  while i < n {
    x := call nat_limb(oa, la, i);
    y := call nat_limb(ob, lb, i);
    POOL⟨pt⟩[pb + i] := x ^ y;
    i += 1
  }
}

/-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult -/
@[l_impl ConRon.Arena.natOpResult]
def natLand : FunDecl := lfn (oa, la, ob, lb) locals (top, n, i, x, y, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  n := la;
  if lb < la { n := lb };
  if len(POOL⟨pt⟩) - pb < n { abort };
  ⟪andLoop⟫;
  n := call nat_trim(top, n);
  CTL.u64[0] := top + n;
  return n
}

/-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult -/
@[l_impl ConRon.Arena.natOpResult]
def natLor : FunDecl := lfn (oa, la, ob, lb) locals (top, n, i, x, y, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  n := la;
  if la < lb { n := lb };
  if len(POOL⟨pt⟩) - pb < n { abort };
  ⟪orLoop⟫;
  n := call nat_trim(top, n);
  CTL.u64[0] := top + n;
  return n
}

/-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult -/
@[l_impl ConRon.Arena.natOpResult]
def natXor : FunDecl := lfn (oa, la, ob, lb) locals (top, n, i, x, y, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  n := la;
  if la < lb { n := lb };
  if len(POOL⟨pt⟩) - pb < n { abort };
  ⟪xorLoop⟫;
  n := call nat_trim(top, n);
  CTL.u64[0] := top + n;
  return n
}

/-- The bitwise `Nat` functions, as one program. -/
def natBitsProg : Prog :=
  natProg ++ [("nat_land", natLand), ("nat_lor", natLor), ("nat_xor", natXor)]

/- `0xF0 land 0x0F = 0` (operands at 0, 1; top at 2, after both). -/
#guard (run natBitsProg 100 "nat_land" [0, 1, 1, 1] { words := #[#[0xF0, 0x0F, 0, 0], #[2]] }).toOption.map (·.1)
  == some [0]
/- `0xF0 lor 0x0F = 0xFF` (same layout). -/
#guard (run natBitsProg 100 "nat_lor" [0, 1, 1, 1] { words := #[#[0xF0, 0x0F, 0, 0], #[2]] }).toOption.map (fun (r, m) => (r, m.words))
  == some ([1], #[#[0xF0, 0x0F, 0xFF, 0], #[3]])
/- `[1, 1] xor [1] = [0, 1]` (top limb survives, bottom cancels; length 2 after trim; operands at
0 (len 2) and 2 (len 1), top at 3). -/
#guard (run natBitsProg 100 "nat_xor" [0, 2, 2, 1] { words := #[#[1, 1, 1, 0, 0], #[3]] }).toOption.map
  (fun (r, m) => (r, m.words)) == some ([2], #[#[1, 1, 1, 0, 1], #[5]])

section bits
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb) (Pg : Array Word) (C : Nat)

/-- The invariant of a bitwise loop: the pool agrees with the entry pool `Pg` below `top`, the
operands lie below `top`, the result fits above it, and the first `i` limbs of the result are
`f`-combined from the (zero-extended) operand limbs — the house shape of `AddInv`, without a
carry. -/
def BitInv (f : Word → Word → Word) (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  POOL < s.mem.words.size ∧ C < 2 ^ 64 ∧ Pg.size = 2 ^ 41 ∧
  pcap s.mem = C ∧ Agree (vpool s.mem) Pg (s.loc 4).toNat ∧
  (s.loc 4).toNat + (s.loc 5).toNat ≤ C ∧
  s.loc 9 = s.loc 4 >>> 40 ∧ s.loc 10 = s.loc 4 &&& 1099511627775 ∧
  (s.loc 10).toNat + (s.loc 5).toNat ≤ (s.mem.arr64 (tierA 0 (s.loc 9))).size ∧
  (s.mem.arr64 (tierA 0 (s.loc 9))).size ≤ 2 ^ 40 ∧ (s.loc 9).toNat ≤ 1 ∧ (s.loc 4).toNat < 2 ^ 41 ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 6).toNat ≤ (s.loc 5).toNat ∧
  pv (vpool s.mem) (s.loc 4).toNat (s.loc 6).toNat =
    bv f Pg (s.loc 0).toNat (s.loc 1).toNat (s.loc 2).toNat (s.loc 3).toNat (s.loc 6).toNat

/-- Shared post of every bitwise loop: the result's first `n` limbs (at `top`) are `f` of the
operands' (zero-extended) first `n` limbs; the frame and sizes are `AddInv`'s. -/
def BitPost (f : Word → Word → Word) (Pg : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧
  pcap s'.mem = C ∧ Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
  s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 9 = s₀.loc 9 ∧ s'.loc 10 = s₀.loc 10 ∧
  pv (vpool s'.mem) (s₀.loc 4).toNat (s₀.loc 5).toNat =
    bv f Pg (s₀.loc 0).toNat (s₀.loc 1).toNat (s₀.loc 2).toNat (s₀.loc 3).toNat (s₀.loc 5).toNat

set_option maxHeartbeats 2000000 in
include hpl in
theorem andLoop_spec (n : Nat) (s₀ : St) (h : BitInv andF Pg C s₀) :
    ⦃fun s => s = s₀⦄ exec p n andLoop ⦃fun r s' => BitPost andF Pg C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [BitInv, BitPost] at h ⊢
    rw [exec, step_while (w := andLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, st64, ih, natLimb_spec p hpl n] <;>
      finish (splits := 20) [BitInv, BitPost]

set_option maxHeartbeats 2000000 in
include hpl in
theorem andLoop_step_spec (n : Nat) (s₀ : St) (h : BitInv andF Pg C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) andLoop ⦃fun r s' => BitPost andF Pg C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (andLoop_spec p hpl Pg C (n + 1) s₀ h)

set_option maxHeartbeats 2000000 in
include hpl in
theorem orLoop_spec (n : Nat) (s₀ : St) (h : BitInv orF Pg C s₀) :
    ⦃fun s => s = s₀⦄ exec p n orLoop ⦃fun r s' => BitPost orF Pg C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [BitInv, BitPost] at h ⊢
    rw [exec, step_while (w := orLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, st64, ih, natLimb_spec p hpl n] <;>
      finish (splits := 20) [BitInv, BitPost]

set_option maxHeartbeats 2000000 in
include hpl in
theorem orLoop_step_spec (n : Nat) (s₀ : St) (h : BitInv orF Pg C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) orLoop ⦃fun r s' => BitPost orF Pg C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (orLoop_spec p hpl Pg C (n + 1) s₀ h)

set_option maxHeartbeats 2000000 in
include hpl in
theorem xorLoop_spec (n : Nat) (s₀ : St) (h : BitInv xorF Pg C s₀) :
    ⦃fun s => s = s₀⦄ exec p n xorLoop ⦃fun r s' => BitPost xorF Pg C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [BitInv, BitPost] at h ⊢
    rw [exec, step_while (w := xorLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, st64, ih, natLimb_spec p hpl n] <;>
      finish (splits := 20) [BitInv, BitPost]

set_option maxHeartbeats 2000000 in
include hpl in
theorem xorLoop_step_spec (n : Nat) (s₀ : St) (h : BitInv xorF Pg C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) xorLoop ⦃fun r s' => BitPost xorF Pg C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (xorLoop_spec p hpl Pg C (n + 1) s₀ h)

end bits

section bitFn
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb) (hpt : p.lookup "nat_trim" = some natTrim)

set_option maxHeartbeats 2000000 in
include hpl hpt in
/-- `nat_land` appends the limb-wise AND of `(oa, la)`/`(ob, lb)` (`min la lb` limbs before
trimming), normalised, at the old top; nothing below the old top changes. -/
theorem natLand_spec (hpa : p.lookup "nat_land" = some natLand) (n : Nat) (s₀ : St)
    (oa la ob lb : Word) (hok : PoolOK s₀.mem) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_land" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        bv andF (vpool s₀.mem) oa.toNat la.toNat ob.toNat lb.toNat
          (if lb.toNat < la.toNat then lb.toNat else la.toNat) ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  have hok₀ := hok
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  -- the `ptop0` disjunct of `PoolOK` is dead here, and `grind` splits on it in every goal
  obtain ⟨hok1, hok2, hok3, hok4, -, hok6⟩ := hok
  replace ha := ha.1
  replace hb := hb.1
  rw [invoke_eq _ hpa]
  simp only [callFn, natLand]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        andLoop_step_spec p hpl (vpool s₀.mem) (pcap s₀.mem) n,
        natTrim_spec p hpt n] <;>
      finish (gen := 40) (ematch := 20) (splits := 30) (instances := 5000) [BitInv, BitPost]

set_option maxHeartbeats 2000000 in
include hpl hpt in
theorem natLor_spec (hpo : p.lookup "nat_lor" = some natLor) (n : Nat) (s₀ : St)
    (oa la ob lb : Word) (hok : PoolOK s₀.mem) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_lor" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        bv orF (vpool s₀.mem) oa.toNat la.toNat ob.toNat lb.toNat
          (if la.toNat < lb.toNat then lb.toNat else la.toNat) ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  have hok₀ := hok
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  -- the `ptop0` disjunct of `PoolOK` is dead here, and `grind` splits on it in every goal
  obtain ⟨hok1, hok2, hok3, hok4, -, hok6⟩ := hok
  replace ha := ha.1
  replace hb := hb.1
  rw [invoke_eq _ hpo]
  simp only [callFn, natLor]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        orLoop_step_spec p hpl (vpool s₀.mem) (pcap s₀.mem) n,
        natTrim_spec p hpt n] <;>
      finish (gen := 40) (ematch := 20) (splits := 30) (instances := 5000) [BitInv, BitPost]

set_option maxHeartbeats 2000000 in
include hpl hpt in
theorem natXor_spec (hpx : p.lookup "nat_xor" = some natXor) (n : Nat) (s₀ : St)
    (oa la ob lb : Word) (hok : PoolOK s₀.mem) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_xor" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        bv xorF (vpool s₀.mem) oa.toNat la.toNat ob.toNat lb.toNat
          (if la.toNat < lb.toNat then lb.toNat else la.toNat) ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  have hok₀ := hok
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  -- the `ptop0` disjunct of `PoolOK` is dead here, and `grind` splits on it in every goal
  obtain ⟨hok1, hok2, hok3, hok4, -, hok6⟩ := hok
  replace ha := ha.1
  replace hb := hb.1
  rw [invoke_eq _ hpx]
  simp only [callFn, natXor]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        xorLoop_step_spec p hpl (vpool s₀.mem) (pcap s₀.mem) n,
        natTrim_spec p hpt n] <;>
      finish (gen := 40) (ematch := 20) (splits := 30) (instances := 5000) [BitInv, BitPost]

end bitFn

end L.Arena
