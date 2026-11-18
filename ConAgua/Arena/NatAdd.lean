module

meta import ConAgua.L.Semantics
meta import ConAgua.Layout
meta import ConAgua.Arena.NatLeaf
public import ConAgua.Arena.NatLeaf
import ConAgua.Arena.NatCmpFacts
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `Nat.add` on the limb pool

`nat_trim` (con-ron's `norm`/`sig_len`, `ron/nat.rs:122,149`) and `nat_add` (`add`/`add_from`,
`ron/nat.rs:235,242`), with `vcgen` specs: the result slice denotes `a + b` and is normalised.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `nat_trim(o, n)`: the length of `(o, n)` without its trailing zero limbs -/

def trimLoop : Stmt := lblk (o, n) {
  while 0 < n && POOL⦃o + n - 1⦄ == 0 { n -= 1 }
}

/-- No `return` inside the loop: the inliner (`Compiler/Inline.lean`) inlines `nat_trim` into its
callers only then, which leaves `nat_add` and the other passes without a call, so the compiler
keeps their locals in registers (lane linleaf).
con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat` -/
@[no_expose] def natTrim : FunDecl := lfn (o, n) {
  ⟪trimLoop⟫;
  return n
}

section trim
variable (p : Prog) (hp : p.lookup "nat_trim" = some natTrim)

theorem trimLoop_spec (n : Nat) (s₀ : St) (hs : pcap s₀.mem < 2 ^ 64)
    (hb : (s₀.loc 0).toNat + (s₀.loc 1).toNat ≤ pcap s₀.mem) :
    ⦃fun s => s = s₀⦄
    exec p n trimLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧
      (s'.loc 1).toNat ≤ (s₀.loc 1).toNat ∧
      pv (vpool s₀.mem) (s₀.loc 0).toNat (s'.loc 1).toNat =
        pv (vpool s₀.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
      Norm (vpool s₀.mem) (s₀.loc 0).toNat (s'.loc 1).toNat; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := trimLoop) rfl]
    sym only [lang_grind, arena_grind] => vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish [Norm]

theorem trimLoop_step_spec (n : Nat) (s₀ : St) (hs : pcap s₀.mem < 2 ^ 64)
    (hb : (s₀.loc 0).toNat + (s₀.loc 1).toNat ≤ pcap s₀.mem) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) trimLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧
      (s'.loc 1).toNat ≤ (s₀.loc 1).toNat ∧
      pv (vpool s₀.mem) (s₀.loc 0).toNat (s'.loc 1).toNat =
        pv (vpool s₀.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
      Norm (vpool s₀.mem) (s₀.loc 0).toNat (s'.loc 1).toNat; ⊤⦄ :=
  Triple.step_exec (trimLoop_spec p (n + 1) s₀ hs hb)

include hp in
theorem natTrim_spec (n : Nat) (s₀ : St) (o l : Word) (hs : pcap s₀.mem < 2 ^ 64)
    (hb : o.toNat + l.toNat ≤ pcap s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_trim" [o, l]
    ⦃fun r s' => s' = s₀ ∧ (r.headD 0).toNat ≤ l.toNat ∧
      pv (vpool s₀.mem) o.toNat (r.headD 0).toNat = pv (vpool s₀.mem) o.toNat l.toNat ∧
      Norm (vpool s₀.mem) o.toNat (r.headD 0).toNat; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natTrim]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, trimLoop_step_spec p n] <;> finish

end trim

/-! ## `nat_add(oa, la, ob, lb)`: append `a + b` to the pool, return its length

The result slice starts at the old top `CTL[0]`. One pass of ripple carry over
`n = max la lb` limbs (a missing limb reads as `0`, con-ron's `limb`), the carry limb, then
`nat_trim`. Inputs need not be normalised; the output is. -/

/-- Limb `i` of the slice `(o, l)`, `0` past its end (con-ron's `limb`, `ron/nat.rs:112`). -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def natLimb : FunDecl := lfn (o, l, i) {
  if i < l { return POOL⦃o + i⦄ };
  return 0
}

/-- `add_n` over the limbs both operands have, `add_1` over the rest of the longer one, the carry
limb at `n`, the longer operand's length. -/
def addCore : Stmt := lblk (oa, la, ob, lb, top, n, c, pt, pb) {
  if la < lb {
    c := call add_n(top, oa, ob, la, 0);
    c := call add_1(top + la, ob + la, lb - la, c)
  } else {
    c := call add_n(top, oa, ob, lb, 0);
    c := call add_1(top + lb, oa + lb, la - lb, c)
  };
  POOL⟨pt⟩[pb + n] := c
}

/-- `add_n` over the limbs both operands have, `add_1` over the rest of the longer one, the carry
limb, `nat_trim`. The passes are leaves (`NatLeaf.lean`).
con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natAdd : FunDecl := lfn (oa, la, ob, lb) locals (top, n, c, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  n := la;
  if la < lb { n := lb };
  if len(POOL⟨pt⟩) - pb <= n { abort };
  ⟪addCore⟫;
  n := call nat_trim(top, n + 1);
  CTL.u64[0] := top + n;
  return n
}

/-- The pool functions, as one `#eval`-able program. -/
def natProg : Prog :=
  [("nat_limb", natLimb), ("nat_trim", natTrim), ("and_n", andN), ("or_n", orN), ("xor_n", xorN),
   ("copy_n", copyN), ("add_n", addN),
   ("add_1", add1), ("nat_add", natAdd)]

/- `(2^128 - 1) + 1 = 2^128`: limbs `[max, max]` at 0 and `[1]` at 2, top 3; the sum is
`[0, 0, 1]` at 3 and the top moves to 6. -/
#guard (run natProg 100 "nat_add" [0, 2, 2, 1]
  (Mem.ofWords [(POOL, #[0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 1, 0, 0, 0, 0, 0]), (CTL, #[3])])).toOption.map
  (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) ==
  some ([3], #[0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 1, 0, 0, 1, 0, 0], #[6])

/- Normalisation: `0 + 0` has length 0 (the carry limb `0` is trimmed); the top stays. -/
#guard (run natProg 100 "nat_add" [0, 0, 0, 0] (Mem.ofWords [(POOL, #[0, 0]), (CTL, #[0])])).toOption.map (·.1)
  == some [0]

/- No room: `abort`. -/
#guard (run natProg 100 "nat_add" [0, 1, 0, 1] (Mem.ofWords [(POOL, #[5, 0]), (CTL, #[1])])).toOption.isNone

section add
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)

include hpl in
theorem natLimb_spec (n : Nat) (s₀ : St) (o l i : Word)
    (hb : o.toNat + l.toNat ≤ pcap s₀.mem) (hs : pcap s₀.mem < 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_limb" [o, l, i]
    ⦃fun r s' => s' = s₀ ∧
      (r.headD 0).toNat = lv (vpool s₀.mem) o.toNat l.toNat i.toNat; ⊤⦄ := by
  rw [invoke_eq _ hpl]
  simp only [callFn, natLimb]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] => vcgen [exec, step, evalE, evalC, evalArgs, ld64] <;> finish

end add

/-- The pool below `T` is kept: `add_n` and `add_1` wrote only at `T` and above, and so does the
carry limb. -/
theorem add_agree (m0 m1 m2 : Mem) (T k l v : Word)
    (hs : pcap m0 < 2 ^ 64) (hc2 : pcap m2 = pcap m0) (hT41 : T.toNat < 2 ^ 41) (hl41 : l.toNat < 2 ^ 41)
    (hk : k.toNat ≤ l.toNat)
    (hbd : ((T &&& 1099511627775) + l).toNat < (m2.arr64 (tierA POOL (T >>> 40))).size)
    (h1 : Off (vpool m1) (vpool m0) T.toNat k.toNat)
    (h2 : Off (vpool m2) (vpool m1) (T + k).toNat (l - k).toNat) :
    Agree (vpool (m2.set64 (tierA POOL (T >>> 40)) ((T &&& 1099511627775) + l) v)) (vpool m0) T.toNat := by
  have hT : T.toNat + l.toNat < 2 ^ 41 :=
    win_lt m2 T l hT41 hl41 (by have := pcap_tier m2 (T >>> 40) (by omega); omega) hbd
  have hsz := pcap_tier m2 (T >>> 40) (by omega)
  have hTk : (T + k).toNat = T.toNat + k.toNat := w_add T k (by omega)
  rw [st_win m2 T l v (by omega) (by omega) (by omega) hbd]
  rw [hTk] at h2
  intro j hj
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by omega)]
  exact (h2 j (Or.inl (by omega))).trans (h1 j (Or.inl hj))

/-- The room check `len - i > n` of a tier array: `i + r ≤ len` for `r ≤ n + 1`. -/
theorem room_le (m : Mem) (a : TieredArray) (i n r : Word) (hin : i.toNat ≤ (m.arr64 a).size)
    (hsz : (m.arr64 a).size < 2 ^ 40) (h : ¬decide (m.len64 a - i ≤ n) = true)
    (hr : r.toNat ≤ (n + 1).toNat) : i.toNat + r.toNat ≤ (m.arr64 a).size := by
  have hs : (m.len64 a).toNat = (m.arr64 a).size := by
    simp only [Mem.len64]; exact Nat.mod_eq_of_lt (by omega)
  have h' : n.toNat < (m.len64 a - i).toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using h
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hs] at h'
  have hn1 : (n + 1).toNat = n.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
  omega

/-- A pool function's last step: it wrote only the pool (`PFrame`) and kept it below the old top
`T`, then moved the top past its `r` result limbs: the pool grew. -/
theorem grows_ctl (m0 m2 : Mem) (T r : Word) (hok : PoolOK m0) (hT0 : m0.top = T)
    (hf : PFrame m0 m2) (ha : Agree (vpool m2) (vpool m0) T.toNat)
    (hroom : (T &&& 1099511627775).toNat + r.toNat ≤ (m0.arr64 (tierA POOL (T >>> 40))).size) :
    Grows m0 (m2.set64 CTL 0 (T + r)) := by
  subst hT0
  exact Grows.write m0 m2 r hok hf ha hroom

theorem vpool_ctl (m : Mem) (w : Word) : vpool (m.set64 CTL 0 w) = vpool m :=
  vpool_set64_ne _ _ _ _ (by decide)

/-- The value of `nat_add`'s result on arrays: `add_n` wrote the `k` common limbs (`P1`), `add_1`
the `l - k` limbs of the longer operand's rest (`P2`), the carry limb goes at `T + l`. -/
theorem add_pv (P0 P1 P2 : Array Word) (T x y k l c1 c2 : Nat) (v : Word) (hv : v.toNat = c2)
    (hP2 : P2.size = 2 ^ 41) (hT : T + l < 2 ^ 41) (hk : k ≤ l) (hx : x + l ≤ T)
    (h1 : Off P1 P0 T k) (h2 : Off P2 P1 (T + k) (l - k))
    (e1 : pv P1 T k + c1 * wt k = pv P0 x k + pv P0 y k + 0)
    (e2 : pv P2 (T + k) (l - k) + c2 * wt (l - k) = pv P1 (x + k) (l - k) + c1) :
    pv (P2.set! (T + l) v) T (l + 1) = pv P0 x l + pv P0 y k := by
  rw [pv_set_succ P2 T l (l + 1) (T + l) v rfl rfl (by omega), hv]
  have a2 := pv_append P2 T k (l - k)
  have a0 := pv_append P0 x k (l - k)
  rw [show k + (l - k) = l by omega] at a2 a0
  have d2 : pv P2 T k = pv P1 T k := Off.pv_disj P2 P1 (T + k) (l - k) T k h2 (Or.inl (by omega))
  have d1 : pv P1 (x + k) (l - k) = pv P0 (x + k) (l - k) :=
    Off.pv_disj P1 P0 T k (x + k) (l - k) h1 (Or.inl (by omega))
  have w := wt_add k (l - k) l (by omega)
  rw [a2, a0, d2, w]
  rw [d1] at e2
  generalize pv P1 T k = A at *
  generalize pv P2 (T + k) (l - k) = B at *
  generalize pv P0 (x + k) (l - k) = D at *
  generalize wt k = W at *
  generalize wt (l - k) = W' at *
  have : W * (B + c2 * W') = W * (D + c1) := by rw [e2]
  grind

/-- `add_pv` in the shape of `addCore`'s goal (the operands `(x, k)` and `(y, l)`: `add_n` over
`k`, `add_1` over the rest of `y`, the carry limb `v` at `T + l`). -/
theorem add_core_goal (m0 m1 m2 : Mem) (T x y k l v c1 c0 n : Word) (hn : n = l) (hc0 : c0 = 0)
    (hs : pcap m0 < 2 ^ 64) (hc2 : pcap m2 = pcap m0) (hT41 : T.toNat < 2 ^ 41) (hl41 : l.toNat < 2 ^ 41)
    (hk : k.toNat ≤ l.toNat) (hy : y.toNat + l.toNat ≤ T.toNat)
    (hbd : ((T &&& 1099511627775) + l).toNat < (m2.arr64 (tierA POOL (T >>> 40))).size)
    (h1 : Off (vpool m1) (vpool m0) T.toNat k.toNat)
    (h2 : Off (vpool m2) (vpool m1) (T + k).toNat (l - k).toNat)
    (e1 : pv (vpool m1) T.toNat k.toNat + c1.toNat * wt k.toNat =
      pv (vpool m0) x.toNat k.toNat + pv (vpool m0) y.toNat k.toNat + c0.toNat)
    (e2 : pv (vpool m2) (T + k).toNat (l - k).toNat + v.toNat * wt (l - k).toNat =
      pv (vpool m1) (y + k).toNat (l - k).toNat + c1.toNat) :
    pv (vpool (m2.set64 (tierA POOL (T >>> 40)) ((T &&& 1099511627775) + n) v)) T.toNat (n.toNat + 1) =
      pv (vpool m0) x.toNat k.toNat + pv (vpool m0) y.toNat l.toNat := by
  subst n
  subst c0
  have hsz := pcap_tier m2 (T >>> 40) (by omega)
  have hT : T.toNat + l.toNat < 2 ^ 41 := win_lt m2 T l hT41 hl41 (by omega) hbd
  have hTk : (T + k).toNat = T.toNat + k.toNat := w_add T k (by omega)
  have hyk : (y + k).toNat = y.toNat + k.toNat := w_add y k (by omega)
  have hlk : (l - k).toNat = l.toNat - k.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hk)
  rw [st_win m2 T l v (by omega) (by omega) (by omega) hbd]
  rw [hTk, hlk] at h2 e2
  rw [hyk] at e2
  simp only [UInt64.toNat_zero] at e1
  rw [Nat.add_comm (pv (vpool m0) x.toNat k.toNat)]
  rw [Nat.add_comm (pv (vpool m0) x.toNat k.toNat)] at e1
  exact add_pv _ _ _ T.toNat y.toNat x.toNat k.toNat l.toNat c1.toNat v.toNat v rfl (vpool_size m2)
    (by omega) hk (by omega) h1 h2 e1 e2

/-- `add_core_goal` with the longer operand first (`addCore`'s `else` branch). -/
theorem add_core_goal2 (m0 m1 m2 : Mem) (T x y k l v c1 c0 n : Word) (hn : n = l) (hc0 : c0 = 0)
    (hs : pcap m0 < 2 ^ 64) (hc2 : pcap m2 = pcap m0) (hT41 : T.toNat < 2 ^ 41) (hl41 : l.toNat < 2 ^ 41)
    (hk : k.toNat ≤ l.toNat) (hy : y.toNat + l.toNat ≤ T.toNat)
    (hbd : ((T &&& 1099511627775) + l).toNat < (m2.arr64 (tierA POOL (T >>> 40))).size)
    (h1 : Off (vpool m1) (vpool m0) T.toNat k.toNat)
    (h2 : Off (vpool m2) (vpool m1) (T + k).toNat (l - k).toNat)
    (e1 : pv (vpool m1) T.toNat k.toNat + c1.toNat * wt k.toNat =
      pv (vpool m0) y.toNat k.toNat + pv (vpool m0) x.toNat k.toNat + c0.toNat)
    (e2 : pv (vpool m2) (T + k).toNat (l - k).toNat + v.toNat * wt (l - k).toNat =
      pv (vpool m1) (y + k).toNat (l - k).toNat + c1.toNat) :
    pv (vpool (m2.set64 (tierA POOL (T >>> 40)) ((T &&& 1099511627775) + n) v)) T.toNat (n.toNat + 1) =
      pv (vpool m0) y.toNat l.toNat + pv (vpool m0) x.toNat k.toNat := by
  subst n
  rw [Nat.add_comm (pv (vpool m0) y.toNat k.toNat) (pv (vpool m0) x.toNat k.toNat)] at e1
  rw [Nat.add_comm (pv (vpool m0) y.toNat l.toNat)]
  exact add_core_goal m0 m1 m2 T x y k l v c1 c0 l rfl hc0 hs hc2 hT41 hl41 hk hy hbd h1 h2 e1 e2

/-- The pool written by `addCore` agrees below `T` with the entry pool. -/
theorem add_core_agree (m0 m1 m2 : Mem) (T k l v n : Word) (hn : n = l)
    (hs : pcap m0 < 2 ^ 64) (hc2 : pcap m2 = pcap m0) (hT41 : T.toNat < 2 ^ 41) (hl41 : l.toNat < 2 ^ 41)
    (hk : k.toNat ≤ l.toNat)
    (hbd : ((T &&& 1099511627775) + l).toNat < (m2.arr64 (tierA POOL (T >>> 40))).size)
    (h1 : Off (vpool m1) (vpool m0) T.toNat k.toNat)
    (h2 : Off (vpool m2) (vpool m1) (T + k).toNat (l - k).toNat) :
    Agree (vpool (m2.set64 (tierA POOL (T >>> 40)) ((T &&& 1099511627775) + n) v)) (vpool m0) T.toNat := by
  subst n
  exact add_agree m0 m1 m2 T k l v hs hc2 hT41 hl41 hk hbd h1 h2

section addCore
variable (p : Prog) (hpn : p.lookup "add_n" = some addN) (hp1 : p.lookup "add_1" = some add1)

/-- `addCore`'s precondition: locals `(oa, la, ob, lb, top, n, c, pt, pb)`, the operands below the
top, `n` the longer length, room for `n + 1` limbs in the top's tier. -/
def AddCorePre (s : St) : Prop :=
  pcap s.mem < 2 ^ 64 ∧ (s.loc 4).toNat < 2 ^ 41 ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 1 < s.loc 3 → s.loc 5 = s.loc 3) ∧ (¬s.loc 1 < s.loc 3 → s.loc 5 = s.loc 1) ∧
  s.loc 7 = s.loc 4 >>> 40 ∧ s.loc 8 = s.loc 4 &&& 1099511627775 ∧
  (s.loc 8).toNat + (s.loc 5).toNat < (s.mem.arr64 (tierA POOL (s.loc 7))).size

def AddCorePost (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ PFrame s₀.mem s'.mem ∧
  pcap s'.mem = pcap s₀.mem ∧ Agree (vpool s'.mem) (vpool s₀.mem) (s₀.loc 4).toNat ∧
  pv (vpool s'.mem) (s₀.loc 4).toNat ((s₀.loc 5).toNat + 1) =
    pv (vpool s₀.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat + pv (vpool s₀.mem) (s₀.loc 2).toNat (s₀.loc 3).toNat

include hpn hp1 in
theorem addCore_spec (n : Nat) (s₀ : St) (h : AddCorePre s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) addCore ⦃fun r s' => AddCorePost s₀ r s'; ⊤⦄ := by
  simp only [AddCorePre, AddCorePost] at h ⊢
  obtain ⟨hs, hT41, ha, hb, hn1, hn2, h7, h8, hroom⟩ := h
  have hsz := pcap_tier s₀.mem (s₀.loc 7) hs
  unfold addCore
  vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, st64,
    addN_spec p hpn n, add1_spec p hp1 n]
  all_goals (try simp only [LocEq] at *)
  all_goals (try simp_all only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    BinOp.eval, Cmp.eval, reduceIte, Nat.reduceEqDiff])
  all_goals split_clear_locs
  all_goals (try and_intros)
  all_goals first
    | (grind (splits := 10) [arena_grind, lang_grind]; done)
    | (with_reducible apply add_core_goal
       case h2 => with_reducible assumption
       case h1 => with_reducible assumption
       case e1 => with_reducible assumption
       case e2 => with_reducible assumption
       all_goals first | rfl | grind)
    | (with_reducible apply add_core_goal2
       case h2 => with_reducible assumption
       case h1 => with_reducible assumption
       case e1 => with_reducible assumption
       case e2 => with_reducible assumption
       all_goals first | rfl | grind)
    | (with_reducible apply add_core_agree
       case h2 => with_reducible assumption
       case h1 => with_reducible assumption
       all_goals grind)

end addCore

/-- `nat_add`'s result: the trimmed length `r` of the `n + 1` limbs `addCore` wrote, read after
the top moved. -/
theorem add_final (m : Mem) (T T' X n n' r R w : Word) (A : Nat) (hX : X = T) (hR : R = r)
    (hT : T' = T) (hn' : n' = n) (hn : n.toNat < 2 ^ 41)
    (et : pv (vpool m) T'.toNat r.toNat = pv (vpool m) T'.toNat (n' + 1).toNat)
    (hc : pv (vpool m) T.toNat (n.toNat + 1) = A) :
    pv (vpool (m.set64 CTL 0 w)) X.toNat R.toNat = A := by
  subst X R T' n'
  have hn1 : (n + 1).toNat = n.toNat + 1 := w_add n 1 (by simp; omega)
  rw [vpool_ctl, et, hn1, hc]

section addFn
variable (p : Prog) (hpn : p.lookup "add_n" = some addN) (hp1 : p.lookup "add_1" = some add1)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpa : p.lookup "nat_add" = some natAdd)

include hpn hp1 hpt hpa in
/-- `nat_add` appends `a + b`, normalised, at the old top and moves the top past it; nothing
below the old top changes, and no other array but `CTL[0]`. -/
theorem natAdd_spec (n : Nat) (s₀ : St) (oa la ob lb : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_add" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat + pv (vpool s₀.mem) ob.toNat lb.toNat ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  have hok₀ := hok
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  have hok2 := hok.ctl; have hok3 := hok.cap; have hok4 := hok.top; have hok6 := hok.inTier
  clear hok
  replace ha := ha.1
  replace hb := hb.1
  have hs : pcap s₀.mem < 2 ^ 64 := by omega
  rw [invoke_eq _ hpa]
  simp only [callFn, natAdd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      addCore_spec p hpn hp1 n, natTrim_spec p hpt n]
    all_goals (try simp only [LocEq, AddCorePre, AddCorePost] at *)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval,
      reduceIte, Nat.reduceEqDiff, UInt64.toNat_zero] at *)
    all_goals split_clear_locs
    all_goals (try and_intros)
    all_goals first
      | (grind (splits := 10) [arena_grind, lang_grind, Mem.top_eq, vpool_ctl, Norm]; done)
      | (with_reducible apply grows_ctl
         case hroom =>
           first
             | grind [Mem.top_eq]
             | (apply room_le
                case hr => with_reducible assumption
                case h => assumption
                all_goals grind [Mem.top_eq])
         all_goals grind [Mem.top_eq, vpool_ctl])
      | (with_reducible apply add_final
         case hc => with_reducible assumption
         case et => with_reducible assumption
         all_goals first | rfl | grind [Mem.top_eq])

end addFn

end L.Arena
