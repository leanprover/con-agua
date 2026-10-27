module

public import ConAgua.Arena.Store
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The name store's `str` table in L: a prefix handle and a string in the shared pool

The arena's name store keeps `str pre s` nodes in a `Tbl StrNode NIdx UInt64` per tier
(`Arena/Store.lean:113`, `NTables.strs`), keyed by the prefix handle and the whole `String`. Its L
representation keeps the string's UTF-8 bytes in the **pool** (`POOL`), one byte per word, and the
record points at the slice, as the level-list store (`LsStore.lean`) does with handle words:

* **Records.** Word array `NSREC`, four words per node: the prefix's handle word, pool offset,
  length, and the hash (`lit_hash` of the slice, then one FNV step with the prefix). Tiers
  interleaved: node `i` of tier `t` at `NSREC[8 i + 4 t ..]`. The node count of tier `t` is
  `CTL[36 + t]`.
* **Cons table.** Word array `NSSLOT`, the same open addressing as `SLOT`.
* **The key.** The prefix word and a slice `(o, l)` below the pool top. Matching: the prefix, the
  hash, the length, then `limbs_eq`. The name store has no scratch skip.

One byte per word keeps the comparison and the hash `lit`'s (`limbs_eq`, `lit_hash`) and the key
a list of words (`PoolSlice.lean`); packing eight bytes per word is a later optimisation.

The functions: `nstr_match(t, i, q, o, l, h)`, `nstr_find(t, q, o, l, h)`,
`nstr_push(t, q, o, l, h, j)` and `intern_nstr(q, o, l)` (`internNNode (.str pre s)` for the
prefix `q` and the string whose bytes the slice holds).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The name `str` records, both tiers interleaved (four words per node). -/
abbrev NSREC : ArrId := 35
/-- The name `str` cons-table slots, both tiers interleaved. -/
abbrev NSSLOT : ArrId := 36

/-! ## `nstr_match(t, i, q, o, l, h)` -/

/-- The model of `nstr_match`: node `i` of tier `t` has prefix `q`, hash `h`, length `l` and the
words of the slice `(o, l)`. -/
def nsmatchW (r p : Array Word) (_t i q o l h : Word) : Bool :=
  rdW r (i * 4) == q && rdW r (i * 4 + 3) == h &&
    rdW r (i * 4 + 2) == l && eqW p (rdW r (i * 4 + 1)) o l 0

/-- con-ron: none — the open-addressing table's own key hash/compare (the twin's `Std.HashMap`) -/
def nsMatch : FunDecl := lfn (t, i, q, o, l, h) locals (k, e) {
  k := i * 4;
  if NSREC⟨t⟩[k] != q { return 0 };
  if NSREC⟨t⟩[k + 3] != h { return 0 };
  if NSREC⟨t⟩[k + 2] != l { return 0 };
  e := call limbs_eq(NSREC⟨t⟩[k + 1], o, l);
  return e
}

section match_
variable (p : Prog) (hpe : p.lookup "limbs_eq" = some limbsEq)
  (hp : p.lookup "nstr_match" = some nsMatch)

include hpe hp in
theorem nsMatch_spec (n : Nat) (s₀ : St) (t i q o l h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nstr_match" [t, i, q, o, l, h]
    ⦃fun r s' => s' = s₀ ∧
      r = [if nsmatchW (s₀.mem.arr64 (tierA NSREC t)) (tpool s₀.mem) t i q o l h then 1 else 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nsMatch]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, limbsEq_spec p hpe n] <;>
      finish [nsmatchW, baseW]

end match_

/-! ## The name `str` table as a cons schema (`ConsLib.lean`)

The key is the prefix handle `q` and the string's slice `(o, l)`; the record stores them and the
hash (`lit_hash`'s of the slice, then one FNV step with `q`; it reads the pool: `nsKeyOK`); the
match is a call of `nstr_match`. No scratch skip. Handle tag `1` (`NTag.str`). -/

/-- The handle word of node `0` of the persistent / scratch name `str` tier. -/
def nsP : Word := 0x10000000
def nsS : Word := 0x18000000

/-- The hash of a name `str` record: the slice's, then one FNV step with the prefix. -/
def nstrHashW (q hs : Word) : Word := (hs ^^^ q) * fnvPrime

/-- The hash of node `i` of tier `t`: its word 3. -/
def nshash (m : Mem) (t i : Word) : Word := rdW (m.arr64 (tierA NSREC t)) (i * 4 + 3)

/-- The slice of a key `[q, o, l]` is in bounds (what `lit_hash`'s spec needs). -/
def nsKeyOK (m : Mem) (ks : List Word) : Prop :=
  pcap m < 2 ^ 64 ∧ (ks.getD 1 0).toNat + (ks.getD 2 0).toNat ≤ pcap m

def nstrCS : ConsSch where
  ra := NSREC
  sa := NSSLOT
  w := 4
  ca := 36
  P := nsP
  S := nsS
  tag := 1
  fname := "nstr_find"
  pname := "nstr_push"
  nk := 3
  mloc := 1
  mpre := some (.call [10] "nstr_match"
    [.var 0, .bin .sub (.var 8) (.const 1), .var 1, .var 2, .var 3, .var 4])
  mc := .cmp .ne (.var 10) (.const 0)
  np := 4
  room := condOf (lblk (t, q, o, l, h, j, c) { if len(NSREC⟨t⟩) < (c + 1) * 4 { skip } })
  recW := [.var 1, .var 2, .var 3, .var 4]
  ihash := lblk (q, o, l, h) {
    h := call lit_hash(o, l);
    h := (h ^ q) * ⟪fnvPrime⟫
  }
  skipW := none
  mtM m ks t i := nsmatchW (m.arr64 (tierA NSREC t)) (tpool m) t i (ks.getD 0 0) (ks.getD 1 0)
    (ks.getD 2 0) (ks.getD 3 0)
  qhM m ks := nstrHashW (ks.getD 0 0) (hashN (tpool m) (ks.getD 1 0).toNat (ks.getD 2 0).toNat)
  hsM := nshash
  vsM as := as
  roomM m t c := decide (m.len64 (tierA NSREC t) < (c + 1) * 4)
  keyOK := nsKeyOK

/-! ## `nstr_find(t, q, o, l, h)`, `nstr_push(t, q, o, l, h, j)`, `intern_nstr(q, o, l)`

The arena's `internNNode (.str pre s)`: the persistent probe, the scratch probe if the scratch
tier is open, the append to the tier the store is in. -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def nsFind : FunDecl := consFindG nstrCS

/-- The node count of tier `t` of the name `str` table, `CTL[36 + t]`. -/
def nscnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (36 + t)

/-- `nstr_push`'s room checks: the handle index, the record array (by multiplication, as
`letE`'s), the load limit. -/
def nspushOK (m : Mem) (t : Word) : Bool :=
  decide (nscnt m t < (134217728 : Word)) && decide ((nscnt m t + 1) * 4 ≤ m.len64 (tierA NSREC t))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def nsPush : FunDecl := consPushG nstrCS

/-- The model of `intern_nstr`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def nsinternW (m : Mem) (q o l : Word) : Option (Word × Mem) := consInternM nstrCS m [q, o, l]

/-- con-ron: ConRon/Arena/Monad.lean:381-397 ConRon.Arena.internNNode -/
@[l_impl ConRon.Arena.internNNode]
def internNStr : FunDecl := consInternG nstrCS

/-- The name `str` store functions, as one `#eval`-able program. -/
def nstrProg : Prog :=
  [("lit_hash", litHash), ("limbs_eq", limbsEq), ("nstr_match", nsMatch), ("nstr_find", nsFind),
   ("nstr_push", nsPush), ("intern_nstr", internNStr)]

/-- A memory with the strings `"a"`, `"b"`, `"a"`, `"ab"` in the pool (top 5), 8 nodes and `SN0`
slots per tier, the scratch tier closed or open. -/
def nstrMem (scratch : Word) : Mem :=
  { words := withTiers <| #[#[97, 98, 97, 97, 98, 0, 0, 0], (Array.replicate 64 0).set! 1 scratch |>.set! 0 5] ++
      Array.replicate 33 #[] ++ #[Array.replicate 64 0, Array.replicate consTestWords 0] }

/-- Intern each `(prefix, offset, length)` in turn; the handles. -/
def internNStrs (m : Mem) : List (Word × Word × Word) → Option (List Word)
  | [] => some []
  | (q, o, l) :: xs => match run nstrProg 100 "intern_nstr" [q, o, l] m with
    | .ok (r, m') => (internNStrs m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `0.a`, `0.b`, `0.a` (another copy), `0.ab`, `1.a`: persistent handles 0, 1, 0, 2, 3. -/
#guard internNStrs (nstrMem 0) [(0, 0, 1), (0, 1, 1), (0, 2, 1), (0, 3, 2), (1, 0, 1)] ==
  some [0x10000000, 0x10000001, 0x10000000, 0x10000002, 0x10000003]

/- With the scratch tier open the nodes go there. -/
#guard internNStrs (nstrMem 1) [(0, 0, 1), (0, 1, 1), (0, 2, 1)] ==
  some [0x18000000, 0x18000001, 0x18000000]

/-! ## The specs: the library's, from the table's obligations -/

section specs
variable (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
  (hpe : p.lookup "limbs_eq" = some limbsEq)

theorem setLoc_twice (s : St) (x : Var) (a b : Word) : (s.setLoc x a).setLoc x b = s.setLoc x b := by
  cases s; simp only [St.setLoc, St.mk.injEq, true_and]; funext y; split <;> rfl

include hph hpe in
theorem nstrOK (hpm : p.lookup "nstr_match" = some nsMatch) : ConsOK p nstrCS where
  match_ := by
    intro n s₀
    simp only [nstrCS]
    vcgen [step, evalArgs, evalE, setLocs, nsMatch_spec p hpe hpm n]
    all_goals simp_all [St.setLocs_cons, St.setLocs_nil, Keep1, Cond.pval, Expr.pval, Cmp.eval,
      BinOp.eval, argsOf, List.range_succ, St.setLoc_loc, St.setLoc_mem]
    all_goals first
      | (intro z hz; simp [St.setLoc_loc, hz])
      | exact ite_bneC _
  ihashG := fun h => by simp [nstrCS] at h
  qpure := fun _ h => by simp [nstrCS] at h
  mloc := fun _ => by simp [nstrCS]
  exnk := fun h => by simp [nstrCS] at h
  ihash := by
    intro n s₀
    apply triple_pre_and
    rintro ⟨hs, hb⟩
    simp only [nstrCS, argsOf, List.range_succ, List.range_zero, List.map, List.nil_append,
      List.cons_append, List.getD_cons_zero, List.getD_cons_succ, L.Notation.blk] at hs hb ⊢
    vcgen [step, evalArgs, evalE, setLoc, setLocs,
      litHash_spec p hph n s₀ (s₀.loc (1 + 0)) (s₀.loc (2 + 0)) hs hb]
    all_goals simp_all [St.setLocs_cons, St.setLocs_nil, St.setLoc_loc, setLoc_twice, BinOp.eval,
      nstrHashW]
  pre := rfl
  colA := by simp [nstrCS]
  recs := ⟨by
      intro e he s s' h
      simp only [nstrCS, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> simp [Expr.pval, h],
    fun s => by simp [nstrCS, argsOf, Expr.pval, List.range_succ]⟩
  room := fun s => by
    simp only [nstrCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval, BinOp.eval]; rfl
  skips := by intro e he; simp [nstrCS] at he
  push_np := by decide
  arrs := by decide
  lt := ⟨by decide, by decide, fun A h => by
    simp only [nstrCS, reduceCtorEq] at h; (try subst h); (try decide)⟩

theorem nspushOK_eqC (m : Mem) (t : Word) : nspushOK m t = pushOKC nstrCS m t := by
  rw [nspushOK, pushOKC, dec_le_not_lt ((nscnt m t + 1) * 4) (m.len64 (tierA NSREC t))]
  rfl

include hph hpe in
theorem internNStr_spec (hpm : p.lookup "nstr_match" = some nsMatch)
    (hpf : p.lookup "nstr_find" = some nsFind) (hpp : p.lookup "nstr_push" = some nsPush)
    (hp : p.lookup "intern_nstr" = some internNStr) (n : Nat) (s₀ : St) (q o l : Word)
    (hs : pcap s₀.mem < 2 ^ 64) (hb : o.toNat + l.toNat ≤ pcap s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_nstr" [q, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ nsinternW s₀.mem q o l = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p nstrCS (nstrOK p hph hpe hpm) hpf hpp "intern_nstr" hp n s₀ [q, o, l] rfl
    ⟨hs, hb⟩

end specs

end L.Arena
