module

public import ConAgua.Arena.Store
public import ConAgua.Arena.LpCol
meta import ConAgua.Arena.LpCol
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.Store
meta import ConAgua.Arena.ConsLib
import ConAgua.Census.Attr

@[expose] public section

/-!
# The level-list store in L: a variable-length key in the shared pool

The arena's level-list store keeps one node per universe-argument list, a
`Tbl ListNode LsIdx LDer` per tier (`Arena/Store.lean:229`, `LsTables.lists`), keyed by the whole
`List LIdx`. Its L representation keeps the list in the **pool** (`POOL`, the array the `lit`
store keeps its limbs in), one handle word per element, and the record points at the slice:

* **Records.** Word array `LSREC`, three words per node: pool offset, length, and the hash of the
  slice (`lit_hash`, FNV-1a over the words). Tiers interleaved: node `i` of tier `t` at
  `LSREC[6 i + 3 t ..]`. The node count of tier `t` is `CTL[40 + t]`.
* **Cons table.** Word array `LSSLOT`, the same open addressing as `SLOT`.
* **The key.** A slice `(o, l)` below the pool top. Matching is `lit`'s: the hash, the length,
  then `limbs_eq` word for word. The level-list store has no scratch skip
  (`LsStore.find?` probes the persistent tier unconditionally).

The functions: `ls_match(t, i, o, l, h)`, `ls_find(t, o, l, h)`, `ls_push(t, o, l, h, j)` and
`intern_ls(o, l)` (`internLsNode us` for the list whose handle words are the slice). They call
`lit_hash` and `limbs_eq` (`Store.lean`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The level-list records, both tiers interleaved (three words per node). -/
abbrev LSREC : ArrId := 39
/-- The level-list cons-table slots, both tiers interleaved. -/
abbrev LSSLOT : ArrId := 40

/-! ## `ls_match(t, i, o, l, h)` -/

/-- The model of `ls_match`: node `i` of tier `t` has hash `h`, length `l` and the words of the
slice `(o, l)`. -/
def lsmatchW (r p : Array Word) (_t i o l h : Word) : Bool :=
  rdW r (i * 3 + 2) == h && rdW r (i * 3 + 1) == l &&
    eqW p (rdW r (i * 3)) o l 0

/-- con-ron: none — the open-addressing table's own key hash/compare (the twin's `Std.HashMap`) -/
def lsMatch : FunDecl := lfn (t, i, o, l, h) locals (k, e) {
  k := i * 3;
  if LSREC⟨t⟩[k + 2] != h { return 0 };
  if LSREC⟨t⟩[k + 1] != l { return 0 };
  e := call limbs_eq(LSREC⟨t⟩[k], o, l);
  return e
}

section match_
variable (p : Prog) (hpe : p.lookup "limbs_eq" = some limbsEq)
  (hp : p.lookup "ls_match" = some lsMatch)

include hpe hp in
theorem lsMatch_spec (n : Nat) (s₀ : St) (t i o l h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ls_match" [t, i, o, l, h]
    ⦃fun r s' => s' = s₀ ∧
      r = [if lsmatchW (s₀.mem.arr64 (tierA LSREC t)) (tpool s₀.mem) t i o l h then 1 else 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lsMatch]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, limbsEq_spec p hpe n] <;>
      finish [lsmatchW, baseW]

end match_

/-! ## The level-list table as a cons schema (`ConsLib.lean`)

The key is the slice `(o, l)` of level handle words; the record stores the slice and its hash
(`lit_hash`'s: it reads the pool, `litKeyOK`); the match is a call of `ls_match`; the push
writes the derived column `LSHP` (the list's has-param word, `lsOrW`, computed by the prelude
`hpLoopLs`). No scratch skip. -/

/-- The handle word of node `0` of the persistent / scratch level-list tier. -/
def lsP : Word := 0x00000000
def lsS : Word := 0x08000000

/-- The hash of node `i` of tier `t`: its word 2. -/
def lshash (m : Mem) (t i : Word) : Word := rdW (m.arr64 (tierA LSREC t)) (i * 3 + 2)

/-- The push's prelude: the has-param word of the list (`x`, variable 7). -/
def lsPre : Stmt := lblk (t, o, l, h, j, c, k, x, g, ti, ix, u, q, y) {
  x := 0;
  q := 0;
  ⟪hpLoopLs⟫
}

def lsCS : ConsSch where
  ra := LSREC
  sa := LSSLOT
  w := 3
  ca := 40
  P := lsP
  S := lsS
  tag := 0
  fname := "ls_find"
  pname := "ls_push"
  nk := 2
  mloc := 1
  mpre := some (.call [9] "ls_match" [.var 0, .bin .sub (.var 7) (.const 1), .var 1, .var 2, .var 3])
  mc := .cmp .ne (.var 9) (.const 0)
  np := 3
  room := condOf (lblk (t, o, l, h, j, c) {
    if len(LSREC⟨t⟩) < (c + 1) * 3 || len(LSHP⟨t⟩) <= c { skip } })
  recW := [.var 1, .var 2, .var 3]
  ihash := .call [2] "lit_hash" [.var 0, .var 1]
  skipW := none
  xloc := 7
  pre := some lsPre
  col := some LSHP
  mtM m ks t i := lsmatchW (m.arr64 (tierA LSREC t)) (tpool m) t i (ks.getD 0 0) (ks.getD 1 0) (ks.getD 2 0)
  qhM m ks := hashN (tpool m) (ks.getD 0 0).toNat (ks.getD 1 0).toNat
  hsM := lshash
  vsM as := as
  roomM m t c := decide (m.len64 (tierA LSREC t) < (c + 1) * 3) || decide (m.len64 (tierA LSHP t) ≤ c)
  colM m as := lsOrW m (as.getD 0 0) (as.getD 1 0).toNat
  keyOK := litKeyOK

/-! ## `ls_find(t, o, l, h)`, `ls_push(t, o, l, h, j)`, `intern_ls(o, l)`

The arena's `internLsNode us`: the persistent probe, the scratch probe if the scratch tier is
open, the append to the tier the store is in. Handle tag `0` (`LsTag.list`). -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def lsFind : FunDecl := consFindG lsCS

/-- The node count of tier `t` of the level-list table, `CTL[40 + t]`. -/
def lscnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (40 + t)

/-- `ls_push`'s room checks: the handle index, the record array (width 3: by multiplication,
as `letE`'s), the load limit. -/
def lspushOK (m : Mem) (t : Word) : Bool :=
  decide (lscnt m t < (134217728 : Word)) && decide ((lscnt m t + 1) * 3 ≤ m.len64 (tierA LSREC t)) &&
    decide (lscnt m t < m.len64 (tierA LSHP t))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def lsPush : FunDecl := consPushG lsCS

/-- The model of `intern_ls`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def lsinternW (m : Mem) (o l : Word) : Option (Word × Mem) := consInternM lsCS m [o, l]

/-- con-ron: ConRon/Arena/Monad.lean:499-515 ConRon.Arena.internLsNode -/
@[l_impl ConRon.Arena.internLsNode]
def internLs : FunDecl := consInternG lsCS

/-- The level-list store functions, as one `#eval`-able program. -/
def lsProg : Prog :=
  [("lit_hash", litHash), ("limbs_eq", limbsEq), ("ls_match", lsMatch), ("ls_find", lsFind),
   ("ls_push", lsPush), ("intern_ls", internLs)]

/-- A memory with the lists `[5]`, `[7]`, `[5]`, `[5, 7]`, `[]` in the pool (top 5), 8 nodes and
`SN0` slots per tier, the scratch tier closed or open. -/
def lsMem (scratch : Word) : Mem :=
  { words := withTiers <| #[#[5, 7, 5, 5, 7, 0, 0, 0], (Array.replicate 64 0).set! 1 scratch |>.set! 0 5] ++
      Array.replicate 37 #[] ++ #[Array.replicate 48 0, Array.replicate consTestWords 0] ++
      Array.replicate 62 (Array.replicate consTestWords 0) }

/-- Intern each slice in turn; the handles. -/
def internLss (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (o, l) :: xs => match run lsProg 100 "intern_ls" [o, l] m with
    | .ok (r, m') => (internLss m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `[5]`, `[7]`, `[5]` (another copy), `[5, 7]`, `[]`, `[]`: persistent handles 0, 1, 0, 2, 3, 3. -/
#guard internLss (lsMem 0) [(0, 1), (1, 1), (2, 1), (3, 2), (0, 0), (4, 0)] ==
  some [0, 1, 0, 2, 3, 3]

/- With the scratch tier open the nodes go there. -/
#guard internLss (lsMem 1) [(0, 1), (1, 1), (2, 1)] == some [0x08000000, 0x08000001, 0x08000000]

/-! ## The specs: the library's, from the table's obligations -/

section specs
variable (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
  (hpe : p.lookup "limbs_eq" = some limbsEq)

include hph hpe in
theorem lsOK (hpm : p.lookup "ls_match" = some lsMatch) : ConsOK p lsCS where
  match_ := by
    intro n s₀
    simp only [lsCS]
    vcgen [step, evalArgs, evalE, setLocs, lsMatch_spec p hpe hpm n]
    all_goals simp_all [St.setLocs_cons, St.setLocs_nil, Keep1, Cond.pval, Expr.pval, Cmp.eval,
      BinOp.eval, argsOf, List.range_succ, St.setLoc_loc, St.setLoc_mem]
    all_goals first
      | (intro z hz; simp [St.setLoc_loc, hz])
      | exact ite_bneC _
  ihashG := fun h => by simp [lsCS] at h
  qpure := fun _ h => by simp [lsCS] at h
  mloc := fun _ => by simp [lsCS]
  exnk := fun h => by simp [lsCS] at h
  ihash := by
    intro n s₀
    apply triple_pre_and
    rintro ⟨hs, hb⟩
    simp only [lsCS, argsOf, List.range_succ, List.range_zero, List.map, List.nil_append,
      List.cons_append, List.getD_cons_zero, List.getD_cons_succ] at hs hb ⊢
    vcgen [step, evalArgs, evalE, setLocs,
      litHash_spec p hph n s₀ (s₀.loc (0 + 0)) (s₀.loc (1 + 0)) hs hb]
    all_goals simp_all [St.setLocs_cons, St.setLocs_nil, Nat.zero_add]
  pre := by
    unfold PreOK
    simp only [lsCS]
    intro n s₀
    have hL : ∀ s₁ : St, ⦃fun s => s = s₁ ∧ (s₁.loc 12 ≤ s₁.loc 2 ∧
        s₁.loc 7 = lsOrW s₁.mem (s₁.loc 1) (s₁.loc 12).toNat)⦄
        step p (exec p n) hpLoopLs
        ⦃fun r s' => s'.mem = s₁.mem ∧ r = .normal ∧ s'.loc 0 = s₁.loc 0 ∧ s'.loc 1 = s₁.loc 1 ∧
          s'.loc 2 = s₁.loc 2 ∧ s'.loc 3 = s₁.loc 3 ∧ s'.loc 4 = s₁.loc 4 ∧ s'.loc 5 = s₁.loc 5 ∧
          s'.loc 6 = s₁.loc 6 ∧ s'.loc 7 = lsOrW s₁.mem (s₁.loc 1) (s₁.loc 2).toNat; ⊤⦄ :=
      fun s₁ => triple_pre_and fun ⟨hq, hx⟩ => hpLoopLs_step_spec p n s₁ hq hx
    simp only [lsPre, L.Notation.blk]
    vcgen [step, evalE, setLoc, hL]
    all_goals simp_all [St.setLoc_loc, St.setLoc_mem, KeepLo, argsOf, List.range_succ, lsOrW_zero]
    all_goals (intro x hx; obtain ⟨e0, e1, e2, e3, e4, -⟩ := ‹_ ∧ _›
               rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 by omega) with
                 rfl | rfl | rfl | rfl | rfl <;> assumption)
  colA := by simp only [lsCS, Option.some.injEq]; rintro A rfl; decide
  recs := ⟨by
      intro e he s s' h
      simp only [lsCS, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> simp [Expr.pval, h],
    fun s => by simp [lsCS, argsOf, Expr.pval, List.range_succ]⟩
  room := fun s => by
    simp only [lsCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval, BinOp.eval]; rfl
  skips := by intro e he; simp [lsCS] at he
  push_np := by decide
  arrs := by decide
  lt := ⟨by decide, by decide, fun A h => by
    simp only [lsCS, reduceCtorEq, Option.some.injEq] at h; (try subst h); (try decide)⟩

theorem lspushOK_eqC (m : Mem) (t : Word) : lspushOK m t = pushOKC lsCS m t := by
  rw [lspushOK, pushOKC, dec_le_not_lt ((lscnt m t + 1) * 3) (m.len64 (tierA LSREC t)),
    dec_lt_not_le' (lscnt m t) (m.len64 (tierA LSHP t))]
  simp only [lsCS, Bool.not_or, Bool.and_assoc]
  rfl

include hph hpe in
theorem internLs_spec (hpm : p.lookup "ls_match" = some lsMatch)
    (hpf : p.lookup "ls_find" = some lsFind) (hpp : p.lookup "ls_push" = some lsPush)
    (hp : p.lookup "intern_ls" = some internLs) (n : Nat) (s₀ : St) (o l : Word)
    (hs : pcap s₀.mem < 2 ^ 64) (hb : o.toNat + l.toNat ≤ pcap s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_ls" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ lsinternW s₀.mem o l = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p lsCS (lsOK p hph hpe hpm) hpf hpp "intern_ls" hp n s₀ [o, l] rfl ⟨hs, hb⟩

end specs

end L.Arena
