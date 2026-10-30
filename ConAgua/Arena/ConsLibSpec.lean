module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
public import ConAgua.Arena.ConsLibSpecFind
public import ConAgua.Arena.ConsLibSpecGrow
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section
/-!
# The cons-table library: the specs of the templates, proved once (lane conslib)

A table instance supplies, besides its `ConsSch`, one obligation per fragment (`ConsOK`, in
`ConsLibSpecBase.lean`). From them: `consFindG_spec` (`ConsLibSpecFind.lean`), the in-place growth
block (`ConsLibSpecGrow.lean`), and here

* `consPushG_spec`: `X_push(t, args, j)` appends node `cntC` and grows (`pushMC`, `kgrowIf`);
* `consInternG_spec`: `intern_X(k)` returns the handle and memory of `consInternM C m k`, **the**
  L model of every intern table.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `X_push`: the append -/

/-- The node count of tier `t`. -/
def cntC (C : ConsSch) (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (C.ca + t)

/-- The push's room checks: the handle index, the table's own test. -/
def pushOKC (C : ConsSch) (m : Mem) (t : Word) : Bool :=
  decide (cntC C m t < (134217728 : Word)) && !C.roomM m t (cntC C m t)

/-- Write the words `vs` into array `ra` from word `k + f`. -/
def wrRecK (ra : TieredArray) (k : Word) : Mem → Word → List Word → Mem
  | m, _, [] => m
  | m, f, v :: vs => wrRecK ra k (m.set64 ra (k + f) v) (f + 1) vs

/-- After the record: register node `c` of tier `t` at slot `j` of its table (the value word,
and the key word `q`), count it. -/
def tailM (C : ConsSch) (t j c q : Word) (m : Mem) : Mem :=
  ((m.set64 (tierA C.sa t) (krW C.sa m t + j * 2) (rdW (m.arr64 CTL) SCB * t + c + 1)).set64
    (tierA C.sa t) (krW C.sa m t + j * 2 + 1) q).set64 CTL (C.ca + (t &&& 1)) (c + 1)

/-- **The memory after the append** of node `c` (record `vs`, key word `q`) to tier `t`,
registered at `j`. -/
def pushMC (C : ConsSch) (m : Mem) (t : Word) (vs : List Word) (j c q : Word) : Mem :=
  tailM C t j c q (wrRecK (tierA C.ra t) (c * C.w) m 0 vs)

/-- The derived column's write, `col⟨t⟩[c] := x` (none without a column). -/
def colW (C : ConsSch) (t c x : Word) (m : Mem) : Mem :=
  match C.col with
  | none => m
  | some A => m.set64 (tierA A t) c x

/-- **The memory after the append** with the derived column's word `x`. -/
def pushMX (C : ConsSch) (m : Mem) (t : Word) (vs : List Word) (x j c q : Word) : Mem :=
  colW C t c x (pushMC C m t vs j c q)

theorem pushMX_none {C : ConsSch} (h : C.col = none) (m : Mem) (t : Word) (vs : List Word)
    (x j c q : Word) : pushMX C m t vs x j c q = pushMC C m t vs j c q := by
  simp [pushMX, colW, h]

/-- The growth of tier `t` if node count `c + 1` passes 3/4 of its slot count `g + SN0` (`g` its
count word, read before the push's writes). -/
def growK (C : ConsSch) (t g c : Word) (m : Mem) : Option Mem :=
  if (g + SN0) * 3 < (c + 1) * 4 then kgrowM C.sa (ghC C) t m else some m

/-- **A push's tail**: from the memory `m` after the push's writes, grow tier `t` if node count
`c + 1` passes 3/4 of its slot count in the memory `m₀` before them. -/
def kgrowIf (C : ConsSch) (t : Word) (m₀ m : Mem) (c : Word) : Option Mem :=
  if knW C.sa m₀ t * 3 < (c + 1) * 4 then kgrowM C.sa (ghC C) t m else some m

theorem kgrowIf_growK (C : ConsSch) (t : Word) (m₀ M : Mem) (c : Word) :
    kgrowIf C t m₀ M c = growK C t (rdW (m₀.arr64 (tierA C.sa t)) 0) c M := rfl

/-- The key word a push stores, from its inputs `as` (`cpKey`): the key's hash recomputed (a
fingerprint table without a stored hash), else the key word of the key and the stored hash. -/
def kwP (C : ConsSch) (m : Mem) (as : List Word) : Word :=
  if C.exact then kwQ C as 0
  else if C.nk < C.np then as.getD C.nk 0
  else C.qhM m (as.take C.nk)

theorem kwP_mem (p : Prog) {C : ConsSch} (hO : ConsOK p C) (m m' : Mem) (as : List Word) :
    kwP C m as = kwP C m' as := by
  have hn := hO.push_np
  unfold kwP; split
  · rfl
  · split
    · rfl
    · rename_i hx hlt
      exact hO.qpure (by simpa using hx) (by omega) _ _ _

theorem argsOf_take (base nk np : Nat) (h : nk ≤ np) (s : St) :
    (argsOf base np s).take nk = argsOf base nk s := by
  simp only [argsOf, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem argsOf_getD (base nk np : Nat) (h : nk < np) (s : St) :
    (argsOf base np s).getD nk 0 = s.loc (nk + base) := by
  simp [argsOf, List.getD_eq_getElem?_getD, h]

/-! ### Copying the key words -/

/-- `s` with the words `1 ‥ k` copied to `o ‥ o + k - 1`. -/
def copyS (o : Nat) : Nat → St → St
  | 0, s => s
  | k + 1, s => (copyS o k s).setLoc (o + k) (s.loc (1 + k))

theorem copyS_mem (o k : Nat) (s : St) : (copyS o k s).mem = s.mem := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [copyS, St.setLoc_mem, ih]

theorem copyS_loc (o k : Nat) (s : St) (x : Nat) :
    (copyS o k s).loc x = if o ≤ x ∧ x < o + k then s.loc (x - o + 1) else s.loc x := by
  induction k with
  | zero =>
    simp only [copyS, Nat.add_zero]
    split
    · rename_i h; omega
    · rfl
  | succ k ih =>
    simp only [copyS, St.setLoc_loc, ih]
    by_cases hx : x = o + k
    · subst hx
      simp only [↓reduceIte, show o ≤ o + k ∧ o + k < o + (k + 1) from ⟨by omega, by omega⟩, and_self]
      rw [show o + k - o + 1 = 1 + k by omega]
    · simp only [hx, ↓reduceIte]
      by_cases h1 : o ≤ x ∧ x < o + k
      · simp only [h1, show o ≤ x ∧ x < o + (k + 1) from ⟨h1.1, by omega⟩, and_self, ↓reduceIte]
      · simp only [h1, ↓reduceIte]
        rw [ite_eq_right (fun h => h1 ⟨h.1, by omega⟩)]

theorem seqs_append_one (l : List Stmt) (x t : Stmt) : seqs (l ++ [x]) t = seqs l (.seq x t) := by
  induction l with
  | nil => rfl
  | cons y l ih => simp [seqs, ih]

theorem copies_spec (p : Prog) (n o : Nat) :
    ∀ (k : Nat), k + 1 ≤ o → ∀ (t : Stmt) (s₀ : St) (Q : Sig → St → Prop),
      ⦃fun s => s = copyS o k s₀⦄ step p (exec p n) t ⦃Q; ⊤⦄ →
      ⦃fun s => s = s₀⦄
      step p (exec p n) (seqs ((List.range k).map fun i => .set (o + i) (.var (1 + i))) t) ⦃Q; ⊤⦄
  | 0, _, t, s₀, Q, ht => ht
  | k + 1, hk, t, s₀, Q, ht => by
    rw [List.range_succ, List.map_append, List.map_singleton, seqs_append_one]
    refine copies_spec p n o k (by omega) _ s₀ Q ?_
    refine triple_seq (· = copyS o (k + 1) s₀) ?_ (fun s₁ h₁ => h₁ ▸ ht)
    have e : (copyS o k s₀).loc (1 + k) = s₀.loc (1 + k) := by
      rw [copyS_loc]; rw [ite_eq_right (by omega)]
    vcgen [step, evalE_spec, setLoc]
    rename_i h
    subst h
    simp only [Expr.pval, e]
    rfl

theorem argsOf_copyS (o k : Nat) (_hk : k + 1 ≤ o) (s : St) : argsOf o k (copyS o k s) = argsOf 1 k s := by
  simp only [argsOf]
  apply List.map_congr_left
  intro i hi
  have := List.mem_range.mp hi
  rw [copyS_loc, ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel]

/-! ### The tail -/

/-- The key word the push computes from its state `s` (after the record). -/
abbrev pkw (C : ConsSch) (s : St) : Word := kwP C s.mem (argsOf 1 C.np s)

theorem cpKey_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁⦄
    step p (exec p n) (cpKey C)
    ⦃fun r s' => r = .normal ∧ s'.mem = s₁.mem ∧ KeepLo (gO C + 2) s₁ s' ∧
      s'.loc (gO C + 2) = pkw C s₁; ⊤⦄ := by
  have hn := hO.push_np
  unfold cpKey
  cases hx : C.exact with
  | true =>
    simp only [↓reduceIte]
    vcgen [step, evalE_spec, setLoc]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, kwE_pval, kwP, hx, ↓reduceIte, kwQ] at *)
    all_goals grind [lang_grind, KeepLo, argsOf]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hlt : C.nk < C.np
    · simp only [hlt, ↓reduceIte]
      vcgen [step, evalE_spec, setLoc]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval] at *)
      all_goals (simp only [kwP, hx, Bool.false_eq_true, ↓reduceIte, hlt,
        argsOf_getD 1 C.nk C.np hlt] at *)
      all_goals grind [lang_grind, KeepLo]
    · have he : C.np = C.nk := by omega
      simp only [hlt, ↓reduceIte]
      have hI := hO.ihashG (.inr he)
      refine copies_spec p n (gO C + 14) C.nk (by simp [gO]; omega) _ s₁ _ ?_
      vcgen [step, evalE_spec, setLoc, hI n]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval, argsOf_copyS _ _
        (show C.nk + 1 ≤ gO C + 14 by simp [gO]; omega)] at *)
      all_goals (simp only [kwP, hx, he, Bool.false_eq_true, Nat.lt_irrefl, ↓reduceIte,
        argsOf_take 1 C.nk C.nk (Nat.le_refl _)] at *)
      all_goals grind [lang_grind, KeepLo, copyS_loc, copyS_mem]

theorem cpRest_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₁ : St)
    (hg : s₁.loc (gO C + 1) = rdW (s₁.mem.arr64 (tierA C.sa (s₁.loc 0))) 0) :
    ⦃fun s => s = s₁⦄
    step p (exec p n) (cpRest C)
    ⦃fun r s' => r = .ret [s₁.loc (2 + C.np)] ∧
      growK C (s₁.loc 0) (s₁.loc (gO C + 1)) (s₁.loc (2 + C.np))
        (colW C (s₁.loc 0) (s₁.loc (2 + C.np)) (s₁.loc (4 + C.np))
          (tailM C (s₁.loc 0) (s₁.loc (1 + C.np)) (s₁.loc (2 + C.np)) (pkw C s₁) s₁.mem)) =
        some s'.mem; ⊤⦄ := by
  have hsa := hO.arrs.2.1
  have hgO : 4 + C.np ≤ gO C := by simp only [gO]; omega
  simp only [cpRest, seqs]
  refine triple_seq _ (cpKey_spec p C hO n s₁) (fun s₂ h₂ => ?_)
  obtain ⟨m2, k2, q2⟩ := h₂
  have l0 : s₂.loc 0 = s₁.loc 0 := k2 0 (by omega)
  have l1 : s₂.loc (1 + C.np) = s₁.loc (1 + C.np) := k2 _ (by omega)
  have l2 : s₂.loc (2 + C.np) = s₁.loc (2 + C.np) := k2 _ (by omega)
  have l4 : s₂.loc (4 + C.np) = s₁.loc (4 + C.np) := k2 _ (by omega)
  have lg : s₂.loc (gO C + 1) = s₁.loc (gO C + 1) := k2 _ (by omega)
  cases hc : C.col with
  | none =>
    simp only [cpSlot, cpCnt, cpGrowIf, cpColW, hc, Option.map_none, seqO, mapS, mapE, lvF, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub]
    vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, st64, kgrowBlk_spec p C hO n]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
          Expr.pval, Cond.pval, decide_eq_true_eq, rd64_rdWC, ↓reduceIte, colW, hc] at *)
    all_goals grind [lang_grind, growK, tailM, krW, knW, koW]
  | some A =>
    have hA := hO.colA A hc
    simp only [cpSlot, cpCnt, cpGrowIf, cpColW, hc, Option.map_some, seqO, mapS, mapE, lvF, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub]
    vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, st64, kgrowBlk_spec p C hO n]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
          Expr.pval, Cond.pval, decide_eq_true_eq, rd64_rdWC, ↓reduceIte, colW, hc] at *)
    all_goals grind [lang_grind, growK, tailM, krW, knW, koW]

theorem cpWr_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) :
    ∀ (es : List Expr), (∀ e ∈ es, LocOnly e) → ∀ (f : Nat) (s₁ : St),
    s₁.loc (gO C + 1) = rdW (s₁.mem.arr64 (tierA C.sa (s₁.loc 0))) 0 →
    ⦃fun s => s = s₁⦄
    step p (exec p n) (cpWr C f es (cpRest C))
    ⦃fun r s' => r = .ret [s₁.loc (2 + C.np)] ∧
      growK C (s₁.loc 0) (s₁.loc (gO C + 1)) (s₁.loc (2 + C.np))
        (colW C (s₁.loc 0) (s₁.loc (2 + C.np)) (s₁.loc (4 + C.np))
          (tailM C (s₁.loc 0) (s₁.loc (1 + C.np)) (s₁.loc (2 + C.np)) (pkw C s₁)
            (wrRecK (tierA C.ra (s₁.loc 0)) (s₁.loc (3 + C.np)) s₁.mem (UInt64.ofNat f)
              (es.map (Expr.pval s₁))))) =
        some s'.mem; ⊤⦄ := by
  have hrs := hO.arrs.2.2
  intro es
  induction es with
  | nil =>
    intro _ f s₁ hg
    simp only [cpWr, List.map_nil, wrRecK]
    exact cpRest_spec p C hO n s₁ hg
  | cons e es ih =>
    intro hl f s₁ hg
    have hes : ∀ e' ∈ es, LocOnly e' := fun e' h => hl e' (List.mem_cons_of_mem _ h)
    have hmap : ∀ s : St, s.loc = s₁.loc → es.map (Expr.pval s) = es.map (Expr.pval s₁) :=
      fun s h => List.map_congr_left (fun e' he' => hes e' he' s s₁ h)
    have ef : UInt64.ofNat (f + 1) = UInt64.ofNat f + 1 := by simp [UInt64.ofNat_add]
    have e0 : UInt64.ofNat 0 = 0 := rfl
    have hkw : ∀ (M : Mem), pkw C { mem := M, loc := s₁.loc } = pkw C s₁ := fun M => by
      simp only [pkw, argsOf]; exact kwP_mem p hO _ _ _
    have hsa : ∀ (k v : Word), (s₁.mem.set64 (tierA C.ra (s₁.loc 0)) k v).arr64
        (tierA C.sa (s₁.loc 0)) = s₁.mem.arr64 (tierA C.sa (s₁.loc 0)) :=
      fun k v => Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm (tierA_ne hrs _ _))
    simp only [cpWr]
    by_cases hf0 : f = 0
    · subst hf0
      simp only [↓reduceIte]
      vcgen [step, evalE_spec, st64, ih hes (0 + 1)]
      all_goals (simp only [Expr.pval, List.map_cons, wrRecK, ef, e0,
        UInt64.add_zero, Nat.zero_add, hkw, hsa] at *)
      all_goals (try simp only [hmap _ rfl] at *)
      all_goals grind
    · simp only [hf0, ↓reduceIte]
      vcgen [step, evalE_spec, st64, ih hes (f + 1)]
      all_goals (simp only [BinOp.eval, Expr.pval, List.map_cons,
        wrRecK, ef, hkw, hsa] at *)
      all_goals (try simp only [hmap _ rfl] at *)
      all_goals grind

theorem addnp_eq_gO (C : ConsSch) (k j : Nat) (h : k < 4 + j) : (k + C.np = gO C + j) = False := by
  simp only [gO, eq_iff_iff, iff_false]; omega

theorem gO_eq_addnp (C : ConsSch) (k j : Nat) (h : k < 4 + j) : (gO C + j = k + C.np) = False := by
  simp only [gO, eq_iff_iff, iff_false]; omega

theorem argsOf_setLoc_gO (C : ConsSch) (j : Nat) (s : St) (v : Word) :
    argsOf 1 C.np (s.setLoc (gO C + j) v) = argsOf 1 C.np s :=
  argsOf_setLoc 1 C.np _ (by simp only [gO]; omega) s v

theorem pkw_init (p : Prog) {C : ConsSch} (hO : ConsOK p C) (m m' : Mem) (vs : List Word) :
    pkw C { mem := m, loc := Locals.init vs } = kwP C m' (argsL 1 C.np vs) := by
  simp only [pkw, argsOf_mk]; exact kwP_mem p hO _ _ _

/-- **`X_push(t, args, j)`** appends node `cntC` to tier `t` (record `vsM args`, column word
`colM args`, key word `kwP args`) at slot `j`, then grows the tier if it passed 3/4 load (any
argument list: `t`, the inputs, `j` are its words `0`, `1 ‥ np`, `np + 1`). -/
theorem consPushG_specV (p : Prog) (C : ConsSch) (hO : ConsOK p C)
    (hp : p.lookup C.pname = some (consPushG C)) (n : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) C.pname vs
    ⦃fun r s' => LocEq s' s₀ ∧ pushOKC C s₀.mem (Locals.init vs 0) = true ∧
      r = [cntC C s₀.mem (Locals.init vs 0)] ∧
      kgrowIf C (Locals.init vs 0) s₀.mem (pushMX C s₀.mem (Locals.init vs 0)
        (C.vsM (argsL 1 C.np vs)) (C.colM s₀.mem (argsL 1 C.np vs)) (Locals.init vs (1 + C.np))
        (cntC C s₀.mem (Locals.init vs 0)) (kwP C s₀.mem (argsL 1 C.np vs)))
        (cntC C s₀.mem (Locals.init vs 0)) = some s'.mem; ⊤⦄ := by
  have hV := hO.recs.2
  have hPO := hO.pre
  unfold PreOK at hPO
  rw [invoke_eq _ hp]
  simp only [callFn, consPushG, cpHead, cpMid, seqs, List.map, mapS, mapE, mapC, lvF, L.Notation.blk]
  rcases Classical.em (C.w = 1) with hw | hw <;> simp only [hw, ↓reduceIte, mapS, mapE, lvF] <;>
  cases hpre : C.pre with
  | none =>
    simp only [hpre] at hPO
    simp only [seqO]
    cases n with
    | zero => vcgen [exec] <;> grind
    | succ n =>
      vcgen [exec, step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64,
        cpWr_spec p C hO n C.recW hO.recs.1 0]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
          Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_right_cancel_iff,
          Nat.reduceEqDiff, rd64_rdWC, argsOf_setLoc_add 1 C.np 2 (by decide),
          argsOf_setLoc_add 1 C.np 3 (by decide), zero_ne_add 2 C.np (by decide),
          zero_ne_add 3 C.np (by decide), argsOf_mk,
          addnp_eq_gO C 1 1 (by decide), addnp_eq_gO C 2 1 (by decide), addnp_eq_gO C 3 1 (by decide),
          argsOf_setLoc_gO,
          hO.room_eq, hO.recs.2, ofNat_zero', pushMX, colW, hPO,
          ↓reduceIte, kgrowIf_growK, pushMC, pushOKC,
          cntC, hw, UInt64.mul_one] at *)
      all_goals grind [lang_grind, arena_grind]
  | some b =>
    simp only [hpre] at hPO
    simp only [seqO]
    cases n with
    | zero => vcgen [exec] <;> grind
    | succ n =>
      vcgen [exec, step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, hPO n,
        cpWr_spec p C hO n C.recW hO.recs.1 0]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
          Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_right_cancel_iff,
          Nat.reduceEqDiff, rd64_rdWC, argsOf_setLoc_add 1 C.np 2 (by decide),
          argsOf_setLoc_add 1 C.np 3 (by decide), zero_ne_add 2 C.np (by decide),
          zero_ne_add 3 C.np (by decide), argsOf_mk,
          addnp_eq_gO C 1 1 (by decide), addnp_eq_gO C 2 1 (by decide), addnp_eq_gO C 3 1 (by decide), addnp_eq_gO C 4 1 (by decide),
          argsOf_setLoc_gO,
          hO.room_eq, hO.recs.2, ofNat_zero', pushMX,
          ↓reduceIte, kgrowIf_growK, pushMC, pushOKC,
          cntC, hw, UInt64.mul_one] at *)
      all_goals (obtain ⟨hm1, hk1, hx1⟩ := ‹_ ∧ KeepLo _ _ _ ∧ _›
                 have e0 := hk1 0 (by omega)
                 have e1 := hk1 (1 + C.np) (by omega)
                 have ea := argsOf_keepLo 1 C.np (2 + C.np) (by omega) _ _ hk1
                 simp only [argsOf_mk] at ea e0 e1
                 simp only [e0, ea, hm1, hx1, Nat.add_comm 1 C.np] at *)
      all_goals grind [lang_grind, arena_grind]

/-- `X_push(t, args, j)` at `np` inputs. -/
theorem consPushG_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C)
    (hp : p.lookup C.pname = some (consPushG C)) (n : Nat) (s₀ : St) (t : Word)
    (as : List Word) (has : as.length = C.np) (j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) C.pname (t :: (as ++ [j]))
    ⦃fun r s' => LocEq s' s₀ ∧ pushOKC C s₀.mem t = true ∧ r = [cntC C s₀.mem t] ∧
      kgrowIf C t s₀.mem (pushMX C s₀.mem t (C.vsM as) (C.colM s₀.mem as) j
        (cntC C s₀.mem t) (kwP C s₀.mem as)) (cntC C s₀.mem t) = some s'.mem; ⊤⦄ := by
  have ek := argsL_eq [t] as [j] C.np has
  have ej := init_last t as j C.np has
  simp only [List.length_singleton, List.singleton_append] at ek
  vcgen [consPushG_specV p C hO hp n s₀]
  all_goals simp_all [Locals.init_cons_zero]

/-! ## `intern_X`: the model and the spec -/

/-- The scratch-skip word `intern_X` computes: the table's skip word if the scratch tier is open. -/
def skipC (C : ConsSch) (m : Mem) (ks : List Word) : Word :=
  match C.skipW with
  | some _ => if rdW (m.arr64 CTL) 1 ≠ 0 then C.skM ks else 0
  | none => 0

/-- The push's inputs: the key, and the hash if the record stores it. -/
def pushArgs (C : ConsSch) (ks : List Word) (h : Word) : List Word :=
  ks ++ (if C.nk < C.np then [h] else [])

/-- The append of the key's record to tier `t` at slot `j`, with the handle (base `B`). -/
def pushC (C : ConsSch) (m : Mem) (t B : Word) (ks : List Word) (h j : Word) : Option (Word × Mem) :=
  if pushOKC C m t then
    match kgrowIf C t m (pushMX C m t (C.vsM (pushArgs C ks h)) (C.colM m (pushArgs C ks h))
      j (cntC C m t) (kwP C m (pushArgs C ks h))) (cntC C m t) with
    | some m' => some (B + cntC C m t, m')
    | none => none
  else none

/-- The probe of tier `t` for key `ks` (hash `h`). -/
def probeC (C : ConsSch) (m : Mem) (ks : List Word) (h t : Word) : List Word :=
  cprobeW (m.arr64 (tierA C.sa t)) (C.mtM m (ks ++ [h]) t) C.exact (kwQ C ks h) (baseW m t)
    (knW C.sa m t)
    (krW C.sa m t) (homeW h (knW C.sa m t)) 0

/-- An exact two-word key with a word at or above `2^32`: `intern_X` aborts (`ciChk`; its key
word could not pack the key). -/
def bigK (C : ConsSch) (ks : List Word) : Prop :=
  C.exact = true ∧ C.nk = 2 ∧ (ks.getD 0 0 ||| ks.getD 1 0) >>> 32 ≠ 0

instance (C : ConsSch) (ks : List Word) : Decidable (bigK C ks) := by
  unfold bigK; infer_instance

theorem ciChk_pos {C : ConsSch} (h : C.exact = true ∧ C.nk = 2) :
    ciChk C = [.ite (.cmp .ne (.bin .shr (.bin .or (.var 0) (.var 1)) (.const 32)) (.const 0))
      (.abort (.const R_CAP_KEY)) .skip] := by
  simp only [ciChk, h, and_self, ↓reduceIte]

theorem ciChk_neg {C : ConsSch} (h : ¬ (C.exact = true ∧ C.nk = 2)) : ciChk C = [] := by
  simp only [ciChk, h, ↓reduceIte]

theorem kwP_pushArgs (C : ConsSch) (m : Mem) (ks : List Word) (hks : ks.length = C.nk) :
    kwP C m (pushArgs C ks (C.qhM m ks)) = kwQ C ks (C.qhM m ks) := by
  have ht : (pushArgs C ks (C.qhM m ks)).take C.nk = ks := by
    simp [pushArgs, ← hks]
  cases hx : C.exact
  · simp only [kwP, kwQ, hx, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hlt
      simp [pushArgs, hlt, List.getD_eq_getElem?_getD, hks]
    · rw [ht]
  · simp only [kwP, kwQ, hx, ↓reduceIte]
    split
    · rfl
    · rename_i h1
      simp only [pushArgs, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    · rename_i h0 h1
      have a0 : C.nk ≠ 0 := h0
      have a1 : C.nk ≠ 1 := h1
      simp only [pushArgs, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]

/-- **The L model of `intern_X(k)`**: the handle and the memory after, `none` where the L code
aborts (an oversized exact key, a full table). The persistent probe unless skipped, the scratch probe if the scratch tier is open, the
append to the tier the store is in. -/
def consInternM (C : ConsSch) (m : Mem) (ks : List Word) : Option (Word × Mem) :=
  let h := C.qhM m ks
  let rs₀ := probeC C m ks h 0
  let rs₁ := probeC C m ks h 1
  if bigK C ks then none
  else if skipC C m ks = 0 ∧ rs₀ = [] then none
  else if skipC C m ks = 0 ∧ rs₀.headD 0 ≠ 0 then some (C.P + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (C.S + rs₁.tail.headD 0, m)
    else pushC C m 1 C.S ks h (rs₁.tail.tail.headD 0)
  else pushC C m 0 C.P ks h (rs₀.tail.tail.headD 0)

theorem ConsOK.ihash_spec {p : Prog} {C : ConsSch} (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ C.keyOK s₀.mem (argsOf 0 C.nk s₀)⦄
    step p (exec p n) C.ihash
    ⦃fun r s' => r = .normal ∧ s' = s₀.setLoc C.nk (C.qhM s₀.mem (argsOf 0 C.nk s₀)); ⊤⦄ :=
  hO.ihash n s₀

theorem evalArgs_spec (es : List Expr) (s₀ : St) :
    ⦃fun s => s = s₀⦄ evalArgs es ⦃fun vs s' => s' = s₀ ∧ vs = es.map (Expr.pval s₀); ⊤⦄ := by
  induction es with
  | nil => vcgen [evalArgs] <;> grind
  | cons e es ih => vcgen [evalArgs, evalE_spec e s₀, ih] <;> grind

theorem map_keyArgs (nk : Nat) (extra : List Expr) (s : St) :
    (keyArgs nk extra).map (Expr.pval s) = argsOf 0 nk s ++ extra.map (Expr.pval s) := by
  simp [keyArgs, argsOf, Expr.pval]

theorem argsOf_self (m : Mem) (ks : List Word) (k : Nat) (h : ks.length = k) :
    argsOf 0 k { mem := m, loc := Locals.init ks } = ks := by
  subst h; simpa using argsOf_init [] ks [] m

theorem init_app_past (t : Word) (ks rest : List Word) (k a : Nat) (h : ks.length = k) :
    Locals.init (t :: (ks ++ rest)) (a + 1 + k) = Locals.init rest a := by
  subst h; simpa [Nat.add_assoc, Nat.add_comm] using init_past [t] ks rest a

theorem keyArgs_len (nk : Nat) (extra : List Expr) : (keyArgs nk extra).length = nk + extra.length := by
  simp [keyArgs]

theorem map_hOpt (C : ConsSch) (s : St) :
    (hOpt C).map (Expr.pval s) = if C.nk < C.np then [s.loc C.nk] else [] := by
  unfold hOpt; split <;> simp [Expr.pval]

theorem argsL_push (C : ConsSch) (hn : C.nk ≤ C.np ∧ C.np ≤ 1 + C.nk) (t h j : Word)
    (ks : List Word) (hks : ks.length = C.nk) :
    argsL 1 C.np (t :: (ks ++ ((if C.nk < C.np then [h] else []) ++ [j]))) = pushArgs C ks h := by
  unfold pushArgs
  rw [← List.append_assoc]
  apply argsL_app
  split <;> simp <;> omega

theorem init_push_j (C : ConsSch) (hn : C.nk ≤ C.np ∧ C.np ≤ 1 + C.nk) (t h j : Word)
    (ks : List Word) (hks : ks.length = C.nk) :
    Locals.init (t :: (ks ++ ((if C.nk < C.np then [h] else []) ++ [j]))) (1 + C.np) = j := by
  rw [← List.append_assoc]
  apply init_last
  split <;> simp <;> omega

/-! `intern_X(k)`'s spec, one theorem per arm (skip or not, exact pair or not; elaborated in
parallel). -/

-- the arms' normalising `simp` needs more than the default (heartbeats, not search)
set_option maxHeartbeats 1600000 in
theorem consInternG_sk_x (p : Prog) (C : ConsSch) (hO : ConsOK p C)
    (hpf : p.lookup C.fname = some (consFindG C)) (hpp : p.lookup C.pname = some (consPushG C))
    (fn : FnName)
    (hpi : p.lookup fn = some (consInternG C)) (n : Nat) (s₀ : St) (ks : List Word)
    (hks : ks.length = C.nk) (hk : C.keyOK s₀.mem ks)
    (e : Expr) (hsk : C.skipW = some e) (hb : C.exact = true ∧ C.nk = 2) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) fn ks
    ⦃fun r s' => LocEq s' s₀ ∧ consInternM C s₀.mem ks = some (r.headD 0, s'.mem); ⊤⦄ := by
  have hn := hO.push_np
  have hml := hO.mloc
  rw [invoke_eq _ hpi]
  simp only [callFn]
  rw [consInternG.eq_def]; simp only [hsk]
  rw [ciChk_pos hb]
  all_goals simp only [seqs, List.cons_append, List.nil_append, ciFind, ciHit, ciScr, ciEnd,
    ciPush, ciOpen]
  all_goals cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE_spec, evalC_spec, evalArgs_spec, setLoc, setLocs, hO.ihash_spec n,
      consFindG_specV p C hO.match_ hml hpf n, consPushG_specV p C hO hpp n]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, BinOp.eval, Cmp.eval,
      Expr.pval, Cond.pval, rd64_rdWC, List.map_cons, map_keyArgs,
      List.map_append, map_hOpt] at *)
    all_goals subst_vars
    all_goals (simp only [hO.skips e hsk, Nat.add_right_cancel_iff, Nat.reduceEqDiff,
      argsOf_setLoc 0 C.nk C.nk (by omega), argsOf_setLoc_add 0 C.nk 1 (by omega),
      argsOf_setLoc_add 0 C.nk 2 (by omega), argsOf_setLoc_add 0 C.nk 3 (by omega),
      argsOf_setLoc_add 0 C.nk 4 (by omega), argsOf_setLoc_add 0 C.nk 5 (by omega),
      argsOf_self _ ks C.nk hks, argsL_key _ _ ks C.nk hks, argsL_app _ ks _ C.nk hks,
      Locals.init_cons_zero,
      init_last _ ks _ C.nk hks, init_past2 _ ks _ C.nk 4 hks (by decide),
      argsL_push C hn _ _ _ ks hks, init_push_j C hn _ _ _ ks hks, List.map_nil,
      self_ne_add 1 C.nk (by decide), ↓reduceIte] at *)
    all_goals (simp only [consInternM, skipC, hsk, probeC, pushC, Sig.retVal, List.headD_cons,
      bne_iff_ne, beq_iff_eq, ne_eq, LocEq, Sig.retOr, bigK] at *)
    all_goals (simp_all [Locals.init])

-- the arms' normalising `simp` needs more than the default (heartbeats, not search)
set_option maxHeartbeats 1600000 in
theorem consInternG_sk_nx (p : Prog) (C : ConsSch) (hO : ConsOK p C)
    (hpf : p.lookup C.fname = some (consFindG C)) (hpp : p.lookup C.pname = some (consPushG C))
    (fn : FnName)
    (hpi : p.lookup fn = some (consInternG C)) (n : Nat) (s₀ : St) (ks : List Word)
    (hks : ks.length = C.nk) (hk : C.keyOK s₀.mem ks)
    (e : Expr) (hsk : C.skipW = some e) (hb : ¬ (C.exact = true ∧ C.nk = 2)) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) fn ks
    ⦃fun r s' => LocEq s' s₀ ∧ consInternM C s₀.mem ks = some (r.headD 0, s'.mem); ⊤⦄ := by
  have hn := hO.push_np
  have hml := hO.mloc
  rw [invoke_eq _ hpi]
  simp only [callFn]
  rw [consInternG.eq_def]; simp only [hsk]
  rw [ciChk_neg hb]
  all_goals simp only [seqs, List.cons_append, List.nil_append, ciFind, ciHit, ciScr, ciEnd,
    ciPush, ciOpen]
  all_goals cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE_spec, evalC_spec, evalArgs_spec, setLoc, setLocs, hO.ihash_spec n,
      consFindG_specV p C hO.match_ hml hpf n, consPushG_specV p C hO hpp n]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, BinOp.eval, Cmp.eval,
      Expr.pval, Cond.pval, rd64_rdWC, List.map_cons, map_keyArgs,
      List.map_append, map_hOpt] at *)
    all_goals subst_vars
    all_goals (simp only [hO.skips e hsk, Nat.add_right_cancel_iff, Nat.reduceEqDiff,
      argsOf_setLoc 0 C.nk C.nk (by omega), argsOf_setLoc_add 0 C.nk 1 (by omega),
      argsOf_setLoc_add 0 C.nk 2 (by omega), argsOf_setLoc_add 0 C.nk 3 (by omega),
      argsOf_setLoc_add 0 C.nk 4 (by omega), argsOf_setLoc_add 0 C.nk 5 (by omega),
      argsOf_self _ ks C.nk hks, argsL_key _ _ ks C.nk hks, argsL_app _ ks _ C.nk hks,
      Locals.init_cons_zero,
      init_last _ ks _ C.nk hks, init_past2 _ ks _ C.nk 4 hks (by decide),
      argsL_push C hn _ _ _ ks hks, init_push_j C hn _ _ _ ks hks, List.map_nil,
      self_ne_add 1 C.nk (by decide), ↓reduceIte] at *)
    all_goals (simp only [consInternM, skipC, hsk, probeC, pushC, Sig.retVal, List.headD_cons,
      bne_iff_ne, beq_iff_eq, ne_eq, LocEq, Sig.retOr, bigK] at *)
    all_goals (simp_all [Locals.init])

-- the arms' normalising `simp` needs more than the default (heartbeats, not search)
set_option maxHeartbeats 1600000 in
theorem consInternG_nsk_x (p : Prog) (C : ConsSch) (hO : ConsOK p C)
    (hpf : p.lookup C.fname = some (consFindG C)) (hpp : p.lookup C.pname = some (consPushG C))
    (fn : FnName)
    (hpi : p.lookup fn = some (consInternG C)) (n : Nat) (s₀ : St) (ks : List Word)
    (hks : ks.length = C.nk) (hk : C.keyOK s₀.mem ks)
    (hsk : C.skipW = none) (hb : C.exact = true ∧ C.nk = 2) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) fn ks
    ⦃fun r s' => LocEq s' s₀ ∧ consInternM C s₀.mem ks = some (r.headD 0, s'.mem); ⊤⦄ := by
  have hn := hO.push_np
  have hml := hO.mloc
  rw [invoke_eq _ hpi]
  simp only [callFn]
  rw [consInternG.eq_def]; simp only [hsk]
  rw [ciChk_pos hb]
  all_goals simp only [seqs, List.cons_append, List.nil_append, ciFind, ciHit, ciScr, ciEnd,
    ciPush, ciOpen]
  all_goals cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE_spec, evalC_spec, evalArgs_spec, setLoc, setLocs, hO.ihash_spec n,
      consFindG_specV p C hO.match_ hml hpf n, consPushG_specV p C hO hpp n]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, BinOp.eval, Cmp.eval,
      Expr.pval, Cond.pval, rd64_rdWC, List.map_cons, map_keyArgs,
      List.map_append, map_hOpt] at *)
    all_goals subst_vars
    all_goals (simp only [Nat.add_right_cancel_iff, Nat.reduceEqDiff,
      argsOf_setLoc 0 C.nk C.nk (by omega),
      argsOf_setLoc_add 0 C.nk 2 (by omega), argsOf_setLoc_add 0 C.nk 3 (by omega),
      argsOf_setLoc_add 0 C.nk 4 (by omega), argsOf_setLoc_add 0 C.nk 5 (by omega),
      argsOf_self _ ks C.nk hks, argsL_key _ _ ks C.nk hks, argsL_app _ ks _ C.nk hks,
      Locals.init_cons_zero,
      init_last _ ks _ C.nk hks, init_past2 _ ks _ C.nk 4 hks (by decide),
      argsL_push C hn _ _ _ ks hks, init_push_j C hn _ _ _ ks hks, List.map_nil, ↓reduceIte] at *)
    all_goals (simp only [consInternM, skipC, hsk, probeC, pushC, Sig.retVal, List.headD_cons,
      bne_iff_ne, ne_eq, LocEq, Sig.retOr, bigK] at *)
    all_goals (simp_all [Locals.init])

-- the arms' normalising `simp` needs more than the default (heartbeats, not search)
set_option maxHeartbeats 1600000 in
theorem consInternG_nsk_nx (p : Prog) (C : ConsSch) (hO : ConsOK p C)
    (hpf : p.lookup C.fname = some (consFindG C)) (hpp : p.lookup C.pname = some (consPushG C))
    (fn : FnName)
    (hpi : p.lookup fn = some (consInternG C)) (n : Nat) (s₀ : St) (ks : List Word)
    (hks : ks.length = C.nk) (hk : C.keyOK s₀.mem ks)
    (hsk : C.skipW = none) (hb : ¬ (C.exact = true ∧ C.nk = 2)) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) fn ks
    ⦃fun r s' => LocEq s' s₀ ∧ consInternM C s₀.mem ks = some (r.headD 0, s'.mem); ⊤⦄ := by
  have hn := hO.push_np
  have hml := hO.mloc
  rw [invoke_eq _ hpi]
  simp only [callFn]
  rw [consInternG.eq_def]; simp only [hsk]
  rw [ciChk_neg hb]
  all_goals simp only [seqs, List.cons_append, List.nil_append, ciFind, ciHit, ciScr, ciEnd,
    ciPush, ciOpen]
  all_goals cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE_spec, evalC_spec, evalArgs_spec, setLoc, setLocs, hO.ihash_spec n,
      consFindG_specV p C hO.match_ hml hpf n, consPushG_specV p C hO hpp n]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, BinOp.eval, Cmp.eval,
      Expr.pval, Cond.pval, rd64_rdWC, List.map_cons, map_keyArgs,
      List.map_append, map_hOpt] at *)
    all_goals subst_vars
    all_goals (simp only [Nat.add_right_cancel_iff, Nat.reduceEqDiff,
      argsOf_setLoc 0 C.nk C.nk (by omega),
      argsOf_setLoc_add 0 C.nk 2 (by omega), argsOf_setLoc_add 0 C.nk 3 (by omega),
      argsOf_setLoc_add 0 C.nk 4 (by omega), argsOf_setLoc_add 0 C.nk 5 (by omega),
      argsOf_self _ ks C.nk hks, argsL_key _ _ ks C.nk hks, argsL_app _ ks _ C.nk hks,
      Locals.init_cons_zero,
      init_last _ ks _ C.nk hks, init_past2 _ ks _ C.nk 4 hks (by decide),
      argsL_push C hn _ _ _ ks hks, init_push_j C hn _ _ _ ks hks, List.map_nil, ↓reduceIte] at *)
    all_goals (simp only [consInternM, skipC, hsk, probeC, pushC, Sig.retVal, List.headD_cons,
      bne_iff_ne, ne_eq, LocEq, Sig.retOr, bigK] at *)
    all_goals simp_all

/-- **`intern_X(k)`** returns the handle and the memory of `consInternM`. -/
theorem consInternG_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C)
    (hpf : p.lookup C.fname = some (consFindG C)) (hpp : p.lookup C.pname = some (consPushG C))
    (fn : FnName)
    (hpi : p.lookup fn = some (consInternG C)) (n : Nat) (s₀ : St) (ks : List Word)
    (hks : ks.length = C.nk) (hk : C.keyOK s₀.mem ks) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) fn ks
    ⦃fun r s' => LocEq s' s₀ ∧ consInternM C s₀.mem ks = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases hsk : C.skipW with
  | some e =>
    by_cases hb : C.exact = true ∧ C.nk = 2
    · exact consInternG_sk_x p C hO hpf hpp fn hpi n s₀ ks hks hk e hsk hb
    · exact consInternG_sk_nx p C hO hpf hpp fn hpi n s₀ ks hks hk e hsk hb
  | none =>
    by_cases hb : C.exact = true ∧ C.nk = 2
    · exact consInternG_nsk_x p C hO hpf hpp fn hpi n s₀ ks hks hk hsk hb
    · exact consInternG_nsk_nx p C hO hpf hpp fn hpi n s₀ ks hks hk hsk hb

/-! ## What an interning does to memory -/

/-- **An interning hits** (the memory is unchanged) **or appends** node `cntC` to a tier, with its
growth. -/
theorem consInternM_cases {C : ConsSch} {m m₁ : Mem} {ks : List Word} {r : Word}
    (h : consInternM C m ks = some (r, m₁)) :
    m₁ = m ∨ ∃ t j, t ≤ 1 ∧ pushOKC C m t = true ∧
      kgrowIf C t m (pushMX C m t (C.vsM (pushArgs C ks (C.qhM m ks)))
        (C.colM m (pushArgs C ks (C.qhM m ks))) j (cntC C m t)
        (kwP C m (pushArgs C ks (C.qhM m ks))))
        (cntC C m t) = some m₁ ∧ r = (if t = 0 then C.P else C.S) + cntC C m t := by
  simp only [consInternM, pushC] at h
  repeat' split at h
  all_goals simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals first
    | exact .inl h.2.symm
    | (obtain ⟨rfl, rfl⟩ := h
       first
         | exact .inr ⟨1, _, by decide, ‹_›, ‹_›, by simp⟩
         | exact .inr ⟨0, _, by decide, ‹_›, ‹_›, by simp⟩)

/-! ## The memory outside the slot array -/

/-- **The growth writes only the slot array** (and keeps every size). -/
theorem kgrowIf_frame (C : ConsSch) (t : Word) (m₀ m m' : Mem) (c : Word)
    (h : kgrowIf C t m₀ m c = some m') : GFr (tierA C.sa t) m m' := by
  unfold kgrowIf at h
  split at h
  · exact kgrowM_fr _ _ _ _ _ h
  · cases h; exact GFr.refl _ _

theorem arr64_size_set64 (m : Mem) (a b : TieredArray) (i v : Word) :
    ((m.set64 a i v).arr64 b).size = (m.arr64 b).size := by
  by_cases e : b = a
  · subst e; exact Mem.size_arr64_set64 m b i v
  · rw [Mem.arr64_set64_ne _ _ _ _ _ e]

theorem wrRecK_size (ra : TieredArray) (k : Word) (b : TieredArray) :
    ∀ (vs : List Word) (m : Mem) (f : Word), ((wrRecK ra k m f vs).arr64 b).size = (m.arr64 b).size := by
  intro vs
  induction vs with
  | nil => intro m f; rfl
  | cons v vs ih => intro m f; rw [wrRecK, ih, arr64_size_set64]


/-- The memory after the append of the key's node to tier `t`, outside the slot array: the
record, the count, the column. -/
def pushRec (C : ConsSch) (m : Mem) (t : Word) (ks : List Word) : Mem :=
  colW C t (cntC C m t) (C.colM m (pushArgs C ks (C.qhM m ks)))
    ((wrRecK (tierA C.ra t) (cntC C m t * C.w) m 0 (C.vsM (pushArgs C ks (C.qhM m ks)))).set64
      CTL (C.ca + (t &&& 1)) (cntC C m t + 1))

theorem colW_arr (C : ConsSch) (t c x : Word) (m : Mem) (b : TieredArray)
    (hb : ∀ A, C.col = some A → tierA A t ≠ b) :
    (colW C t c x m).arr64 b = m.arr64 b := by
  unfold colW; split
  · rfl
  · rename_i A hA; exact Mem.arr64_set64_ne _ _ _ _ _ (fun e => hb A hA e.symm)

theorem colW_size (C : ConsSch) (t c x : Word) (m : Mem) (b : TieredArray) :
    ((colW C t c x m).arr64 b).size = (m.arr64 b).size := by
  unfold colW; split
  · rfl
  · exact arr64_size_set64 _ _ _ _ _

theorem arr64_set64_congr {M₁ M₂ : Mem} {a b : TieredArray} (h : M₁.arr64 a = M₂.arr64 a)
    (hb : M₁.arr64 b = M₂.arr64 b) (i v : Word) :
    (M₁.set64 a i v).arr64 b = (M₂.set64 a i v).arr64 b := by
  by_cases e : b = a
  · subst e; simp only [Mem.arr64_set64_same, h]
  · simp only [Mem.arr64_set64_ne _ _ _ _ _ e, hb]

/-- Two memories agree outside array `sa`. -/
def OutSa (sa : TieredArray) (M₁ M₂ : Mem) : Prop := ∀ b, b ≠ sa → M₁.arr64 b = M₂.arr64 b

theorem OutSa.set64 {sa : TieredArray} {M₁ M₂ : Mem} (h : OutSa sa M₁ M₂) {a : TieredArray} (ha : a ≠ sa)
    (i v : Word) : OutSa sa (M₁.set64 a i v) (M₂.set64 a i v) :=
  fun b hb => arr64_set64_congr (h a ha) (h b hb) i v

theorem OutSa.set64_sa {sa : TieredArray} {M₁ M₂ : Mem} (h : OutSa sa M₁ M₂) (i v : Word) :
    OutSa sa (M₁.set64 sa i v) M₂ :=
  fun b hb => (Mem.arr64_set64_ne _ _ _ _ _ hb).trans (h b hb)

theorem OutSa.colW (C : ConsSch) (t : Word) (hcol : ∀ A, C.col = some A → tierA A t ≠ tierA C.sa t)
    {M₁ M₂ : Mem} (h : OutSa (tierA C.sa t) M₁ M₂) (c x : Word) :
    OutSa (tierA C.sa t) (colW C t c x M₁) (colW C t c x M₂) := by
  unfold L.Arena.colW; split
  · exact h
  · rename_i A hA; exact h.set64 (hcol A hA) _ _

/-- **An interning hits** (the memory is unchanged) **or appends** node `cntC` to tier `t`: the
handle is the tier's base plus the count, and outside the slot array the memory is `pushRec`. -/
theorem consInternM_outA {C : ConsSch} {m : Mem} (hsc : C.sa ≠ CTL)
    (hcol : ∀ A, C.col = some A → A ≠ C.sa)
    {ks : List Word} {w : Word} {m' : Mem}
    (h : consInternM C m ks = some (w, m')) :
    m' = m ∨ ∃ t, t ≤ 1 ∧ pushOKC C m t = true ∧ w = (if t = 0 then C.P else C.S) + cntC C m t ∧
      (∀ b, b ≠ tierA C.sa t → m'.arr64 b = (pushRec C m t ks).arr64 b) ∧
      (∀ b, (m'.arr64 b).size = (m.arr64 b).size) := by
  rcases consInternM_cases h with e | ⟨t, j, ht, hok, hg, hr⟩
  · exact .inl e
  refine .inr ⟨t, ht, hok, hr, ?_⟩
  have g := kgrowIf_frame _ _ _ _ _ _ hg
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [g.arr b hb]
    simp only [pushMX, pushMC, tailM, pushRec]
    refine OutSa.colW C t (fun A hA => tierA_ne (hcol A hA) t t)
      (fun b hb => ?_) _ _ b hb
    refine OutSa.set64 (fun b hb => ?_)
      (ne_tierA (Ne.symm hsc) t) _ _ b hb
    exact OutSa.set64_sa (OutSa.set64_sa (fun _ _ => rfl) _ _) _ _ b hb
  · rw [g.size b]
    simp only [pushMX, pushMC, tailM, colW_size, arr64_size_set64, wrRecK_size]



-- The model is opaque outside the library: users read it through the lemmas above and in
-- `ConsLibRel.lean`.
attribute [irreducible] consInternM


end L.Arena
