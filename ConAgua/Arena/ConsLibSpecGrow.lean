module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
public import ConAgua.Arena.SlotGrowSpec
public import ConAgua.L.PureEval
public import ConAgua.Arena.ConsLibSpecBase
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The cons-table library specs: the in-place growth block (lane conslib)

`kgrowBlk_spec` and the specs of its loops (zeroing, re-insertion, sweep, top-down rehash).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The growth block

`kgrowBlk C` (`kgrowB` with its variables renamed by `gmap`): its loops' specs, then the block's,
against `SlotGrowSpec.lean`'s models. Variables (`gO` + …): `n2` 0, `n` 1, `H` 2, `Q` 3, `ob` 4,
`nb` 5, `x` 6, `e` 7, `v` 8, `q` 9, `h` 10, `j` 11, `d` 12, `bt` 13, the `ihash` block from 14. -/

theorem gmap_lit (C : ConsSch) (k : Nat) (h : k ≠ 0) : gmap C k = gO C + (k - 1) := by
  simp [gmap, h]

theorem gmap_zero (C : ConsSch) : gmap C 0 = 0 := rfl

theorem zero_eq_addlit (a k : Nat) (h : 0 < k) : (0 = a + k) = False := by
  simp only [eq_iff_iff, iff_false]; omega

theorem addlit_eq_zero (a k : Nat) (h : 0 < k) : (a + k = 0) = False := by
  simp only [eq_iff_iff, iff_false]; omega

theorem self_eq_addlit (a k : Nat) (h : 0 < k) : (a = a + k) = False := by
  simp only [eq_iff_iff, iff_false]; omega

theorem addlit_eq_self (a k : Nat) (h : 0 < k) : (a + k = a) = False := by
  simp only [eq_iff_iff, iff_false]; omega

section zero
variable (sa : TieredArray) (x e : Word) (m : Mem)

theorem kzeroW_done (h : e = 0) : kzeroW sa x e.toNat m = m := by
  subst h; rfl

theorem kzeroW_step (h : ¬ e = 0) :
    kzeroW sa x e.toNat m = kzeroW sa (x + 8) (e - 1).toNat ((((((((m.set64 sa x 0).set64 sa (x + 1) 0).set64 sa
      (x + 2) 0).set64 sa (x + 3) 0).set64 sa (x + 4) 0).set64 sa (x + 5) 0).set64 sa (x + 6) 0).set64
      sa (x + 7) 0) := by
  have h1 : e.toNat = (e - 1).toNat + 1 := by
    have : e.toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.mp (by simpa using h'))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  rw [h1]; rfl

end zero

grind_pattern [arena_grind] kzeroW_done => kzeroW sa x e.toNat m
grind_pattern [arena_grind] kzeroW_step => kzeroW sa x e.toNat m

/-- **The zero loop**, renamed by `f` (its tier at `a`, `x` at `xv`, `e` at `ev`). -/
theorem kzeroLs_spec (p : Prog) (sa : ArrId) (f : Var → Var) (a xv ev : Var) (h0 : f 0 = a)
    (h7 : f 7 = xv) (h8 : f 8 = ev) (hax : a ≠ xv) (hae : a ≠ ev) (hxe : xv ≠ ev) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mapS f (kzeroLs sa))
    ⦃fun r s' => r = .normal ∧ Keep2 xv ev s₀ s' ∧
      s'.mem = kzeroW (tierA sa (s₀.loc a)) (s₀.loc xv) (s₀.loc ev).toNat s₀.mem; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := mapS f (kzeroLs sa)) rfl]
  simp only [mapS, mapE, mapC, h0, h7, h8]
  vcgen [step, evalE_spec, evalC_spec, setLoc, st64, ih]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, bne_iff_ne, ne_eq, ↓reduceIte, hax, hae,
    hxe, Ne.symm hxe] at *)
  all_goals grind [lang_grind, arena_grind, Keep2]

theorem kzeroL_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mapS (gmap C) (kzeroL C))
    ⦃fun r s' => r = .normal ∧ Keep2 (gO C + 6) (gO C + 7) s₀ s' ∧
      s'.mem = kzeroW (tierA C.sa (s₀.loc 0)) (s₀.loc (gO C + 6)) (s₀.loc (gO C + 7)).toNat s₀.mem; ⊤⦄ :=
  kzeroLs_spec p C.sa (gmap C) 0 (gO C + 6) (gO C + 7) rfl (gmap_lit C 7 (by decide))
    (gmap_lit C 8 (by decide)) (show (0 : Nat) ≠ gO C + 6 by simp only [gO]; omega)
    (show (0 : Nat) ≠ gO C + 7 by simp only [gO]; omega) (show gO C + 6 ≠ gO C + 7 by omega) n s₀

theorem kzeroL_step_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kzeroL C))
    ⦃fun r s' => r = .normal ∧ Keep2 (gO C + 6) (gO C + 7) s₀ s' ∧
      s'.mem = kzeroW (tierA C.sa (s₀.loc 0)) (s₀.loc (gO C + 6)) (s₀.loc (gO C + 7)).toNat s₀.mem; ⊤⦄ :=
  Triple.step_exec (kzeroL_spec p C (n + 1) s₀)

theorem mapE_shiftE (f : Var → Var) (o o' : Nat) (hf : ∀ x, f (x + o) = x + o') :
    ∀ e, mapE f (shiftE o e) = shiftE o' e
  | .const _ => rfl
  | .var x => by simp [mapE, shiftE, hf]
  | .bin op a b => by simp [mapE, shiftE, mapE_shiftE f o o' hf a, mapE_shiftE f o o' hf b]
  | .ld8 a i => by simp [mapE, shiftE, mapE_shiftE f o o' hf i]
  | .ld64 a i => by simp [mapE, shiftE, mapE_shiftE f o o' hf i]
  | .len8 _ => rfl
  | .len64 _ => rfl
  | .cmpw c a b => by simp [mapE, shiftE, mapE_shiftE f o o' hf a, mapE_shiftE f o o' hf b]
  | .ldc d i => by simp [mapE, shiftE, mapE_shiftE f o o' hf i]
  | .glob _ => rfl
  | .ld64t a t i => by simp [mapE, shiftE, mapE_shiftE f o o' hf t, mapE_shiftE f o o' hf i]
  | .len64t a t => by simp [mapE, shiftE, mapE_shiftE f o o' hf t]
  | .ld8x8 b i => by simp [mapE, shiftE, mapE_shiftE f o o' hf i]
  | .ld32t a t i => by simp [mapE, shiftE, mapE_shiftE f o o' hf t, mapE_shiftE f o o' hf i]
  | .ld32h a t i _ => by simp [mapE, shiftE, mapE_shiftE f o o' hf t, mapE_shiftE f o o' hf i]

theorem mapW_shiftW (f : Var → Var) (o o' : Nat) (hf : ∀ x, f (x + o) = x + o') :
    ∀ w, mapW f (shiftW o w) = shiftW o' w
  | .plain _ => rfl
  | .tier a t => by simp [mapW, shiftW, mapE_shiftE f o o' hf t]

theorem mapC_shiftC (f : Var → Var) (o o' : Nat) (hf : ∀ x, f (x + o) = x + o') :
    ∀ c, mapC f (shiftC o c) = shiftC o' c
  | .cmp c a b => by simp [mapC, shiftC, mapE_shiftE f o o' hf]
  | .and p q => by simp [mapC, shiftC, mapC_shiftC f o o' hf p, mapC_shiftC f o o' hf q]
  | .or p q => by simp [mapC, shiftC, mapC_shiftC f o o' hf p, mapC_shiftC f o o' hf q]
  | .not p => by simp [mapC, shiftC, mapC_shiftC f o o' hf p]

/-- A renaming after a shift is a shift. -/
theorem mapS_shiftS (f : Var → Var) (o o' : Nat) (hf : ∀ x, f (x + o) = x + o') :
    ∀ s, mapS f (shiftS o s) = shiftS o' s
  | .skip => rfl
  | .set x e => by simp [mapS, shiftS, hf, mapE_shiftE f o o' hf]
  | .st8 a i e => by simp [mapS, shiftS, mapE_shiftE f o o' hf]
  | .st64 a i e => by simp [mapS, shiftS, mapE_shiftE f o o' hf]
  | .seq s t => by simp [mapS, shiftS, mapS_shiftS f o o' hf s, mapS_shiftS f o o' hf t]
  | .ite c s t => by
    simp [mapS, shiftS, mapC_shiftC f o o' hf, mapS_shiftS f o o' hf s, mapS_shiftS f o o' hf t]
  | .while c s => by simp [mapS, shiftS, mapC_shiftC f o o' hf, mapS_shiftS f o o' hf s]
  | .brk => rfl
  | .ret es => by simp [mapS, shiftS, mapE_shiftE f o o' hf]
  | .call xs g args => by simp [mapS, shiftS, mapE_shiftE f o o' hf, hf]
  | .abort e => by simp [mapS, shiftS, mapE_shiftE f o o' hf]
  | .gset g e => by simp [mapS, shiftS, mapE_shiftE f o o' hf]
  | .st64t a t i e => by simp [mapS, shiftS, mapE_shiftE f o o' hf]
  | .copy64 d di s si n => by simp [mapS, shiftS, mapE_shiftE f o o' hf, mapW_shiftW f o o' hf]
  | .copy8w d di s si n => by simp [mapS, shiftS, mapE_shiftE f o o' hf, mapW_shiftW f o o' hf]
  | .scan8 x s i e c => by simp [mapS, shiftS, mapE_shiftE f o o' hf, hf]
  | .st32t a t i e => by simp [mapS, shiftS, mapE_shiftE f o o' hf]

theorem argsOf_zero (o : Nat) (s : St) : argsOf o 0 s = [] := rfl
theorem argsOf_one (o : Nat) (s : St) : argsOf o 1 s = [s.loc o] := by simp [argsOf]
theorem argsOf_two (o : Nat) (s : St) : argsOf o 2 s = [s.loc o, s.loc (o + 1)] := by
  simp [argsOf, List.range_succ, Nat.add_comm]

theorem mapS_seqs (f : Var → Var) (t : Stmt) :
    ∀ l : List Stmt, mapS f (seqs l t) = seqs (l.map (mapS f)) (mapS f t)
  | [] => rfl
  | s :: l => by simp [seqs, mapS, mapS_seqs f t l]

theorem gmap_ihash (C : ConsSch) : mapS (gmap C) (ihashAt C 15) = ihashAt C (gO C + 14) :=
  mapS_shiftS _ 15 (gO C + 14) (fun x => by
    have h1 : ∀ y : Nat, y + 15 ≠ 0 := fun y => by omega
    have h2 : ∀ y : Nat, y + 15 - 1 = y + 14 := fun y => by omega
    simp only [gmap, h1, ite_false]; rw [h2]; ac_rfl) C.ihash

/-- **The growth's hash** (`khashB`, renamed): `h` (`gO + 10`) becomes `ghC` of the key word `q`
(`gO + 9`); the variables below `gO + 14` but `h` are kept. -/
theorem khash_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (khashB C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧
      (∀ z, z < gO C + 14 → z ≠ gO C + 10 → s'.loc z = s₀.loc z) ∧
      (∀ z, gO C + 17 ≤ z → s'.loc z = s₀.loc z) ∧
      s'.loc (gO C + 10) = ghC C s₀.mem (s₀.loc (gO C + 9)); ⊤⦄ := by
  unfold khashB
  cases hx : C.exact with
  | false =>
    simp (disch := decide) only [Bool.false_eq_true, ↓reduceIte, mapS, mapE, gmap_lit, Nat.reduceSub]
    vcgen [step, evalE_spec, setLoc]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval] at *)
    all_goals grind [ghC]
  | true =>
    have hnk := hO.exnk hx
    have hI := hO.ihashG (.inl hx)
    simp only [↓reduceIte, mapS_seqs, mapS, gmap_ihash]
    rcases (by omega : C.nk = 0 ∨ C.nk = 1 ∨ C.nk = 2) with hn | hn | hn
    · simp (disch := decide) only [hn, seqs, List.map, mapE, gmap_lit, Nat.reduceSub,
        Nat.add_zero]
      vcgen [step, evalE_spec, setLoc, hI n]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval, ] at *)
      all_goals (simp only [hn, ghC, hx, ↓reduceIte, unpackK, argsOf_zero] at *)
      all_goals grind
    · simp (disch := decide) only [hn, seqs, List.map, mapS, mapE, gmap_lit, Nat.reduceSub]
      vcgen [step, evalE_spec, setLoc, hI n]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval, ] at *)
      all_goals (simp only [hn, ghC, hx, ↓reduceIte, unpackK, argsOf_one, St.setLoc_loc] at *)
      all_goals grind
    · simp (disch := decide) only [hn, seqs, List.map, mapS, mapE, gmap_lit, Nat.reduceSub]
      vcgen [step, evalE_spec, setLoc, hI n]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval, BinOp.eval, ] at *)
      all_goals (simp only [hn, ghC, hx, ↓reduceIte, unpackK, argsOf_two, St.setLoc_loc] at *)
      all_goals grind

theorem homeW_eq (h n : Word) :
    UInt64.ofNat (((h * golden) ^^^ ((h * golden) >>> 32)).toNat * n.toNat / 2 ^ 64) = homeW h n :=
  rfl

theorem word_toNat_pred (e : Word) (h : ¬ e = 0) : e.toNat = (e - 1).toNat + 1 := by
  have : e.toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.mp (by simpa using h'))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

theorem self_ne_addlit (a k : Nat) (h : 0 < k) : a ≠ a + k := by omega

theorem addlit_ne_addlit (a i j : Nat) (h : i ≠ j) : a + i ≠ a + j := by omega

theorem lt_ne_addlit (z a k : Nat) (h : z < a) : z ≠ a + k := by omega

theorem zero_lt_gO (C : ConsSch) : 0 < gO C := by simp only [gO]; omega

theorem zero_eq_gO (C : ConsSch) : (0 = gO C) = False := by
  simp only [gO, eq_iff_iff, iff_false]; omega

theorem gO_eq_zero (C : ConsSch) : (gO C = 0) = False := by
  simp only [gO, eq_iff_iff, iff_false]; omega

/-- A triple with a fact about the start state in its precondition, used at an equation pre. -/
theorem triple_pre_and' {p : Prog} {k : Stmt → M Sig} {a : Stmt} {s₀ : St} {K : Prop}
    {Q : Sig → St → Prop} (h : ⦃fun s => s = s₀ ∧ K⦄ step p k a ⦃Q; ⊤⦄) (hK : K) :
    ⦃fun s => s = s₀⦄ step p k a ⦃Q; ⊤⦄ :=
  ⟨fun s hs => h.le_wp s ⟨hs, hK⟩⟩

/-- Sequential composition, with the intermediate assertion `R`. -/
theorem triple_seq {p : Prog} {k : Stmt → M Sig} {a b : Stmt} {s₀ : St} {Q : Sig → St → Prop}
    (R : St → Prop)
    (ha : ⦃fun s => s = s₀⦄ step p k a ⦃fun r s => r = .normal ∧ R s; ⊤⦄)
    (hb : ∀ s₁, R s₁ → ⦃fun s => s = s₁⦄ step p k b ⦃Q; ⊤⦄) :
    ⦃fun s => s = s₀⦄ step p k (.seq a b) ⦃Q; ⊤⦄ := by
  vcgen [step, ha, hb] <;> assumption

/-- A weaker postcondition. -/
theorem triple_weaken {p : Prog} {k : Stmt → M Sig} {a : Stmt} {s₀ : St} {Q Q' : Sig → St → Prop}
    (ha : ⦃fun s => s = s₀⦄ step p k a ⦃Q; ⊤⦄) (h : ∀ r s, Q r s → Q' r s) :
    ⦃fun s => s = s₀⦄ step p k a ⦃Q'; ⊤⦄ := by
  vcgen [ha] <;> grind

/-- Every local but `x`, `y` and `z` is kept. -/
def Keep3 (x y z : Var) (s s' : St) : Prop := ∀ w, w ≠ x → w ≠ y → w ≠ z → s'.loc w = s.loc w

theorem Keep3.loc {x y z : Var} {s s' : St} (h : Keep3 x y z s s') (w : Var) (hx : w ≠ x)
    (hy : w ≠ y) (hz : w ≠ z) : s'.loc w = s.loc w := h w hx hy hz

grind_pattern [lang_grind] Keep3.loc => Keep3 x y z s s', s'.loc w

/-! ### The re-insertion's probe -/

theorem kprobeW_stop (sl : Array Word) (ob N i bt j d : Word)
    (hc : ¬ (j ≠ i ∧ bt < rdW sl (ob + j * 2) ∧ rdW sl (ob + j * 2) < MARK)) :
    kprobeW sl ob N i bt j d = some j := by
  rw [kprobeW]; simp only [hc, ↓reduceIte]

theorem kprobeW_next (sl : Array Word) (ob N i bt j d : Word)
    (hc : j ≠ i ∧ bt < rdW sl (ob + j * 2) ∧ rdW sl (ob + j * 2) < MARK) (hd : ¬ N ≤ d) :
    kprobeW sl ob N i bt j d = kprobeW sl ob N i bt ((j + 1) * (if j + 1 < N then 1 else 0)) (d + 1) := by
  rw [kprobeW]; simp only [hc, hd, ne_eq, not_false_eq_true, and_self, ↓reduceIte]

theorem kprobeL_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mapS (gmap C) (kprobeL C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ Keep2 (gO C + 11) (gO C + 12) s₀ s' ∧
      kprobeW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0))) (s₀.loc (gO C + 4)) (s₀.loc (gO C))
        (s₀.loc (gO C + 2)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 11)) (s₀.loc (gO C + 12)) =
        some (s'.loc (gO C + 11)); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := mapS (gmap C) (kprobeL C)) rfl]
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, gmap_zero,
    Nat.reduceSub, Nat.add_zero]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64, ih]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.reduceEqDiff,
    bne_iff_ne, ne_eq, rd64_rdWC, self_eq_addlit, zero_eq_addlit,
    Bool.and_eq_true, ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, Keep2, kprobeW_stop, kprobeW_next]

theorem kprobeL_step_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kprobeL C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ Keep2 (gO C + 11) (gO C + 12) s₀ s' ∧
      kprobeW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0))) (s₀.loc (gO C + 4)) (s₀.loc (gO C))
        (s₀.loc (gO C + 2)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 11)) (s₀.loc (gO C + 12)) =
        some (s'.loc (gO C + 11)); ⊤⦄ :=
  Triple.step_exec (kprobeL_spec p C (n + 1) s₀)

/-! ### Taking and placing an entry -/

/-- **Take the marked entry** of slot `H`: the budget `e` was not `0` and drops by one, `v`
unmarked, `q` its key word, `j` the home of its hash in the doubled table, `d = 0`. -/
theorem kpickB_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kpickB C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧
      (∀ z, z < gO C + 14 → z ≠ gO C + 7 → z ≠ gO C + 8 → z ≠ gO C + 9 → z ≠ gO C + 10 →
        z ≠ gO C + 11 → z ≠ gO C + 12 → s'.loc z = s₀.loc z) ∧
      (∀ z, gO C + 17 ≤ z → s'.loc z = s₀.loc z) ∧
      ¬ s₀.loc (gO C + 7) = 0 ∧ s'.loc (gO C + 7) = s₀.loc (gO C + 7) - 1 ∧
      s'.loc (gO C + 8) = s₀.loc (gO C + 8) - MARK ∧
      s'.loc (gO C + 9) = rdW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0)))
        (s₀.loc (gO C + 4) + s₀.loc (gO C + 2) * 2 + 1) ∧
      s'.loc (gO C + 11) = homeW (ghC C s₀.mem (s'.loc (gO C + 9))) (s₀.loc (gO C)) ∧
      s'.loc (gO C + 12) = 0; ⊤⦄ := by
  unfold kpickB
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, gmap_zero,
    Nat.reduceSub, Nat.add_zero]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64, khash_spec p C hO n]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, beq_iff_eq, rd64_rdWC, zero_eq_addlit, homeW_eq, ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, lt_ne_addlit]

/-- **Place the entry** at slot `j` (`kplaceW`): the memory and the next value word `v`. -/
theorem kplaceB_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kplaceB C))
    ⦃fun r s' => r = .normal ∧ Keep3 (gO C + 5) (gO C + 6) (gO C + 8) s₀ s' ∧
      s'.mem = (kplaceW (tierA C.sa (s₀.loc 0)) (s₀.loc (gO C + 4)) (s₀.loc (gO C + 2))
        (s₀.loc (gO C + 11)) (s₀.loc (gO C + 8)) (s₀.loc (gO C + 9)) s₀.mem).1 ∧
      s'.loc (gO C + 8) = (kplaceW (tierA C.sa (s₀.loc 0)) (s₀.loc (gO C + 4)) (s₀.loc (gO C + 2))
        (s₀.loc (gO C + 11)) (s₀.loc (gO C + 8)) (s₀.loc (gO C + 9)) s₀.mem).2; ⊤⦄ := by
  unfold kplaceB
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, gmap_zero,
    Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64, st64]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.reduceEqDiff, beq_iff_eq, rd64_rdWC, zero_eq_addlit, ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, Keep3, kplaceW]

/-! ### The re-insertion loops -/

/-- The variables the re-insertion loops keep: the push's (below `gO`), `n2 n ob bt`, and the
mark ranges' (from `gO + 17`). -/
def KeepR (C : ConsSch) (s s' : St) : Prop :=
  KeepLo (gO C) s s' ∧ s'.loc (gO C) = s.loc (gO C) ∧ s'.loc (gO C + 1) = s.loc (gO C + 1) ∧
    s'.loc (gO C + 4) = s.loc (gO C + 4) ∧ s'.loc (gO C + 13) = s.loc (gO C + 13) ∧
    ∀ z, gO C + 17 ≤ z → s'.loc z = s.loc z

theorem kinnerW_done (sa : TieredArray) (G : Mem → Word → Word) (N ob bt i e v : Word) (m : Mem)
    (hv : ¬ MARK ≤ v) : kinnerW sa G N ob bt i e v m = some (m, e) := by
  rw [kinnerW]; simp [hv]

theorem kinnerW_more (sa : TieredArray) (G : Mem → Word → Word) (N ob bt i e v : Word) (m : Mem)
    (hv : MARK ≤ v) (he : ¬ e = 0) (j : Word)
    (hj : kprobeW (m.arr64 sa) ob N i bt (homeW (G m (rdW (m.arr64 sa) (ob + i * 2 + 1))) N) 0 = some j) :
    kinnerW sa G N ob bt i e v m =
      kinnerW sa G N ob bt i (e - 1)
        (kplaceW sa ob i j (v - MARK) (rdW (m.arr64 sa) (ob + i * 2 + 1)) m).2
        (kplaceW sa ob i j (v - MARK) (rdW (m.arr64 sa) (ob + i * 2 + 1)) m).1 := by
  rw [kinnerW]; simp only [hv, he, hj, ↓reduceIte]

theorem kinnerL_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mapS (gmap C) (kinnerL C))
    ⦃fun r s' => r = .normal ∧ KeepR C s₀ s' ∧ s'.loc (gO C + 2) = s₀.loc (gO C + 2) ∧
      kinnerW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 4))
        (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (s₀.loc (gO C + 7)) (s₀.loc (gO C + 8)) s₀.mem =
        some (s'.mem, s'.loc (gO C + 7)); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := mapS (gmap C) (kinnerL C)) rfl]
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit,
    Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, kpickB_spec p C hO n, kprobeL_step_spec p C n,
    kplaceB_spec p C n, ih]
  all_goals (simp (disch := decide) only [Cmp.eval,
    Expr.pval, Cond.pval] at *)
  all_goals grind [lang_grind, arena_grind, KeepR, KeepLo, Keep2, Keep3, kinnerW_done,
    kinnerW_more, lt_ne_addlit]

theorem kinnerL_step_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kinnerL C))
    ⦃fun r s' => r = .normal ∧ KeepR C s₀ s' ∧ s'.loc (gO C + 2) = s₀.loc (gO C + 2) ∧
      kinnerW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 4))
        (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (s₀.loc (gO C + 7)) (s₀.loc (gO C + 8)) s₀.mem =
        some (s'.mem, s'.loc (gO C + 7)); ⊤⦄ :=
  Triple.step_exec (kinnerL_spec p C hO (n + 1) s₀)

theorem krehashW_done (sa : TieredArray) (G : Mem → Word → Word) (N n ob bt i e : Word) (m : Mem)
    (hi : ¬ i < n) : krehashW sa G N n ob bt i e m = some m := by
  rw [krehashW]; simp [hi]

theorem krehashW_step (sa : TieredArray) (G : Mem → Word → Word) (N n ob bt i e : Word) (m m' : Mem)
    (e' : Word) (hi : i < n)
    (h : kinnerW sa G N ob bt i e (rdW (m.arr64 sa) (ob + i * 2)) m = some (m', e')) :
    krehashW sa G N n ob bt i e m = krehashW sa G N n ob bt (i + 1) e' m' := by
  rw [krehashW]; simp [hi, h]

/-- **The re-insertion loop** over the slots `H ‥ u - 1` (`u` a mark range's end, from
`gO + 17` on). -/
theorem krehashL_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (u : Var) (hu : gO C + 17 ≤ gmap C u)
    (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mapS (gmap C) (krehashL C u))
    ⦃fun r s' => r = .normal ∧ KeepR C s₀ s' ∧
      krehashW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gmap C u)) (s₀.loc (gO C + 4))
        (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (s₀.loc (gO C + 7)) s₀.mem = some s'.mem; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := mapS (gmap C) (krehashL C u)) rfl]
  simp (disch := decide) only [krehashS, mapS, mapE, mapC, gmap_lit, gmap_zero,
    Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64, kinnerL_step_spec p C hO n, ih]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, rd64_rdWC, self_eq_addlit, zero_eq_addlit,
    ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, KeepR, KeepLo, krehashW_done, krehashW_step,
    lt_ne_addlit]

theorem krehashL_step_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (u : Var)
    (hu : gO C + 17 ≤ gmap C u) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (krehashL C u))
    ⦃fun r s' => r = .normal ∧ KeepR C s₀ s' ∧
      krehashW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gmap C u)) (s₀.loc (gO C + 4))
        (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (s₀.loc (gO C + 7)) s₀.mem = some s'.mem; ⊤⦄ :=
  Triple.step_exec (krehashL_spec p C hO u hu (n + 1) s₀)

/-! ### The sweep -/

/-- The mark ranges of a growth state (`a0 a1 b0 b1` at `gO + 17 ‥ gO + 20`). -/
def mkOf (C : ConsSch) (s : St) : MkR :=
  ⟨s.loc (gO C + 17), s.loc (gO C + 18), s.loc (gO C + 19), s.loc (gO C + 20)⟩

/-- Every local outside the mark ranges is kept. -/
def KeepMk (C : ConsSch) (s s' : St) : Prop :=
  ∀ z, z < gO C + 17 ∨ gO C + 21 ≤ z → s'.loc z = s.loc z

theorem KeepMk.loc {C : ConsSch} {s s' : St} (h : KeepMk C s s') (z : Var)
    (hz : z < gO C + 17 ∨ gO C + 21 ≤ z) : s'.loc z = s.loc z := h z hz

grind_pattern [lang_grind] KeepMk.loc => KeepMk C s s', s'.loc z

theorem mkOf_setLoc (C : ConsSch) (s : St) (z : Nat) (v : Word) (hz : z < gO C + 17) :
    mkOf C (s.setLoc z v) = mkOf C s := by
  simp only [mkOf, St.setLoc_loc]
  have h1 : (gO C + 17 = z) = False := by simp only [eq_iff_iff, iff_false]; omega
  have h2 : (gO C + 18 = z) = False := by simp only [eq_iff_iff, iff_false]; omega
  have h3 : (gO C + 19 = z) = False := by simp only [eq_iff_iff, iff_false]; omega
  have h4 : (gO C + 20 = z) = False := by simp only [eq_iff_iff, iff_false]; omega
  simp only [h1, h2, h3, h4, ↓reduceIte]

theorem kupW_stop (sl : Array Word) (ob N bt j : Word)
    (hc : ¬ (j < N ∧ bt < rdW sl (ob + j * 2) ∧ rdW sl (ob + j * 2) < MARK ∧ j + 1 < N)) :
    kupW sl ob N bt j = j := by
  rw [kupW]; simp only [hc, ↓reduceIte]

theorem kupW_next (sl : Array Word) (ob N bt j : Word)
    (hc : j < N ∧ bt < rdW sl (ob + j * 2) ∧ rdW sl (ob + j * 2) < MARK ∧ j + 1 < N) :
    kupW sl ob N bt j = kupW sl ob N bt (j + 1) := by
  rw [kupW]; simp only [hc, and_self, ↓reduceIte]

/-- **The sweep's probe loop**: from `j < N` with `x` slot `j`'s value word, it ends at `kupW`'s
slot, `x` that slot's value word. -/
theorem kupLoop_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s₀.loc (gO C + 6) = rdW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0)))
      (s₀.loc (gO C + 4) + s₀.loc (gO C + 11) * 2) ∧ s₀.loc (gO C + 11) < s₀.loc (gO C)⦄
    exec p n (mapS (gmap C) (kupLoop C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ Keep2 (gO C + 6) (gO C + 11) s₀ s' ∧
      s'.loc (gO C + 11) = kupW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0))) (s₀.loc (gO C + 4))
        (s₀.loc (gO C)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 11)) ∧
      s'.loc (gO C + 6) = rdW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0)))
        (s₀.loc (gO C + 4) + s'.loc (gO C + 11) * 2); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := mapS (gmap C) (kupLoop C)) rfl]
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, gmap_zero,
    Nat.reduceSub, Nat.add_zero]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64, ih]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, rd64_rdWC, self_eq_addlit, zero_eq_addlit,
    Bool.and_eq_true, ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, Keep2, kupW_stop, kupW_next]

theorem kupLoop_step_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s₀.loc (gO C + 6) = rdW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0)))
      (s₀.loc (gO C + 4) + s₀.loc (gO C + 11) * 2) ∧ s₀.loc (gO C + 11) < s₀.loc (gO C)⦄
    step p (exec p n) (mapS (gmap C) (kupLoop C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ Keep2 (gO C + 6) (gO C + 11) s₀ s' ∧
      s'.loc (gO C + 11) = kupW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0))) (s₀.loc (gO C + 4))
        (s₀.loc (gO C)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 11)) ∧
      s'.loc (gO C + 6) = rdW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0)))
        (s₀.loc (gO C + 4) + s'.loc (gO C + 11) * 2); ⊤⦄ :=
  Triple.step_exec (kupLoop_spec p C (n + 1) s₀)

/-- **The sweep's probe** from `j < N`. -/
theorem kupL_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s₀.loc (gO C + 11) < s₀.loc (gO C)⦄
    step p (exec p n) (mapS (gmap C) (kupL C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ Keep2 (gO C + 6) (gO C + 11) s₀ s' ∧
      s'.loc (gO C + 11) = kupW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0))) (s₀.loc (gO C + 4))
        (s₀.loc (gO C)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 11)) ∧
      s'.loc (gO C + 6) = rdW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0)))
        (s₀.loc (gO C + 4) + s'.loc (gO C + 11) * 2); ⊤⦄ := by
  unfold kupL
  simp (disch := decide) only [mapS, mapE, gmap_lit, gmap_zero, Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64, kupLoop_step_spec p C n]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval,
    Expr.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, rd64_rdWC, self_eq_addlit, zero_eq_addlit, ↓reduceIte] at *)
  all_goals grind [lang_grind, Keep2]

/-- **A deferral's range** (`kdefB`): the mark ranges become `kdefR` of `n` and the slot `H`. -/
theorem kdefB_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) kdefB)
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ KeepMk C s₀ s' ∧
      mkOf C s' = kdefR (s₀.loc (gO C + 1)) (s₀.loc (gO C + 2)) (mkOf C s₀); ⊤⦄ := by
  unfold kdefB
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff,
    beq_iff_eq, ↓reduceIte] at *)
  all_goals grind [lang_grind, KeepMk, mkOf, kdefR]

theorem homeW_lt_of_gt (h N i : Word) (hi : i < homeW h N) : homeW h N < N := by
  by_cases hN : N = 0
  · subst hN; exfalso
    have : homeW h 0 = 0 := by simp [homeW]
    rw [this] at hi; exact absurd hi (by simp [UInt64.lt_iff_toNat_lt])
  · have hN' : N.toNat ≠ 0 := fun e => hN (UInt64.toNat_inj.mp (by simpa using e))
    simp only [homeW]
    have hx := ((h * golden) ^^^ ((h * golden) >>> 32)).toNat_lt
    have hn' := N.toNat_lt
    have : ((h * golden) ^^^ ((h * golden) >>> 32)).toNat * N.toNat / 2 ^ 64 < N.toNat :=
      Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right hx (by omega))
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact this

/-- **The sweep step's probe** (`ktopP`) at slot `H` (value word `v`): `j` and `x` are `ktgW` and
`kxW` of the growth's hash, `q` the key word. -/
theorem ktopP_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s₀.loc (gO C + 8) = rdW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0)))
      (s₀.loc (gO C + 4) + s₀.loc (gO C + 2) * 2)⦄
    step p (exec p n) (mapS (gmap C) (ktopP C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧
      (∀ z, z ≠ gO C + 6 → z ≠ gO C + 9 → z ≠ gO C + 10 → z ≠ gO C + 11 →
        (z < gO C + 14 ∨ gO C + 17 ≤ z) → s'.loc z = s₀.loc z) ∧
      s'.loc (gO C + 9) = rdW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0)))
        (s₀.loc (gO C + 4) + s₀.loc (gO C + 2) * 2 + 1) ∧
      s'.loc (gO C + 11) = ktgW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 4))
        (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) s₀.mem ∧
      s'.loc (gO C + 6) = kxW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 4))
        (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) s₀.mem; ⊤⦄ := by
  unfold ktopP
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, gmap_zero, Nat.reduceSub, Nat.add_zero]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64, khash_spec p C hO n, kupL_spec p C n]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, rd64_rdWC, zero_eq_addlit,
    homeW_eq, ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, lt_ne_addlit, Keep2, ktgW, kxW, kjW, homeW_lt_of_gt]

/-- **The sweep step's placement** (`ktopQ`): `ktopQW` of `j x v q`. -/
theorem ktopQ_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (ktopQ C))
    ⦃fun r s' => r = .normal ∧ KeepMk C s₀ s' ∧
      s'.mem = (ktopQW (tierA C.sa (s₀.loc 0)) (s₀.loc (gO C + 1)) (s₀.loc (gO C + 4))
        (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (s₀.loc (gO C + 11)) (s₀.loc (gO C + 6))
        (s₀.loc (gO C + 8)) (s₀.loc (gO C + 9)) (mkOf C s₀) s₀.mem).1 ∧
      mkOf C s' = (ktopQW (tierA C.sa (s₀.loc 0)) (s₀.loc (gO C + 1)) (s₀.loc (gO C + 4))
        (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (s₀.loc (gO C + 11)) (s₀.loc (gO C + 6))
        (s₀.loc (gO C + 8)) (s₀.loc (gO C + 9)) (mkOf C s₀) s₀.mem).2; ⊤⦄ := by
  unfold ktopQ
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, gmap_zero, Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc, st64, kdefB_spec p C n]
  all_goals (simp (disch := decide) only [BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval,
    bne_iff_ne, ne_eq] at *)
  all_goals grind [lang_grind, arena_grind, KeepMk, mkOf, ktopQW]

/-- **The sweep's step at a live slot** (`ktopB`): `ktopBW`. -/
theorem ktopB_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s₀.loc (gO C + 8) = rdW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0)))
      (s₀.loc (gO C + 4) + s₀.loc (gO C + 2) * 2)⦄
    step p (exec p n) (mapS (gmap C) (ktopB C))
    ⦃fun r s' => r = .normal ∧
      (∀ z, z ≠ gO C + 6 → z ≠ gO C + 9 → z ≠ gO C + 10 → z ≠ gO C + 11 →
        (z < gO C + 14 ∨ gO C + 21 ≤ z) → s'.loc z = s₀.loc z) ∧
      s'.mem = (ktopBW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 1))
        (s₀.loc (gO C + 4)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (mkOf C s₀) s₀.mem).1 ∧
      mkOf C s' = (ktopBW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 1))
        (s₀.loc (gO C + 4)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (mkOf C s₀) s₀.mem).2; ⊤⦄ := by
  apply triple_pre_and; intro hv
  unfold ktopB
  simp only [mapS]
  refine triple_seq _ (triple_pre_and' (ktopP_spec p C hO n s₀) hv) (fun s₁ h₁ => ?_)
  obtain ⟨m1, k1, q1, j1, x1⟩ := h₁
  refine triple_weaken (ktopQ_spec p C n s₁) (fun r s' ⟨hr, k2, m2, mk2⟩ => ?_)
  have kk : ∀ z, z ≠ gO C + 6 → z ≠ gO C + 9 → z ≠ gO C + 10 → z ≠ gO C + 11 →
      (z < gO C + 14 ∨ gO C + 17 ≤ z) → s₁.loc z = s₀.loc z := k1
  have e0 : s₁.loc 0 = s₀.loc 0 := by
    have := zero_lt_gO C; exact kk 0 (by omega) (by omega) (by omega) (by omega) (.inl (by omega))
  have ek : ∀ i : Nat, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 8 ∨ i = 13 ∨ (17 ≤ i) →
      s₁.loc (gO C + i) = s₀.loc (gO C + i) := fun i hi => by
    rcases hi with h | h | h | h | h | h | h <;>
      refine kk (gO C + i) ?_ ?_ ?_ ?_ ?_ <;> omega
  have mk1 : mkOf C s₁ = mkOf C s₀ := by
    simp only [mkOf, ek 17 (by simp), ek 18 (by simp), ek 19 (by simp), ek 20 (by simp)]
  have hB : ktopBW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 1))
      (s₀.loc (gO C + 4)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (mkOf C s₀) s₀.mem =
      ktopQW (tierA C.sa (s₁.loc 0)) (s₁.loc (gO C + 1)) (s₁.loc (gO C + 4))
        (s₁.loc (gO C + 13)) (s₁.loc (gO C + 2)) (s₁.loc (gO C + 11)) (s₁.loc (gO C + 6))
        (s₁.loc (gO C + 8)) (s₁.loc (gO C + 9)) (mkOf C s₁) s₁.mem := by
    rw [ktopBW, j1, x1, q1, mk1, m1, e0, ek 1 (by simp), ek 4 (by simp), ek 13 (by simp),
      ek 2 (by simp), ek 8 (by simp), hv]
  refine ⟨hr, fun z h6 h9 h10 h11 hz => ?_, by rw [hB]; exact m2, by rw [hB]; exact mk2⟩
  rw [k2 z (by omega)]
  exact kk z h6 h9 h10 h11 (by omega)

theorem ktopW_zero (sa : TieredArray) (G : Mem → Word → Word) (N n ob bt H : Word) (k : MkR) (m : Mem)
    (h : H = 0) : ktopW sa G N n ob bt H k m = (m, k) := by
  rw [ktopW]; simp [h]

theorem ktopW_step (sa : TieredArray) (G : Mem → Word → Word) (N n ob bt H : Word) (k : MkR) (m : Mem)
    (h : ¬ H = 0) : ktopW sa G N n ob bt H k m = ktopW sa G N n ob bt (H - 1)
      (ktopS sa G N n ob bt (H - 1) k m).2 (ktopS sa G N n ob bt (H - 1) k m).1 := by
  rw [ktopW]; simp [h]

theorem ktopS_live (sa : TieredArray) (G : Mem → Word → Word) (N n ob bt i : Word) (k : MkR) (m : Mem)
    (h : bt < rdW (m.arr64 sa) (ob + i * 2)) : ktopS sa G N n ob bt i k m = ktopBW sa G N n ob bt i k m := by
  rw [ktopS]; simp [h]

theorem ktopS_dead (sa : TieredArray) (G : Mem → Word → Word) (N n ob bt i : Word) (k : MkR) (m : Mem)
    (h : ¬ bt < rdW (m.arr64 sa) (ob + i * 2)) : ktopS sa G N n ob bt i k m = (m, k) := by
  rw [ktopS]; simp [h]

/-- The variables the sweep keeps: the push's (below `gO`), `n2 n ob bt`. -/
def KeepT (C : ConsSch) (s s' : St) : Prop :=
  KeepLo (gO C) s s' ∧ s'.loc (gO C) = s.loc (gO C) ∧ s'.loc (gO C + 1) = s.loc (gO C + 1) ∧
    s'.loc (gO C + 4) = s.loc (gO C + 4) ∧ s'.loc (gO C + 13) = s.loc (gO C + 13)

/-- The sweep step's frame: only `H`, `v` and the ranges' and the step's temporaries change. -/
theorem keepT_of (C : ConsSch) (s₀ s : St) (A B : Word)
    (h : ∀ z : Nat, ¬ z = gO C + 6 → ¬ z = gO C + 9 → ¬ z = gO C + 10 → ¬ z = gO C + 11 →
      z < gO C + 14 ∨ gO C + 21 ≤ z →
      s.loc z = if z = gO C + 8 then A else if z = gO C + 2 then B else s₀.loc z) :
    KeepT C s₀ s := by
  have g : ∀ z : Nat, (z < gO C ∨ z = gO C ∨ z = gO C + 1 ∨ z = gO C + 4 ∨ z = gO C + 13) →
      s.loc z = s₀.loc z := fun z hz => by
    rw [h z (by omega) (by omega) (by omega) (by omega) (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  exact ⟨fun z hz => g z (.inl hz), g _ (.inr (.inl rfl)), g _ (.inr (.inr (.inl rfl))),
    g _ (.inr (.inr (.inr (.inl rfl)))), g _ (.inr (.inr (.inr (.inr rfl))))⟩

/-- **The sweep's step** (`ktopBody`): `ktopS` at `H - 1`. -/
theorem ktopBody_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (ktopBody C))
    ⦃fun r s' => r = .normal ∧ KeepT C s₀ s' ∧ s'.loc (gO C + 2) = s₀.loc (gO C + 2) - 1 ∧
      s'.mem = (ktopS (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 1))
        (s₀.loc (gO C + 4)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2) - 1) (mkOf C s₀) s₀.mem).1 ∧
      mkOf C s' = (ktopS (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 1))
        (s₀.loc (gO C + 4)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2) - 1) (mkOf C s₀) s₀.mem).2; ⊤⦄ := by
  unfold ktopBody
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, gmap_zero, Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64, ktopB_spec p C hO n]
  all_goals (try simp (disch := omega) only [St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, decide_eq_true_eq, rd64_rdWC, mkOf_setLoc] at *)
  all_goals (try simp (disch := decide) only [St.setLoc_loc, Nat.add_left_cancel_iff, Nat.reduceEqDiff,
    self_eq_addlit, zero_eq_addlit, ↓reduceIte] at *)
  case vc2 =>
    rename_i hp
    exact keepT_of C s₀ _ _ _ hp.1
  case vc3 =>
    rename_i hp
    rw [hp.1 (gO C + 2) (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [show (gO C + 2 = gO C + 8) = False by simp, ↓reduceIte]
  case vc4 =>
    rename_i hc hp
    rw [ktopS_live _ _ _ _ _ _ _ _ _ hc]; exact hp.2.1
  case vc5 =>
    rename_i hc hp
    rw [ktopS_live _ _ _ _ _ _ _ _ _ hc]; exact hp.2.2
  case vc6 =>
    exact keepT_of C s₀ _ (rdW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0)))
      (s₀.loc (gO C + 4) + (s₀.loc (gO C + 2) - 1) * 2)) (s₀.loc (gO C + 2) - 1)
      (fun z _ _ _ _ _ => by simp only [St.setLoc_loc])
  case vc8 =>
    rename_i hc
    rw [ktopS_dead _ _ _ _ _ _ _ _ _ hc]
  case vc9 =>
    rename_i hc
    rw [ktopS_dead _ _ _ _ _ _ _ _ _ hc]

/-- One sweep step, then the sweep from there: the sweep from the start. -/
theorem ktopW_cons (C : ConsSch) (s₀ s₁ s₂ : St) (hH : ¬ s₀.loc (gO C + 2) = 0)
    (k1 : KeepT C s₀ s₁) (h1 : s₁.loc (gO C + 2) = s₀.loc (gO C + 2) - 1)
    (m1 : s₁.mem = (ktopS (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 1))
        (s₀.loc (gO C + 4)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2) - 1) (mkOf C s₀) s₀.mem).1)
    (r1 : mkOf C s₁ = (ktopS (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 1))
        (s₀.loc (gO C + 4)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2) - 1) (mkOf C s₀) s₀.mem).2)
    (k2 : KeepT C s₁ s₂)
    (m2 : s₂.mem = (ktopW (tierA C.sa (s₁.loc 0)) (ghC C) (s₁.loc (gO C)) (s₁.loc (gO C + 1))
        (s₁.loc (gO C + 4)) (s₁.loc (gO C + 13)) (s₁.loc (gO C + 2)) (mkOf C s₁) s₁.mem).1)
    (r2 : mkOf C s₂ = (ktopW (tierA C.sa (s₁.loc 0)) (ghC C) (s₁.loc (gO C)) (s₁.loc (gO C + 1))
        (s₁.loc (gO C + 4)) (s₁.loc (gO C + 13)) (s₁.loc (gO C + 2)) (mkOf C s₁) s₁.mem).2) :
    KeepT C s₀ s₂ ∧
      s₂.mem = (ktopW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 1))
        (s₀.loc (gO C + 4)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (mkOf C s₀) s₀.mem).1 ∧
      mkOf C s₂ = (ktopW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 1))
        (s₀.loc (gO C + 4)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (mkOf C s₀) s₀.mem).2 := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := k1
  obtain ⟨b0, b1, b2, b3, b4⟩ := k2
  have e0 : s₁.loc 0 = s₀.loc 0 := a0 0 (zero_lt_gO C)
  rw [ktopW_step _ _ _ _ _ _ _ _ _ hH]
  rw [e0, a1, a2, a3, a4, h1, r1, m1] at m2 r2
  refine ⟨⟨fun z hz => (b0 z hz).trans (a0 z hz), b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4⟩,
    m2, r2⟩

/-- **The sweep** (`ktopL`): `ktopW` from the cursor `H`. -/
theorem ktopL_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mapS (gmap C) (ktopL C))
    ⦃fun r s' => r = .normal ∧ KeepT C s₀ s' ∧
      s'.mem = (ktopW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 1))
        (s₀.loc (gO C + 4)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (mkOf C s₀) s₀.mem).1 ∧
      mkOf C s' = (ktopW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 1))
        (s₀.loc (gO C + 4)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (mkOf C s₀) s₀.mem).2; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := mapS (gmap C) (ktopL C)) rfl]
  simp (disch := decide) only [mapE, mapC, gmap_lit, Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, ktopBody_spec p C hO n, ih]
  all_goals (try simp (disch := decide) only [Cmp.eval, Expr.pval, Cond.pval, bne_iff_ne, ne_eq] at *)
  case vc1 =>
    obtain ⟨k1, h1, m1, r1⟩ := ‹KeepT C s₀ _ ∧ _›
    obtain ⟨k2, m2, r2⟩ := ‹KeepT C _ _ ∧ _›
    exact (ktopW_cons C s₀ _ _ ‹_› k1 h1 m1 r1 k2 m2 r2).1
  case vc2 =>
    obtain ⟨k1, h1, m1, r1⟩ := ‹KeepT C s₀ _ ∧ _›
    obtain ⟨k2, m2, r2⟩ := ‹KeepT C _ _ ∧ _›
    exact (ktopW_cons C s₀ _ _ ‹_› k1 h1 m1 r1 k2 m2 r2).2.1
  case vc3 =>
    obtain ⟨k1, h1, m1, r1⟩ := ‹KeepT C s₀ _ ∧ _›
    obtain ⟨k2, m2, r2⟩ := ‹KeepT C _ _ ∧ _›
    exact (ktopW_cons C s₀ _ _ ‹_› k1 h1 m1 r1 k2 m2 r2).2.2
  all_goals first
    | exact ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    | (rename_i hH; rw [ktopW_zero _ _ _ _ _ _ _ _ _ (Classical.not_not.mp hH)])

theorem ktopL_step_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (ktopL C))
    ⦃fun r s' => r = .normal ∧ KeepT C s₀ s' ∧
      s'.mem = (ktopW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 1))
        (s₀.loc (gO C + 4)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (mkOf C s₀) s₀.mem).1 ∧
      mkOf C s' = (ktopW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 1))
        (s₀.loc (gO C + 4)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (mkOf C s₀) s₀.mem).2; ⊤⦄ :=
  Triple.step_exec (ktopL_spec p C hO (n + 1) s₀)

/-! ### The growth block -/

theorem kgrowH1_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kgrowH1 C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ KeepLo (gO C) s₀ s' ∧
      s'.loc (gO C) = knW C.sa s₀.mem (s₀.loc 0) * 2 ∧
      s'.loc (gO C + 1) = knW C.sa s₀.mem (s₀.loc 0) ∧
      s'.loc (gO C + 3) = s₀.mem.len64 (tierA C.sa (s₀.loc 0)) - 2 ∧
      s'.loc (gO C + 4) = koW C.sa s₀.mem (s₀.loc 0) + 2 ∧
      s'.loc (gO C + 5) = koW C.sa s₀.mem (s₀.loc 0); ⊤⦄ := by
  unfold kgrowH1
  simp (disch := decide) only [mapS, mapE, gmap_lit, gmap_zero, Nat.reduceSub,
    Nat.add_zero]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval,
    Expr.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, rd64_rdWC, self_eq_addlit, addlit_eq_self, zero_eq_addlit, zero_eq_gO, ↓reduceIte] at *)
  all_goals grind [lang_grind, KeepLo, knW, koW, lt_ne_addlit]

theorem kgrowH2_spec (p : Prog) (C : ConsSch) (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁⦄
    step p (exec p n) (mapS (gmap C) (kgrowH2 C))
    ⦃fun r s' => r = .normal ∧ ¬ s₁.loc (gO C + 3) < s₁.loc (gO C + 5) + s₁.loc (gO C) * 2 ∧
      s'.mem = s₁.mem.set64 (tierA C.sa (s₁.loc 0)) 0 (s₁.loc (gO C) - SN0) ∧ s'.loc = s₁.loc; ⊤⦄ := by
  unfold kgrowH2
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, gmap_zero, Nat.reduceSub,
    Nat.add_zero]
  vcgen [step, evalE_spec, evalC_spec, setLoc, st64]
  all_goals (simp (disch := decide) only [BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval] at *)
  all_goals grind [lang_grind]

theorem kgrowH3_spec (p : Prog) (C : ConsSch) (n : Nat) (s₂ : St) :
    ⦃fun s => s = s₂⦄
    step p (exec p n) (mapS (gmap C) kgrowH3)
    ⦃fun r s' => r = .normal ∧ s'.mem = s₂.mem ∧ Keep2 (gO C + 6) (gO C + 7) s₂ s' ∧
      s'.loc (gO C + 6) = s₂.loc (gO C + 4) + s₂.loc (gO C + 1) * 2 ∧
      s'.loc (gO C + 7) = s₂.loc (gO C + 1) >>> 2; ⊤⦄ := by
  unfold kgrowH3
  simp (disch := decide) only [mapS, mapE, gmap_lit, Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval,
    Expr.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, ↓reduceIte] at *)
  all_goals grind [lang_grind, Keep2]

theorem kgrowH4_spec (p : Prog) (C : ConsSch) (n : Nat) (s₂ : St) :
    ⦃fun s => s = s₂⦄
    step p (exec p n) (mapS (gmap C) kgrowH4)
    ⦃fun r s' => r = .normal ∧ s'.mem = s₂.mem ∧
      (∀ z : Nat, z ≠ gO C + 2 → z ≠ gO C + 13 → (z < gO C + 17 ∨ gO C + 21 ≤ z) →
        s'.loc z = s₂.loc z) ∧
      s'.loc (gO C + 13) = rdW (s₂.mem.arr64 CTL) SCB * s₂.loc 0 ∧
      s'.loc (gO C + 2) = s₂.loc (gO C + 1) ∧ mkOf C s' = ⟨0, 0, 0, 0⟩; ⊤⦄ := by
  unfold kgrowH4
  simp (disch := decide) only [mapS, mapE, gmap_lit, gmap_zero, Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval,
    Expr.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, rd64_rdWC, ↓reduceIte] at *)
  all_goals grind [lang_grind, mkOf]

theorem kgrowH5_spec (p : Prog) (C : ConsSch) (n : Nat) (s₂ : St) :
    ⦃fun s => s = s₂⦄
    step p (exec p n) (mapS (gmap C) kgrowH5)
    ⦃fun r s' => r = .normal ∧ s'.mem = s₂.mem ∧ Keep2 (gO C + 2) (gO C + 7) s₂ s' ∧
      s'.loc (gO C + 2) = s₂.loc (gO C + 17) ∧ s'.loc (gO C + 7) = s₂.loc (gO C + 1); ⊤⦄ := by
  unfold kgrowH5
  simp (disch := decide) only [mapS, mapE, gmap_lit, Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem,
    Expr.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, ↓reduceIte] at *)
  all_goals grind [lang_grind, Keep2]

theorem kgrowH6_spec (p : Prog) (C : ConsSch) (n : Nat) (s₂ : St) :
    ⦃fun s => s = s₂⦄
    step p (exec p n) (mapS (gmap C) kgrowH6)
    ⦃fun r s' => r = .normal ∧ s'.mem = s₂.mem ∧ Keep2 (gO C + 2) (gO C + 7) s₂ s' ∧
      s'.loc (gO C + 2) = s₂.loc (gO C + 19) ∧ s'.loc (gO C + 7) = s₂.loc (gO C + 1); ⊤⦄ := by
  unfold kgrowH6
  simp (disch := decide) only [mapS, mapE, gmap_lit, Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem,
    Expr.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, ↓reduceIte] at *)
  all_goals grind [lang_grind, Keep2]

/-- **The growth's head**: the room check passed, the count word written, `n2 n ob` and the
zero loop's `x e` set. -/
theorem kgrowH_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kgrowH C))
    ⦃fun r s' => r = .normal ∧ KeepLo (gO C) s₀ s' ∧
      ¬ s₀.mem.len64 (tierA C.sa (s₀.loc 0)) - 2 <
        koW C.sa s₀.mem (s₀.loc 0) + knW C.sa s₀.mem (s₀.loc 0) * 2 * 2 ∧
      s'.mem = s₀.mem.set64 (tierA C.sa (s₀.loc 0)) 0 (knW C.sa s₀.mem (s₀.loc 0) * 2 - SN0) ∧
      s'.loc (gO C) = knW C.sa s₀.mem (s₀.loc 0) * 2 ∧
      s'.loc (gO C + 1) = knW C.sa s₀.mem (s₀.loc 0) ∧
      s'.loc (gO C + 4) = koW C.sa s₀.mem (s₀.loc 0) + 2 ∧
      s'.loc (gO C + 6) = koW C.sa s₀.mem (s₀.loc 0) + 2 + knW C.sa s₀.mem (s₀.loc 0) * 2 ∧
      s'.loc (gO C + 7) = knW C.sa s₀.mem (s₀.loc 0) >>> 2; ⊤⦄ := by
  unfold kgrowH
  simp only [mapS]
  refine triple_seq _ (kgrowH1_spec p C n s₀) (fun s₁ h₁ => ?_)
  obtain ⟨m1, k1, a0, a1, a3, a4, a5⟩ := h₁
  refine triple_seq _ (kgrowH2_spec p C n s₁) (fun s₂ h₂ => ?_)
  obtain ⟨hc, m2, l2⟩ := h₂
  refine triple_weaken (kgrowH3_spec p C n s₂) (fun r s ⟨hr, m3, k3, b6, b7⟩ => ?_)
  have e0 : s₁.loc 0 = s₀.loc 0 := k1 0 (zero_lt_gO C)
  have g : ∀ z, z = gO C ∨ z = gO C + 1 ∨ z = gO C + 4 → s.loc z = s₁.loc z := fun z hz => by
    rcases hz with rfl | rfl | rfl
    · rw [k3 _ (self_ne_addlit _ _ (by decide)) (self_ne_addlit _ _ (by decide)), l2]
    all_goals rw [k3 _ (addlit_ne_addlit _ _ _ (by decide)) (addlit_ne_addlit _ _ _ (by decide)), l2]
  refine ⟨hr, fun z hz => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k3 z (lt_ne_addlit _ _ _ hz) (lt_ne_addlit _ _ _ hz), l2, k1 z hz]
  · rw [a3, a5, a0] at hc; exact hc
  · rw [m3, m2, m1, e0, a0]
  · rw [g _ (.inl rfl), a0]
  · rw [g _ (.inr (.inl rfl)), a1]
  · rw [g _ (.inr (.inr rfl)), a4]
  · rw [b6, l2, a4, a1]
  · rw [b7, l2, a1]

theorem kzeroW_arr (sa : TieredArray) (x : Word) (e : Nat) (m : Mem) (b : TieredArray) (hb : b ≠ sa) :
    (kzeroW sa x e m).arr64 b = m.arr64 b := (kzeroW_fr sa e x m).arr b hb

/-- **The growth block** (renamed into the push): it keeps the push's variables (below `gO`) and
leaves `kgrowM`'s memory. -/
theorem kgrowBlk_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (kgrowBlk C)
    ⦃fun r s' => r = .normal ∧ KeepLo (gO C) s₀ s' ∧
      kgrowM C.sa (ghC C) (s₀.loc 0) s₀.mem = some s'.mem; ⊤⦄ := by
  have hsc : ∀ t, tierA C.sa t ≠ CTL := fun t =>
    (ne_tierA (Ne.symm hO.arrs.2.1) t).symm
  have h0 := zero_lt_gO C
  unfold kgrowBlk kgrowB
  simp only [mapS]
  refine triple_seq _ (kgrowH_spec p C n s₀) (fun s₃ h₃ => ?_)
  obtain ⟨k3, hc, m3, a0, a1, a4, b6, b7⟩ := h₃
  refine triple_seq _ (kzeroL_step_spec p C n s₃) (fun s₄ h₄ => ?_)
  obtain ⟨k4, m4⟩ := h₄
  refine triple_seq _ (kgrowH4_spec p C n s₄) (fun s₅ h₅ => ?_)
  obtain ⟨m5, k5, c13, c2, mk5⟩ := h₅
  refine triple_seq _ (ktopL_step_spec p C hO n s₅) (fun s₆ h₆ => ?_)
  obtain ⟨⟨k6, e6, f6, o6, t6⟩, m6, mk6⟩ := h₆
  refine triple_seq _ (kgrowH5_spec p C n s₆) (fun s₇ h₇ => ?_)
  obtain ⟨m7, k7, d2, d7⟩ := h₇
  refine triple_seq _ (krehashL_step_spec p C hO 19 (by simp [gmap]) n s₇) (fun s₈ h₈ => ?_)
  obtain ⟨⟨k8, e8, f8, o8, t8, h8⟩, w8⟩ := h₈
  refine triple_seq _ (kgrowH6_spec p C n s₈) (fun s₉ h₉ => ?_)
  obtain ⟨m9, k9, g2, g7⟩ := h₉
  refine triple_weaken (krehashL_step_spec p C hO 21 (by simp [gmap]) n s₉)
    (fun r s ⟨hr, ⟨k10, _, _, _, _, _⟩, w10⟩ => ?_)
  -- the keeps, as `Nat` facts
  have K4 : ∀ z : Nat, z ≠ gO C + 6 → z ≠ gO C + 7 → s₄.loc z = s₃.loc z := fun z h1 h2 => k4 z h1 h2
  have K7 : ∀ z : Nat, z ≠ gO C + 2 → z ≠ gO C + 7 → s₇.loc z = s₆.loc z := fun z h1 h2 => k7 z h1 h2
  have K9 : ∀ z : Nat, z ≠ gO C + 2 → z ≠ gO C + 7 → s₉.loc z = s₈.loc z := fun z h1 h2 => k9 z h1 h2
  have H8 : ∀ z : Nat, gO C + 17 ≤ z → s₈.loc z = s₇.loc z := h8
  -- back to `s₀`
  have l0 : ∀ z : Nat, z < gO C → s₉.loc z = s₀.loc z := fun z hz => by
    rw [K9 z (by omega) (by omega), k8 z hz, K7 z (by omega) (by omega), k6 z hz,
      k5 z (by omega) (by omega) (.inl (by omega)), K4 z (by omega) (by omega), k3 z hz]
  have t0 : s₉.loc 0 = s₀.loc 0 := l0 0 h0
  refine ⟨hr, fun z hz => by rw [k10 z hz, l0 z hz], ?_⟩
  have s3_0 : s₃.loc 0 = s₀.loc 0 := k3 0 h0
  have s4_0 : s₄.loc 0 = s₀.loc 0 := by rw [K4 0 (by omega) (by omega), s3_0]
  have s5_0 : s₅.loc 0 = s₀.loc 0 := by rw [k5 0 (by omega) (by omega) (.inl (by omega)), s4_0]
  have s6_0 : s₆.loc 0 = s₀.loc 0 := by rw [k6 0 h0, s5_0]
  have s7_0 : s₇.loc 0 = s₀.loc 0 := by rw [K7 0 (by omega) (by omega), s6_0]
  have s8_0 : s₈.loc 0 = s₀.loc 0 := by rw [k8 0 h0, s7_0]
  -- `n2 n ob` (`gO`, `gO + 1`, `gO + 4`) at `s₅`
  have v5 : ∀ i : Nat, i = 0 ∨ i = 1 ∨ i = 4 → s₅.loc (gO C + i) = s₃.loc (gO C + i) := fun i hi => by
    rcases hi with rfl | rfl | rfl <;>
      rw [k5 _ (by omega) (by omega) (.inl (by omega)), K4 _ (by omega) (by omega)]
  have s5N : s₅.loc (gO C) = knW C.sa s₀.mem (s₀.loc 0) * 2 := by
    have := v5 0 (.inl rfl); simp only [Nat.add_zero] at this; rw [this, a0]
  have s5n : s₅.loc (gO C + 1) = knW C.sa s₀.mem (s₀.loc 0) := by rw [v5 1 (by simp), a1]
  have s5o : s₅.loc (gO C + 4) = koW C.sa s₀.mem (s₀.loc 0) + 2 := by rw [v5 4 (by simp), a4]
  have s5b : s₅.loc (gO C + 13) = rdW (s₀.mem.arr64 CTL) SCB * s₀.loc 0 := by
    rw [c13, m4, kzeroW_arr _ _ _ _ _ (Ne.symm (hsc _)), m3,
      Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm (hsc _)), s4_0]
  have s5H : s₅.loc (gO C + 2) = knW C.sa s₀.mem (s₀.loc 0) := by
    rw [c2, K4 _ (by omega) (by omega), a1]
  have s5m : s₅.mem = kzM C.sa (s₀.loc 0) s₀.mem := by
    rw [m5, m4, s3_0, b6, b7, m3]; rfl
  -- the sweep
  have hT : ktopM C.sa (ghC C) (s₀.loc 0) s₀.mem = (s₆.mem, mkOf C s₆) := by
    rw [m6, mk6, s5_0, s5N, s5n, s5o, s5b, s5H, mk5, s5m]; rfl
  -- the first range
  have s7v : ∀ i : Nat, i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 13 ∨ i = 18 ∨ i = 19 ∨ i = 20 →
      s₇.loc (gO C + i) = s₆.loc (gO C + i) := fun i hi => by
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact K7 _ (by omega) (by omega)
  have s6v : ∀ i : Nat, i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 13 → s₆.loc (gO C + i) = s₅.loc (gO C + i) :=
    fun i hi => by
      rcases hi with rfl | rfl | rfl | rfl
      · exact e6
      · exact f6
      · exact o6
      · exact t6
  have s7v0 : s₇.loc (gO C) = s₆.loc (gO C) := by simpa using s7v 0 (by simp)
  have s6v0 : s₆.loc (gO C) = s₅.loc (gO C) := e6
  have g19 : gmap C 19 = gO C + 18 := by simp [gmap]
  have g21 : gmap C 21 = gO C + 20 := by simp [gmap]
  simp only [g19, d2, d7, s7v0, s7v 4 (by simp), s7v 13 (by simp),
    s7v 18 (by simp), s7_0, m7, s6v0, s6v 1 (by simp), s6v 4 (by simp),
    s6v 13 (by simp)] at w8
  -- the second range
  have s9v : ∀ i : Nat, i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 13 ∨ i = 20 →
      s₉.loc (gO C + i) = s₈.loc (gO C + i) := fun i hi => by
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact K9 _ (by omega) (by omega)
  have s9v0 : s₉.loc (gO C) = s₈.loc (gO C) := by simpa using s9v 0 (by simp)
  simp only [g21, g2, g7, s9v0, s9v 4 (by simp), s9v 13 (by simp),
    s9v 20 (by simp), t0, m9, H8 (gO C + 19) (by omega), H8 (gO C + 20) (by omega), e8, f8, o8, t8, s7v0,
    s7v 1 (by simp), s7v 4 (by simp), s7v 13 (by simp), s7v 19 (by simp), s7v 20 (by simp),
    s6v0, s6v 1 (by simp), s6v 4 (by simp), s6v 13 (by simp)] at w10
  rw [kgrowM, ite_eq_right hc, hT]
  simp only [mkOf]
  rw [← s5N, ← s5n, ← s5o, ← s5b, w8, Option.bind_some]
  exact w10


end L.Arena
