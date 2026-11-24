module

public import ConAgua.Arena.FreezeView
public import ConAgua.Arena.FreezeCmp
import all ConAgua.Arena.FreezeCmp
import all ConAgua.Arena.Freeze
import ConAgua.L.Blocks

@[expose] public section

/-!
# `cmp_hdr_s`'s run (lane compare, design (i))

`cmp_hdr_s(lc)` (`Arena/FreezeCmp.lean`) on the memory `M` after `par_compact(1, hdrW)`:
`cmpHdrSMem M lc`: header S's entries from header C's (`hsMem`), the solution's images
(`xsGo`: the seed, `SFIRSTS`, `SDECL`, `SDLP`), the seed's patches (`seedMem`), header S's words
(`hsTail`). `cmpHdrS_spec`: a returning call ends there, having stayed in bounds (`CmpHdrSOK`).
-/

namespace L.Arena

open L
open Std.WP
open scoped Lean.Order

/-! ## Statements of one step -/

theorem step_seq_normal {p : Prog} {f : Stmt → M Sig} (a rest : Stmt) (s s' : St)
    (h : (step p f a).run s = .ok (.normal, s')) :
    (step p f (.seq a rest)).run s = (step p f rest).run s' := by
  simp only [step, StateT.run_bind, h]; rfl

/-- A store whose index evaluates to `iw` and whose value evaluates to `w` if `P` (else `oob`). -/
theorem step_st64_seq {p : Prog} {f : Stmt → M Sig} (a : ArrId) (ie v : Expr) (rest : Stmt) (s : St)
    (iw w : Word) (P : Prop) [Decidable P] (hi : (evalE ie).run s = .ok (iw, s))
    (hv : (evalE v).run s = if P then .ok (w, s) else .error .oob) :
    (step p f (.seq (.st64 a ie v) rest)).run s =
      if P ∧ iw.toNat < (s.mem.arr64 a).size then
        (step p f rest).run { s with mem := s.mem.set64 a iw w }
      else .error .oob := by
  have e : ∀ {α : Type} (x : α) (g : α → Except Err (Sig × St)), (Except.ok x >>= g) = g x := fun _ _ => rfl
  simp only [step, StateT.run_bind, hi, e]
  by_cases hP : P
  · simp only [hv, hP, ite_true, e]
    by_cases h : iw.toNat < (s.mem.arr64 a).size
    · simp [h, L.st64]
    · simp [h, L.st64]
  · simp only [hv, hP, ite_false, false_and]; rfl

theorem step_st64_one {p : Prog} {f : Stmt → M Sig} (a : ArrId) (ie v : Expr) (s : St)
    (iw w : Word) (hi : (evalE ie).run s = .ok (iw, s)) (hv : (evalE v).run s = .ok (w, s))
    (hb : iw.toNat < (s.mem.arr64 a).size) :
    (step p f (.st64 a ie v)).run s = .ok (.normal, { s with mem := s.mem.set64 a iw w }) := by
  have e : ∀ {α β : Type} (x : α) (g : α → Except Err β), (Except.ok x >>= g) = g x := fun _ _ => rfl
  simp only [step, StateT.run_bind, hi, e, hv]
  simp [hb, L.st64]; rfl

theorem evalE_c (k : Nat) (s : St) : (evalE (fzC k)).run s = .ok (k.toUInt64, s) := rfl

theorem evalE_ldc (a : ArrId) (k : Nat) (s : St) (h : k < (s.mem.arr64 a).size) (hk : k < 2 ^ 64) :
    (evalE (.ld64 a (fzC k))).run s = .ok (rd64 s.mem a k.toUInt64, s) := by
  have := evalE_ld_run a k s
  simp only [fzC]
  rw [this, if_pos (by rw [toNat_hdr k hk]; exact h)]

/-! ## Header S's entries from header C's -/

/-- Header S's entry `i` (the reads of header C's words in `M`). -/
def hsStep (M : Mem) (i : Nat) : Mem :=
  match hsE i with
  | .same j => (M.set64 OUT (10 + 2 * i).toUInt64 (rd64 M OUT (hdrW + (10 + 2 * j)).toUInt64 + hdrW.toUInt64)).set64
      OUT (11 + 2 * i).toUInt64 (rd64 M OUT (hdrW + (11 + 2 * j)).toUInt64)
  | .extra => M

/-- Header S's entries `is`. -/
def hsMem (M : Mem) : List Nat → Mem
  | [] => M
  | i :: is => hsMem (hsStep M i) is

theorem evalE_hcW_add (k : Nat) (s : St) (h : hdrW + k < (s.mem.arr64 OUT).size) (hk : hdrW + k < 2 ^ 64) :
    (evalE (.bin .add (hcW k) (fzC hdrW))).run s =
      .ok (rd64 s.mem OUT (hdrW + k).toUInt64 + hdrW.toUInt64, s) := by
  have e : ∀ {α β : Type} (x : α) (g : α → Except Err β), (Except.ok x >>= g) = g x := fun _ _ => rfl
  have h1 := evalE_ldc OUT (hdrW + k) s h hk
  have ex : evalE (.bin .add (hcW k) (fzC hdrW)) =
      (do let a ← evalE (hcW k); let b ← evalE (fzC hdrW); pure (BinOp.add.eval a b)) := rfl
  rw [ex]
  simp only [StateT.run_bind, hcW, h1, e, evalE_c]
  rfl

theorem hsE_all : (List.range frozen.length).all (fun i => match hsE i with
    | .same j => decide (j < frozen.length) | .extra => true) = true := by
  decide +kernel

theorem hsE_lt {i : Nat} (hi : i < frozen.length) (j : Nat) (hj : hsE i = .same j) : j < frozen.length := by
  have := List.all_eq_true.mp hsE_all i (List.mem_range.mpr hi)
  rw [hj] at this; simpa using this

theorem OutFrame.hsStep (M : Mem) (i : Nat) : OutFrame M (hsStep M i) := by
  unfold L.Arena.hsStep
  split
  · exact (OutFrame.set64 _ _ _).trans (OutFrame.set64 _ _ _)
  · exact OutFrame.refl _

theorem OutFrame.hsMem : ∀ (M : Mem) (is : List Nat), OutFrame M (hsMem M is)
  | _, [] => OutFrame.refl _
  | M, i :: is => (OutFrame.hsStep M i).trans (OutFrame.hsMem _ is)

theorem rd64_set64_lt (M : Mem) (a : ArrId) (i v j : Word) (h : i ≠ j) :
    rd64 (M.set64 a i v) a j = rd64 M a j := by
  simp only [rd64, getD_set64_same]
  rw [if_neg (fun e => h (UInt64.toNat_inj.mp e.1.symm))]

/-- **Header S's entry `i` runs as `hsStep`** (the words of both headers in bounds). -/
theorem hsStmt_run {p : Prog} {f : Stmt → M Sig} (i : Nat) (hi : i < frozen.length) (s : St)
    (hsz : 2 * hdrW ≤ (s.mem.arr64 OUT).size) :
    (step p f (hsStmt i)).run s = .ok (.normal, { s with mem := hsStep s.mem i }) := by
  have hfl := frozen_length
  have hhw := hdrW_eq
  unfold hsStmt hsStep
  cases hj : hsE i with
  | same j =>
    have hj' := hsE_lt hi j hj
    simp only
    rw [step_seq_normal _ _ s _ (step_st64_one _ _ _ s _ _ (evalE_c _ s)
        (evalE_hcW_add _ s (by omega) (by omega)) (by rw [toNat_hdr _ (by omega)]; omega))]
    apply step_st64_one _ _ _ _ _ _ (evalE_c _ _)
    · simp only [hcW]
      rw [evalE_ldc OUT (hdrW + (11 + 2 * j)) _ (by simp [L.Mem.size64_set64]; omega) (by omega),
        rd64_set64_lt _ _ _ _ _ (by
          intro e; have := congrArg UInt64.toNat e
          rw [toNat_hdr _ (by omega), toNat_hdr _ (by omega)] at this; omega)]
    · simp only [L.Mem.size64_set64]; rw [toNat_hdr _ (by omega)]; omega
  | extra => simp [step]; rfl

theorem seq_assoc_run {p : Prog} {f : Stmt → M Sig} (A B C : Stmt) (s : St) :
    (step p f (.seq (.seq A B) C)).run s = (step p f (.seq A (.seq B C))).run s := by
  simp only [step, StateT.run_bind]
  cases (step p f A).run s with
  | error e => rfl
  | ok r => obtain ⟨r, s'⟩ := r; cases r <;> rfl

/-- **Header S's entries run as `hsMem`.** -/
theorem hsFold_run {p : Prog} {f : Stmt → M Sig} (rest : Stmt) :
    ∀ (is : List Nat), (∀ i ∈ is, i < frozen.length) → ∀ (s : St), 2 * hdrW ≤ (s.mem.arr64 OUT).size →
    (step p f (.seq (is.foldr (fun i s => .seq (hsStmt i) s) .skip) rest)).run s =
      (step p f rest).run { s with mem := hsMem s.mem is }
  | [], _, s, _ => by
    rw [step_seq_normal _ _ s s (by simp [step]; rfl)]; rfl
  | i :: is, h, s, hsz => by
    rw [List.foldr_cons, seq_assoc_run, step_seq_normal _ _ s _ (hsStmt_run i (h i (by simp)) s hsz),
      hsFold_run rest is (fun j hj => h j (by simp [hj])) _ (by simp only; rw [(OutFrame.hsStep s.mem i).size]; exact hsz)]
    rfl

/-! ## The solution's images -/

/-- The images after header C's buffer: the seed, then `fzsImgs` (header entry, image). -/
def xsL : List (Nat × Fz) := (0, fzAt 0) :: fzsImgs

/-- The memory and the offset after the images `xs` from offset `o` (header at `OUT[0‥)`). -/
def xsGo : List (Nat × Fz) → Mem → Word → Mem × Word
  | [], M, o => (M, o)
  | (i, z) :: r, M, o => xsGo r (fzStep M 1 i z o 0) (o + fzEv M z.e)

/-- Every image of `xs` in bounds. -/
def xsOK : List (Nat × Fz) → Mem → Word → Bool
  | [], _, _ => true
  | (i, z) :: r, M, o => fzOK M 1 i z o 0 && xsOK r (fzStep M 1 i z o 0) (o + fzEv M z.e)

theorem OutFrame.xsGo : ∀ (xs : List (Nat × Fz)) (M : Mem) (o : Word), OutFrame M (xsGo xs M o).1
  | [], M, _ => OutFrame.refl M
  | (i, z) :: r, M, o => (OutFrame.fzStep M 1 i z o 0).trans (OutFrame.xsGo r _ _)

theorem xsL_ok : xsL.all (fun x => x.2.e.fzOk && x.2.src != OUT) = true := by decide +kernel

theorem fzsF_eq : ∀ x ∈ fzsImgs, fzsF x.1 = fzPreG x.2.src x.2.e x.1 := by
  intro x hx
  simp only [fzsImgs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> rfl

/-- **One image call** `o := f(o, 1, 0)` (`o` local `1`) of an image function `fzPreG`. -/
theorem step_call_fz {p : Prog} (n : Nat) (name : FnName) (z : Fz) (i : Nat)
    (hl : p.lookup name = some (fzPreG z.src z.e i)) (he : z.e.fzOk = true) (rest : Stmt) (s : St) :
    (step p (exec p (n + 1)) (.seq (.call [1] name [.var 1, fzC 1, fzC 0]) rest)).run s =
      if fzOK s.mem 1 i z (s.loc 1) 0 then
        (step p (exec p (n + 1)) rest).run
          ({ s with mem := fzStep s.mem 1 i z (s.loc 1) 0 }.setLoc 1 (s.loc 1 + fzEv s.mem z.e))
      else .error .oob := by
  have hrun := fzPreG_run (p := p) (f := name) (z := z) (i := i) hl he n s (s.loc 1) 1 0
  have e1 : Nat.toUInt64 1 = 1 := rfl
  have e0 : Nat.toUInt64 0 = 0 := rfl
  simp only [step, StateT.run_bind, evalArgs, evalE, fzC, StateT.run_get, pure_bind, StateT.run_pure, e1, e0, hrun]
  by_cases h1 : fzOK s.mem 1 i z (s.loc 1) 0 = true
  · simp only [h1, ite_true]; rfl
  · simp [h1]

/-- The calls of the solution's records' images. -/
def fzsCall (x : Nat × Fz) : Stmt := .call [1] (fzsName x.1) [.var 1, fzC 1, fzC 0]

/-- **The calls of `xs` (a part of `fzsImgs`) run as `xsGo`.** -/
theorem fzsCalls_run {p : Prog} (n : Nat) (hs : ∀ x ∈ fzsImgs, p.lookup (fzsName x.1) = some (fzsF x.1))
    (rest : Stmt) : ∀ (xs : List (Nat × Fz)), (∀ x ∈ xs, x ∈ fzsImgs) → ∀ (s : St),
    (step p (exec p (n + 1)) (.seq ((xs.map fzsCall).foldr .seq .skip) rest)).run s =
      if xsOK xs s.mem (s.loc 1) then
        (step p (exec p (n + 1)) rest).run
          ({ s with mem := (xsGo xs s.mem (s.loc 1)).1 }.setLoc 1 (xsGo xs s.mem (s.loc 1)).2)
      else .error .oob
  | [], _, s => by
    have : ({ s with mem := s.mem } : St).setLoc 1 (s.loc 1) = s := by
      cases s; simp only [St.setLoc]; congr 1; funext y; split <;> simp_all
    rw [step_seq_normal _ _ s s (by simp [step]; rfl)]
    simp [xsOK, xsGo, this]
  | (i, z) :: xs, h, s => by
    have hx := h (i, z) (by simp)
    have hok : z.e.fzOk = true ∧ z.src ≠ OUT := by
      have := List.all_eq_true.mp xsL_ok (i, z) (by simp [xsL, hx])
      simpa using this
    have hl : p.lookup (fzsName i) = some (fzPreG z.src z.e i) := by
      rw [hs _ hx, fzsF_eq _ hx]
    have ih := fzsCalls_run n hs rest xs (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.foldr_cons, fzsCall]
    have hseq : ∀ (A B C : Stmt), (step p (exec p (n + 1)) (.seq (.seq A B) C)).run s =
        (step p (exec p (n + 1)) (.seq A (.seq B C))).run s := by
      intro A B C; simp only [step, StateT.run_bind]
      cases (step p (exec p (n + 1)) A).run s with
      | error e => rfl
      | ok r => obtain ⟨r, s'⟩ := r; cases r <;> rfl
    rw [hseq, step_call_fz n _ z i hl hok.1]
    simp only [xsOK, xsGo, Bool.and_eq_true]
    by_cases h1 : fzOK s.mem 1 i z (s.loc 1) 0 = true
    · simp only [h1, true_and, ite_true]
      rw [show (List.map fzsCall xs).foldr Stmt.seq Stmt.skip = (List.map fzsCall xs).foldr Stmt.seq Stmt.skip from rfl]
      have := ih ({ s with mem := fzStep s.mem 1 i z (s.loc 1) 0 }.setLoc 1 (s.loc 1 + fzEv s.mem z.e))
      simp only [L.St.setLoc_mem, St.setLoc_loc, ite_true] at this
      rw [this]
      simp [St.setLoc_loc_same]
    · simp [h1]

/-! ## The seed's patches and header S's words -/

/-- The seed's word `k` (at `OUT[so + k]`) from `SCTL[k]`. -/
def seedPut (so : Word) (M : Mem) (k : Nat) : Mem :=
  M.set64 OUT (so + k.toUInt64) (rd64 M L.Checker.SCTL k.toUInt64)

/-- **The seed's patches** (the seed image at `OUT[so‥)`): word `128` := `CTL[225]` (the solution's
index counter), `162‥173` := `SCTL`'s, `224` := `0`. -/
def seedMem (M : Mem) (so : Word) : Mem :=
  (hsSeedW.foldl (seedPut so) (M.set64 OUT (so + Nat.toUInt64 128) (rd64 M CTL (Nat.toUInt64 225)))).set64
    OUT (so + Nat.toUInt64 224) (Nat.toUInt64 0)

/-- The seed's patches in bounds. -/
def SeedOK (M : Mem) (so : Word) : Prop :=
  (so + Nat.toUInt64 128).toNat < (M.arr64 OUT).size ∧ (Nat.toUInt64 225).toNat < (M.arr64 CTL).size ∧
    (∀ k ∈ hsSeedW, (so + k.toUInt64).toNat < (M.arr64 OUT).size ∧ (k.toUInt64).toNat < (M.arr64 L.Checker.SCTL).size) ∧
    (so + Nat.toUInt64 224).toNat < (M.arr64 OUT).size

/-- **Header S's words** `0`‥`5`, `8`, `9`. -/
def hsTail (M : Mem) (o : Word) : Mem :=
  (((((((M.set64 OUT (Nat.toUInt64 0) fzMagic).set64 OUT (Nat.toUInt64 1) o).set64 OUT (Nat.toUInt64 2)
    (rd64 M L.Checker.SDECL (Nat.toUInt64 0))).set64 OUT (Nat.toUInt64 3) (rd64 M CTL (Nat.toUInt64 225))).set64
    OUT (Nat.toUInt64 4) frozen.length.toUInt64).set64 OUT (Nat.toUInt64 5) hdrW.toUInt64).set64 OUT
    (Nat.toUInt64 8) (Nat.toUInt64 0)).set64 OUT (Nat.toUInt64 9) hdrW.toUInt64

/-- Header S's loads in bounds (in the memory before the seed's patches: they write only `OUT`). -/
def TailOK (M : Mem) : Prop :=
  (Nat.toUInt64 0).toNat < (M.arr64 L.Checker.SDECL).size ∧ (Nat.toUInt64 225).toNat < (M.arr64 CTL).size

/-- The images' memory and the buffer's whole length. -/
def hsImgs (M : Mem) (lc : Word) : Mem × Word :=
  xsGo xsL (hsMem M (List.range frozen.length)) (hdrW.toUInt64 + lc)

/-- **The memory after `cmp_hdr_s(lc)`.** -/
def cmpHdrSMem (M : Mem) (lc : Word) : Mem :=
  hsTail (seedMem (hsImgs M lc).1 (hdrW.toUInt64 + lc)) (hsImgs M lc).2

/-- **`cmp_hdr_s(lc)` stayed in bounds.** -/
def CmpHdrSOK (M : Mem) (lc : Word) : Prop :=
  xsOK xsL (hsMem M (List.range frozen.length)) (hdrW.toUInt64 + lc) = true ∧
    SeedOK (hsImgs M lc).1 (hdrW.toUInt64 + lc) ∧ TailOK (hsImgs M lc).1

theorem evalE_ldf (a : ArrId) (k : Nat) (s : St) :
    (evalE (.ld64 a (fzC k))).run s =
      if k.toUInt64.toNat < (s.mem.arr64 a).size then .ok (rd64 s.mem a k.toUInt64, s) else .error .oob :=
  evalE_ld_run a k s

theorem evalE_ctl (k : Nat) (s : St) :
    (evalE (fzCtl k)).run s =
      if k.toUInt64.toNat < (s.mem.arr64 CTL).size then .ok (rd64 s.mem CTL k.toUInt64, s) else .error .oob :=
  evalE_ld_run CTL k s

theorem evalE_add_var (x : Var) (k : Nat) (s : St) :
    (evalE (.bin .add (.var x) (fzC k))).run s = .ok (s.loc x + k.toUInt64, s) := by
  simp [evalE, fzC, BinOp.eval]; rfl

/-- **The seed's patches from `SCTL`** (`so` local `2`). -/
theorem seedFold_run {p : Prog} {f : Stmt → M Sig} (rest : Stmt) : ∀ (ks : List Nat) (s : St),
    (step p f (.seq ((ks.map fun k => Stmt.st64 OUT (.bin .add (.var 2) (fzC k))
      (.ld64 L.Checker.SCTL (fzC k))).foldr .seq .skip) rest)).run s =
      if (∀ k ∈ ks, (s.loc 2 + k.toUInt64).toNat < (s.mem.arr64 OUT).size ∧
          (k.toUInt64).toNat < (s.mem.arr64 L.Checker.SCTL).size) then
        (step p f rest).run { s with mem := ks.foldl (seedPut (s.loc 2)) s.mem }
      else .error .oob
  | [], s => by
    rw [step_seq_normal _ _ s s (by simp [step]; rfl)]
    simp
  | k :: ks, s => by
    simp only [List.map_cons, List.foldr_cons]
    rw [seq_assoc_run, step_st64_seq _ _ _ _ s _ _ _ (evalE_add_var 2 k s) (evalE_ldf _ k s)]
    have ih := seedFold_run (p := p) (f := f) rest ks { s with mem := (s.mem.set64 OUT (s.loc 2 + k.toUInt64)
      (rd64 s.mem L.Checker.SCTL k.toUInt64)) }
    simp only [L.Mem.size64_set64] at ih
    by_cases h1 : k.toUInt64.toNat < (s.mem.arr64 L.Checker.SCTL).size ∧
        (s.loc 2 + k.toUInt64).toNat < (s.mem.arr64 OUT).size
    · rw [if_pos h1, ih]
      simp only [List.foldl_cons, seedPut, List.forall_mem_cons]
      by_cases h2 : ∀ x ∈ ks, (s.loc 2 + x.toUInt64).toNat < (s.mem.arr64 OUT).size ∧
          x.toUInt64.toNat < (s.mem.arr64 L.Checker.SCTL).size
      · rw [if_pos h2, if_pos ⟨⟨h1.2, h1.1⟩, h2⟩]
      · rw [if_neg h2, if_neg (fun h => h2 h.2)]
    · rw [if_neg h1, if_neg (fun h => h1 ⟨(List.forall_mem_cons.mp h).1.2, (List.forall_mem_cons.mp h).1.1⟩)]

/-- Header S's words, then the length. -/
def hsTailS : Stmt :=
  .seq (.st64 OUT (fzC 0) (.const fzMagic)) <|
  .seq (.st64 OUT (fzC 1) (.var 1)) <|
  .seq (.st64 OUT (fzC 2) (.ld64 L.Checker.SDECL (fzC 0))) <|
  .seq (.st64 OUT (fzC 3) (fzCtl 225)) <|
  .seq (.st64 OUT (fzC 4) (fzC frozen.length)) <|
  .seq (.st64 OUT (fzC 5) (fzC hdrW)) <|
  .seq (.st64 OUT (fzC 8) (fzC 0)) <|
  .seq (.st64 OUT (fzC 9) (fzC hdrW)) <|
  .ret [.var 1]

/-- `cmp_hdr_s`'s body after `o := hdrW + lc` and header S's entries. -/
def hsRest : Stmt :=
  .seq (.set 2 (.var 1)) <|
  .seq (.call [1] (fzName 0) [.var 1, fzC 1, fzC 0]) <|
  .seq ((fzsImgs.map fzsCall).foldr .seq .skip) <|
  .seq (.st64 OUT (.bin .add (.var 2) (fzC 128)) (fzCtl 225)) <|
  .seq ((hsSeedW.map fun k => Stmt.st64 OUT (.bin .add (.var 2) (fzC k)) (.ld64 L.Checker.SCTL (fzC k))).foldr
    .seq .skip) <|
  .seq (.st64 OUT (.bin .add (.var 2) (fzC 224)) (fzC 0)) <|
  hsTailS

theorem cmpHdrSL_eq : cmpHdrSL = { nparams := 1, nlocals := 3, body := (Stmt.seq
    (.set 1 (.bin .add (fzC hdrW) (.var 0)))
    (.seq ((List.range frozen.length).foldr (fun i s => .seq (hsStmt i) s) .skip) hsRest)) } := by
  unfold cmpHdrSL; rfl

theorem ite_ok {β : Type} {c : Prop} [Decidable c] {a : Except Err β} {x : β}
    (h : (if c then a else .error .oob) = .ok x) : c ∧ a = .ok x := by
  by_cases hc : c
  · rw [if_pos hc] at h; exact ⟨hc, h⟩
  · rw [if_neg hc] at h; cases h

theorem evalE_c_if (k : Nat) (s : St) : (evalE (fzC k)).run s = if True then .ok (k.toUInt64, s) else .error .oob := rfl
theorem evalE_const_if (w : Word) (s : St) :
    (evalE (.const w)).run s = if True then .ok (w, s) else .error .oob := rfl
theorem evalE_var_if (x : Var) (s : St) :
    (evalE (.var x)).run s = if True then .ok (s.loc x, s) else .error .oob := rfl

theorem OutFrame.seedFold (so : Word) : ∀ (ks : List Nat) (M : Mem), OutFrame M (ks.foldl (seedPut so) M)
  | [], M => OutFrame.refl M
  | k :: ks, M => (OutFrame.set64 M _ _).trans (OutFrame.seedFold so ks _)

/-- **`cmp_hdr_s`'s body**: a run that returns stayed in bounds, ends in `cmpHdrSMem` and returns
the whole buffer's length (`lc` local `0`; header C's words in bounds). -/
theorem cmpHdrS_body {p : Prog} (n : Nat) (h0 : p.lookup (fzName 0) = some (fzF 0))
    (hs : ∀ x ∈ fzsImgs, p.lookup (fzsName x.1) = some (fzsF x.1)) (s : St)
    (hsz : 2 * hdrW ≤ (s.mem.arr64 OUT).size) (sig : Sig) (s2 : St)
    (h : (step p (exec p (n + 1)) cmpHdrSL.body).run s = .ok (sig, s2)) :
    CmpHdrSOK s.mem (s.loc 0) ∧ s2.mem = cmpHdrSMem s.mem (s.loc 0) ∧
      sig = .ret [(hsImgs s.mem (s.loc 0)).2] := by
  rw [cmpHdrSL_eq] at h
  simp only at h
  rw [step_seq_normal _ _ s (s.setLoc 1 (hdrW.toUInt64 + s.loc 0))
    (by simp [step, evalE, fzC, BinOp.eval, setLoc]; rfl)] at h
  rw [hsFold_run hsRest _ (fun i hi => List.mem_range.mp hi) _ (by simp only [L.St.setLoc_mem]; exact hsz)] at h
  generalize hlc : s.loc 0 = lc at *
  simp only [L.St.setLoc_mem] at h
  generalize hM1 : hsMem s.mem (List.range frozen.length) = M1 at h
  generalize hL1 : (s.setLoc 1 (hdrW.toUInt64 + lc)).loc = L1 at h
  have hL11 : L1 1 = hdrW.toUInt64 + lc := by rw [← hL1]; simp [St.setLoc]
  simp only [hsRest] at h
  rw [step_seq_normal _ _ _ (({ mem := M1, loc := L1 } : St).setLoc 2 (hdrW.toUInt64 + lc))
    (by simp [step, evalE, setLoc, hL11]; rfl)] at h
  generalize hS2 : ({ mem := M1, loc := L1 } : St).setLoc 2 (hdrW.toUInt64 + lc) = S2 at h
  have hS2m : S2.mem = M1 := by rw [← hS2]; rfl
  have hS21 : S2.loc 1 = hdrW.toUInt64 + lc := by rw [← hS2]; simp [St.setLoc, hL11]
  have hS22 : S2.loc 2 = hdrW.toUInt64 + lc := by rw [← hS2]; simp [St.setLoc]
  have hz0 := fzAt_ok (i := 0) (by decide)
  rw [step_call_fz n _ (fzAt 0) 0 (by rw [h0, fzF_eq (by decide)]) hz0.1, hS2m, hS21] at h
  obtain ⟨hx0, h⟩ := ite_ok h
  generalize hS3 : ({ S2 with mem := fzStep M1 1 0 (fzAt 0) (hdrW.toUInt64 + lc) 0 }.setLoc 1
    (hdrW.toUInt64 + lc + fzEv M1 (fzAt 0).e)) = S3 at h
  have hS3m : S3.mem = fzStep M1 1 0 (fzAt 0) (hdrW.toUInt64 + lc) 0 := by rw [← hS3]; rfl
  have hS31 : S3.loc 1 = hdrW.toUInt64 + lc + fzEv M1 (fzAt 0).e := by rw [← hS3]; simp [St.setLoc]
  have hS32 : S3.loc 2 = hdrW.toUInt64 + lc := by rw [← hS3]; simp [St.setLoc, hS22]
  rw [fzsCalls_run n hs _ fzsImgs (fun _ h => h) S3, hS3m, hS31] at h
  obtain ⟨hx1, h⟩ := ite_ok h
  have hX : xsGo xsL M1 (hdrW.toUInt64 + lc) = xsGo fzsImgs (fzStep M1 1 0 (fzAt 0) (hdrW.toUInt64 + lc) 0)
      (hdrW.toUInt64 + lc + fzEv M1 (fzAt 0).e) := rfl
  have hXok : xsOK xsL M1 (hdrW.toUInt64 + lc) = true := by
    simp only [xsL, xsOK, hx0, hx1, Bool.and_self]
  rw [← hX] at h
  generalize hX4 : xsGo xsL M1 (hdrW.toUInt64 + lc) = X4 at h
  generalize hS4 : ({ S3 with mem := X4.1 }.setLoc 1 X4.2) = S4 at h
  have hS4m : S4.mem = X4.1 := by rw [← hS4]; rfl
  have hS41 : S4.loc 1 = X4.2 := by rw [← hS4]; simp [St.setLoc]
  have hS42 : S4.loc 2 = hdrW.toUInt64 + lc := by rw [← hS4]; simp [St.setLoc, hS32]
  -- the seed's word 128
  rw [step_st64_seq _ _ _ _ S4 _ _ _ (evalE_add_var 2 128 S4) (evalE_ctl 225 S4)] at h
  obtain ⟨hs128, h⟩ := ite_ok h
  rw [seedFold_run] at h
  obtain ⟨hsW, h⟩ := ite_ok h
  rw [step_st64_seq _ _ _ _ _ _ _ _ (evalE_add_var 2 224 _) (evalE_c_if 0 _)] at h
  obtain ⟨hs224, h⟩ := ite_ok h
  simp only [hsTailS] at h
  rw [step_st64_seq _ _ _ _ _ _ _ _ (evalE_c _ _) (evalE_const_if _ _)] at h
  obtain ⟨ht0, h⟩ := ite_ok h
  rw [step_st64_seq _ _ _ _ _ _ _ _ (evalE_c _ _) (evalE_var_if _ _)] at h
  obtain ⟨ht1, h⟩ := ite_ok h
  rw [step_st64_seq _ _ _ _ _ _ _ _ (evalE_c _ _) (evalE_ldf _ _ _)] at h
  obtain ⟨ht2, h⟩ := ite_ok h
  rw [step_st64_seq _ _ _ _ _ _ _ _ (evalE_c _ _) (evalE_ctl _ _)] at h
  obtain ⟨ht3, h⟩ := ite_ok h
  rw [step_st64_seq _ _ _ _ _ _ _ _ (evalE_c _ _) (evalE_c_if _ _)] at h
  obtain ⟨ht4, h⟩ := ite_ok h
  rw [step_st64_seq _ _ _ _ _ _ _ _ (evalE_c _ _) (evalE_c_if _ _)] at h
  obtain ⟨ht5, h⟩ := ite_ok h
  rw [step_st64_seq _ _ _ _ _ _ _ _ (evalE_c _ _) (evalE_c_if _ _)] at h
  obtain ⟨ht8, h⟩ := ite_ok h
  rw [step_st64_seq _ _ _ _ _ _ _ _ (evalE_c _ _) (evalE_c_if _ _)] at h
  obtain ⟨ht9, h⟩ := ite_ok h
  have hret : ∀ (S : St), (step p (exec p (n + 1)) (.ret [.var 1])).run S = .ok (.ret [S.loc 1], S) :=
    fun _ => rfl
  rw [hret] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hI : hsImgs s.mem lc = X4 := by rw [hsImgs, hM1, hX4]
  rw [hS4m, hS41, hS42] at *
  have hF5 := OutFrame.seedFold (hdrW.toUInt64 + lc) hsSeedW (X4.1.set64 OUT (hdrW.toUInt64 + lc + Nat.toUInt64 128)
    (rd64 X4.1 CTL (Nat.toUInt64 225)))
  have hO : ∀ a, ((hsSeedW.foldl (seedPut (hdrW.toUInt64 + lc)) (X4.1.set64 OUT (hdrW.toUInt64 + lc + Nat.toUInt64 128)
      (rd64 X4.1 CTL (Nat.toUInt64 225)))).arr64 a).size = (X4.1.arr64 a).size := fun a => by
    rw [hF5.size, L.Mem.size64_set64]
  have hA : ∀ a : TieredArray, a ≠ OUT → (hsSeedW.foldl (seedPut (hdrW.toUInt64 + lc))
      (X4.1.set64 OUT (hdrW.toUInt64 + lc + Nat.toUInt64 128) (rd64 X4.1 CTL (Nat.toUInt64 225)))).arr64 a =
      X4.1.arr64 a := fun a ha => by rw [hF5.arr a ha, Mem.arr64_set64_ne _ _ _ _ _ ha]
  rw [hO] at hs224
  simp only [L.Mem.size64_set64, Mem.arr64_set64_ne _ _ _ _ _ (show (L.Checker.SCTL : TieredArray) ≠ OUT by decide)]
    at hsW
  simp only [Mem.arr64_set64_ne _ _ _ _ _ (show (L.Checker.SDECL : TieredArray) ≠ OUT by decide),
    Mem.arr64_set64_ne _ _ _ _ _ (show (CTL : TieredArray) ≠ OUT by decide),
    hA _ (show (L.Checker.SDECL : TieredArray) ≠ OUT by decide), hA _ (show (CTL : TieredArray) ≠ OUT by decide)]
    at ht2 ht3
  refine ⟨⟨by rw [hM1]; exact hXok, ?_, ?_⟩, ?_, ?_⟩
  · rw [hI]; exact ⟨hs128.2, hs128.1, hsW, hs224.2⟩
  · rw [hI]; exact ⟨ht2.1, ht3.1⟩
  · rw [cmpHdrSMem, hI]
    simp only [hsTail, seedMem, rd64_set64_out _ L.Checker.SDECL (by decide), rd64_set64_out _ CTL (by decide)]
  · rw [hI]

theorem step_call_zero {p : Prog} {xs : List Var} {f : FnName} {fd : FunDecl} {args : List Expr}
    (hl : p.lookup f = some fd) (rest : Stmt) (s : St) (v : Sig × St)
    (h : (step p (exec p 0) (.seq (.call xs f args) rest)).run s = .ok v) : False := by
  simp [step, StateT.run_bind, invoke, lookupFn, hl, callFn, exec] at h
  revert h
  cases (StateT.run (evalArgs args) s) <;> intro h <;> cases h

/-- **`cmp_hdr_s(lc)` as a triple** (any fuel): a returning call keeps the caller's locals and,
with header C's words in bounds, stayed in bounds, ends in `cmpHdrSMem` and returns the whole
buffer's length. -/
theorem cmpHdrS_spec {p : Prog} (hp : p.lookup "cmp_hdr_s" = some cmpHdrSL)
    (h0 : p.lookup (fzName 0) = some (fzF 0))
    (hs : ∀ x ∈ fzsImgs, p.lookup (fzsName x.1) = some (fzsF x.1)) (n : Nat) (s₀ : St) (lc : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cmp_hdr_s" [lc]
    ⦃fun r s' => LocEq s' s₀ ∧ (2 * hdrW ≤ (s₀.mem.arr64 OUT).size →
      CmpHdrSOK s₀.mem lc ∧ s'.mem = cmpHdrSMem s₀.mem lc ∧ r = [(hsImgs s₀.mem lc).2]); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs0 hrun
  subst hs0
  rw [invoke_eq _ hp] at hrun
  unfold callFn at hrun
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind, StateT.run_modify] at hrun
  generalize hB : (exec p n cmpHdrSL.body).run ({ mem := s.mem, loc := Locals.init [lc] } : St) = B at hrun
  cases B with
  | error e => cases hrun
  | ok v =>
    obtain ⟨sig, s2⟩ := v
    simp only [StateT.run_pure] at hrun
    have hrun' : (sig.retVal, ({ mem := s2.mem, loc := s.loc } : St)) = (r, s') := by
      exact Except.ok.inj hrun
    simp only [Prod.mk.injEq] at hrun'
    obtain ⟨rfl, rfl⟩ := hrun'
    refine ⟨rfl, fun hsz => ?_⟩
    match n with
    | 0 => cases hB
    | 1 =>
      exfalso
      change (step p (exec p 0) cmpHdrSL.body).run _ = _ at hB
      rw [cmpHdrSL_eq] at hB
      simp only at hB
      rw [step_seq_normal _ _ _ _ (by simp [step, evalE, fzC, BinOp.eval, setLoc]; rfl),
        hsFold_run hsRest _ (fun i hi => List.mem_range.mp hi) _ (by simp only [L.St.setLoc_mem]; exact hsz)] at hB
      simp only [hsRest] at hB
      rw [step_seq_normal _ _ _ _ (by simp [step, evalE, setLoc]; rfl)] at hB
      exact step_call_zero h0 _ _ _ hB
    | n + 2 =>
      have := cmpHdrS_body n h0 hs { mem := s.mem, loc := Locals.init [lc] } hsz sig s2 hB
      have e0 : Locals.init [lc] 0 = lc := rfl
      simp only [e0] at this
      obtain ⟨h1, h2, h3⟩ := this
      exact ⟨h1, h2, by rw [h3]; rfl⟩

end L.Arena
