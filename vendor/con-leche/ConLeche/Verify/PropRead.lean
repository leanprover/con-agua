module

public import ConLeche.Kernel.PropRead
public import ConLeche.Verify.Shift

public section

/-!
# The head-symbol prop-ness readers under the verification walks
(task #168)

The readers (`ConLeche/Kernel/PropRead.lean`) look only at head symbols,
arities, stored types and the residual sorts of declared types, none of
which a free-variable shift changes the shape of — so every reader
commutes with `shiftFrom`, which is all the deep-embedding lemma family
(`ConLeche/Verify/Deep.lean`) needs of them.
-/

namespace ConLeche

open Expr

theorem Expr.numArgs_shiftFrom {p : Nat} :
    ∀ (e : Expr), (shiftFrom p e).numArgs = e.numArgs := by
  intro e
  induction e <;> simp_all [shiftFrom, numArgs]
  case fvar => split <;> rfl

/-- `getD` through a mapped list, the default mapped too. -/
theorem List.getD_map_shiftFrom {p : Nat} (l : List Expr) (i : Nat) (d : Expr) :
    (l.map (shiftFrom p)).getD i (shiftFrom p d) = shiftFrom p (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map]

theorem unwrapIdDefs_succ_of_not_const (find? : Name → Option ConstantInfo) {k : Nat}
    {x : Expr} (h : ∀ c us, x.getAppFn ≠ .const c us) :
    unwrapIdDefs find? (k + 1) x = x := by
  simp only [unwrapIdDefs]

theorem shiftFrom_getAppFn_not_const {p : Nat} {e : Expr}
    (h : ∀ c us, e.getAppFn ≠ .const c us) :
    ∀ c us, (shiftFrom p e).getAppFn ≠ .const c us := by
  intro c us hc
  rw [getAppFn_shiftFrom] at hc
  cases hf : e.getAppFn <;> rw [hf] at hc <;> simp only [shiftFrom, reduceCtorEq] at hc
  case const c' us' => exact h c' us' hf
  case fvar => split at hc <;> exact nomatch hc

theorem unwrapIdDefs_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat} :
    ∀ (k : Nat) (e : Expr),
      unwrapIdDefs find? k (shiftFrom p e) = shiftFrom p (unwrapIdDefs find? k e) := by
  intro k
  induction k with
  | zero => intro e; rfl
  | succ k ih =>
    intro e
    by_cases hc : ∃ c us, e.getAppFn = .const c us
    · obtain ⟨c, us, hh⟩ := hc
      have hfn : (shiftFrom p e).getAppFn = .const c us := by
        rw [getAppFn_shiftFrom, hh]; rfl
      simp only [unwrapIdDefs, hfn, hh, getAppArgs_shiftFrom, List.length_map]
      cases find? c with
      | none => rfl
      | some ci =>
        cases ci <;> try rfl
        case defnInfo cv v hint =>
          dsimp only
          cases lamProj? 0 v with
          | none => rfl
          | some kj =>
            dsimp only
            split
            · rw [List.getD_map_shiftFrom, ih]
            · rfl
    · have hn : ∀ c us, e.getAppFn ≠ .const c us := fun c us h => hc ⟨c, us, h⟩
      rw [unwrapIdDefs_succ_of_not_const find? hn,
        unwrapIdDefs_succ_of_not_const find? (shiftFrom_getAppFn_not_const hn)]

theorem peelPisW_succ_eq (find? : Name → Option ConstantInfo) (n : Nat) (e : Expr) :
    peelPisW find? (n + 1) e =
      match unwrapIdDefs find? 4 e with
      | .forallE _ b => peelPisW find? n b
      | _ => none := by
  cases e with
  | forallE ty b =>
    rw [unwrapIdDefs_succ_of_not_const find? (by intro c us h; exact nomatch h)]
    rfl
  | _ => rfl

theorem peelPisW_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat} :
    ∀ (n : Nat) (e : Expr),
      peelPisW find? n (shiftFrom p e) = (peelPisW find? n e).map (shiftFrom p) := by
  intro n
  induction n with
  | zero => intro e; simp [peelPisW, unwrapIdDefs_shiftFrom]
  | succ n ih =>
    intro e
    rw [peelPisW_succ_eq, peelPisW_succ_eq, unwrapIdDefs_shiftFrom]
    cases unwrapIdDefs find? 4 e with
    | forallE ty b => simp only [shiftFrom, ih]
    | fvar idx ty => by_cases hp : idx ≥ p <;> simp [shiftFrom, hp]
    | _ => rfl

theorem residualPW_map_shiftFrom {p : Nat} (o : Option Expr) :
    residualPW (o.map (shiftFrom p)) = residualPW o := by
  match o with
  | none => rfl
  | some e =>
    cases e <;> try rfl
    case fvar => simp only [Option.map_some, shiftFrom]; split <;> rfl

theorem binderDom_shiftFrom {p : Nat} :
    ∀ (k : Nat) (e : Expr), (shiftFrom p e).binderDom k = (e.binderDom k).map (shiftFrom p) := by
  intro k e
  induction e generalizing k <;> cases k <;> simp_all [shiftFrom, binderDom]
  all_goals split <;> rfl

theorem headTypePW_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (root : Expr) (d : Nat) (h : Expr) (n : Nat) :
    headTypePW find? (shiftFrom p root) d (shiftFrom p h) n =
      headTypePW find? root d h n := by
  cases h <;> try rfl
  case fvar =>
    simp only [shiftFrom]
    split <;> simp only [headTypePW, peelPisW_shiftFrom, residualPW_map_shiftFrom]
  case bvar i =>
    simp only [shiftFrom, headTypePW, binderDom_shiftFrom]
    split <;> try rfl
    cases root.binderDom (d - 1 - i) <;>
      simp [peelPisW_shiftFrom, residualPW_map_shiftFrom]

theorem typeSortPWGo_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (root : Expr) :
    ∀ (R : Expr) (d : Nat),
      typeSortPWGo find? (shiftFrom p root) (shiftFrom p R) d =
        typeSortPWGo find? root R d := by
  intro R
  induction R with
  | forallE ty b _ ihb => intro d; simp only [shiftFrom, typeSortPWGo, ihb]
  | sort u => intro d; rfl
  | fvar idx ty =>
    intro d
    have h := headTypePW_shiftFrom find? (p := p) root d (.fvar idx ty) 0
    revert h
    simp only [shiftFrom]
    split <;> intro h <;> exact h
  | bvar i => intro d; exact headTypePW_shiftFrom find? root d (.bvar i) 0
  | const n us => intro d; exact headTypePW_shiftFrom find? root d (.const n us) 0
  | lam ty b => intro d; exact headTypePW_shiftFrom find? root d (.lam ty b) 0
  | letE ty v b => intro d; exact headTypePW_shiftFrom find? root d (.letE ty v b) 0
  | lit l => intro d; exact headTypePW_shiftFrom find? root d (.lit l) 0
  | proj sn i e => intro d; exact headTypePW_shiftFrom find? root d (.proj sn i e) 0
  | app f a =>
    intro d
    show headTypePW find? (shiftFrom p root) d (shiftFrom p (.app f a)).getAppFn
        (shiftFrom p (.app f a)).numArgs =
      headTypePW find? root d (Expr.app f a).getAppFn (Expr.app f a).numArgs
    rw [numArgs_shiftFrom, getAppFn_shiftFrom, headTypePW_shiftFrom]

theorem typeSortPW_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (T : Expr) :
    typeSortPW find? (shiftFrom p T) = typeSortPW find? T :=
  typeSortPWGo_shiftFrom find? T T 0

theorem headProofPW_shiftFrom (find? : Name → Option ConstantInfo)
    (findTable? : Name → Option ProjTable) {p : Nat}
    (h : Expr) :
    headProofPW find? findTable? (shiftFrom p h) = headProofPW find? findTable? h := by
  cases h <;> try rfl
  case fvar =>
    simp only [shiftFrom]
    split <;> simp only [headProofPW, typeSortPW_shiftFrom]

theorem proofPW_shiftFrom (find? : Name → Option ConstantInfo)
    (findTable? : Name → Option ProjTable) {p : Nat} :
    ∀ (a : Expr), proofPW find? findTable? (shiftFrom p a) = proofPW find? findTable? a := by
  intro a
  induction a with
  | lam ty b _ ihb => simp only [shiftFrom, proofPW, ihb]
  | letE ty v b _ _ ihb => simp only [shiftFrom, proofPW, ihb]
  | app f x ihf _ => simp only [shiftFrom, proofPW, ihf]
  | fvar idx ty =>
    have h := headProofPW_shiftFrom find? findTable? (p := p) (.fvar idx ty)
    revert h
    simp only [shiftFrom]
    split <;> intro h <;> exact h
  | _ => rfl

theorem notProofFast_shiftFrom (find? : Name → Option ConstantInfo)
    (findTable? : Name → Option ProjTable) {p : Nat}
    (a : Expr) :
    notProofFast find? findTable? (shiftFrom p a) = notProofFast find? findTable? a := by
  simp only [notProofFast, proofPW_shiftFrom]

theorem isProofFast_shiftFrom (find? : Name → Option ConstantInfo)
    (findTable? : Name → Option ProjTable) {p : Nat}
    (a : Expr) :
    isProofFast find? findTable? (shiftFrom p a) = isProofFast find? findTable? a := by
  simp only [isProofFast, proofPW_shiftFrom]

/-! ## Inversions — what a reader's answer says about the term

The "yes" arm's justification (`prf_of_isProofFast`,
`ConLeche/Model/Rules/DefEqSoundKit.lean`) consumes
the readers through these. -/

theorem Expr.numArgs_eq_length : ∀ (e : Expr), e.numArgs = e.getAppArgs.length := by
  intro e
  induction e <;> simp_all [numArgs, getAppArgs]

theorem residualPW_some_inv {o : Option Expr} {pw : PropWhen}
    (h : residualPW o = some pw) :
    ∃ u, o = some (.sort u) ∧ pw = Level.zeronessOf u := by
  match o, h with
  | some (.sort u), h => exact ⟨u, rfl, (Option.some.inj h).symm⟩
  | none, h => exact nomatch h
  | some (.bvar _), h | some (.fvar _ _), h | some (.const _ _), h
  | some (.app _ _), h | some (.lam _ _), h | some (.forallE _ _), h
  | some (.letE _ _ _), h | some (.lit _), h | some (.proj _ _ _), h =>
    exact nomatch h

theorem isProofFast_inv (find? : Name → Option ConstantInfo)
    (findTable? : Name → Option ProjTable) {a : Expr}
    (h : isProofFast find? findTable? a = true) :
    ∃ pw, proofPW find? findTable? a = some pw ∧ pw.isProp = true := by
  unfold isProofFast at h
  cases hp : proofPW find? findTable? a with
  | none => rw [hp] at h; exact nomatch h
  | some pw => rw [hp] at h; exact ⟨pw, rfl, h⟩

@[simp] theorem PropWhen.isProp_never : PropWhen.isProp .never = false := by rfl

end ConLeche
