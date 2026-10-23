import ConRon.Arena.Frontend.ExportC

/-!
# The twin's parse only appends to `decls` (lane `pipeline`)

con-ron's frontend reads the parse state's tables (`names`, `levels`, `exprs`) and only ever
pushes to its `decls` (`pushDecl`). So a line applied to a state whose `decls` are prefixed by
`D` is the line applied to the state without them, with the result prefixed by `D`
(`applyLine_pre`). The checker parses the stream after the prelude with the prelude's records
still in `DECL` (`Checker/Prelude.lean`): its parse state is the twin's prefixed by them.
-/

namespace ConRon.Arena.Frontend

open ConLeche.Frontend (NameRec LevelRec ExprRec DeclRec LineRec IndTypeRec IndCtorRec IndRecRec)

/-- The parse state with `D` before its records. -/
def StateD.pre (D : Array IDeclaration) (st : StateD) : StateD := { st with decls := D ++ st.decls }

section
variable (D : Array IDeclaration) (st : StateD)

@[simp] theorem StateD.pre_names : (st.pre D).names = st.names := rfl
@[simp] theorem StateD.pre_levels : (st.pre D).levels = st.levels := rfl
@[simp] theorem StateD.pre_exprs : (st.pre D).exprs = st.exprs := rfl
@[simp] theorem StateD.pre_decls : (st.pre D).decls = D ++ st.decls := rfl

theorem StateD.name_pre : StateD.name (st.pre D) = StateD.name st := rfl
theorem StateD.level_pre : StateD.level (st.pre D) = StateD.level st := rfl
theorem StateD.expr_pre : StateD.expr (st.pre D) = StateD.expr st := rfl
theorem StateD.freshName_pre : StateD.freshName (st.pre D) = StateD.freshName st := rfl
theorem StateD.freshLevel_pre : StateD.freshLevel (st.pre D) = StateD.freshLevel st := rfl
theorem StateD.freshExpr_pre : StateD.freshExpr (st.pre D) = StateD.freshExpr st := rfl
theorem getDeclD_pre : getDeclD (st.pre D) = getDeclD st := rfl
theorem parseCVD_pre : parseCVD (st.pre D) = parseCVD st := rfl
theorem parseRuleD_pre : parseRuleD (st.pre D) = parseRuleD st := rfl
theorem validateIndD_pre : validateIndD (st.pre D) = validateIndD st := rfl

theorem pushDecl_pre (d : IDeclaration) :
    pushDecl (st.pre D) d = StateD.pre D <$> pushDecl st d := by
  simp only [pushDecl, map_pure, StateD.pre, Array.append_push]

theorem parseNameEntryD_pre (i : Nat) (r : NameRec) :
    parseNameEntryD (st.pre D) i r = StateD.pre D <$> parseNameEntryD st i r := by
  cases r <;> simp only [parseNameEntryD, StateD.name_pre, StateD.freshName_pre, map_bind,
    map_pure] <;> rfl

theorem parseLevelEntryD_pre (i : Nat) (r : LevelRec) :
    parseLevelEntryD (st.pre D) i r = StateD.pre D <$> parseLevelEntryD st i r := by
  cases r <;> simp only [parseLevelEntryD, StateD.level_pre, StateD.name_pre,
    StateD.freshLevel_pre, map_bind, map_pure] <;> rfl

theorem parseExprEntryD_pre (i : Nat) (r : ExprRec) :
    parseExprEntryD (st.pre D) i r = StateD.pre D <$> parseExprEntryD st i r := by
  cases r <;> simp only [parseExprEntryD, StateD.level_pre, StateD.name_pre, StateD.expr_pre,
    StateD.freshExpr_pre, map_bind, map_pure] <;> rfl

theorem installIndD_pre (tys : List IndTypeRec) (cts : List IndCtorRec) (rcs : List IndRecRec)
    (nPd : Nat) :
    installIndD (st.pre D) tys cts rcs nPd = StateD.pre D <$> installIndD st tys cts rcs nPd := by
  simp only [installIndD, parseCVD_pre, parseRuleD_pre, pushDecl_pre, map_bind]

/-- `Sum.map` on the state. -/
def preL (D : Array IDeclaration) : StateD ⊕ RecordVerdict → StateD ⊕ RecordVerdict :=
  Sum.map (StateD.pre D) id

theorem processLineCoreD_pre (d : DeclRec) :
    processLineCoreD (st.pre D) d = preL D <$> processLineCoreD st d := by
  cases d <;> simp only [processLineCoreD, parseCVD_pre, getDeclD_pre, validateIndD_pre,
    pushDecl_pre, installIndD_pre, map_bind, map_pure, preL, bind_map_left, apply_ite,
    Sum.map_inl, Sum.map_inr, id] <;> congr 1 <;> funext x <;> (try split) <;>
    simp [map_bind, map_pure, Sum.map_inl, Sum.map_inr]

/-- **A line on the prefixed state** is the line on the state, prefixed. -/
theorem applyLine_pre (r : LineRec) :
    applyLine (st.pre D) r = preL D <$> applyLine st r := by
  cases r <;> simp [applyLine, applyDeclD, parseExprEntryD_pre, parseNameEntryD_pre,
    parseLevelEntryD_pre, processLineCoreD_pre, map_pure, preL]

theorem applyLine_pre_run (r : LineRec) (a : AState) :
    (applyLine (st.pre D) r).run a =
      ((applyLine st r).run a).map fun p => (preL D p.1, p.2) := by
  rw [applyLine_pre, StateT.run_map]
  cases (applyLine st r).run a <;> rfl

end

end ConRon.Arena.Frontend
