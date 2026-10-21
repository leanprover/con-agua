module

public import ConLeche.Kernel.Core
public import ConLeche.Verify.Inductives.NestedRead

public section

/-!
# Environment well-formedness

`EnvWF` collects the syntactic facts the checker establishes for every
accepted constant — closed, level parameters within the declared list,
referenced constants resolving — as an invariant of the environment.  The
delta-unfolding and monotonicity lemmas need it.
-/

namespace ConLeche

/-- The projection-table name shape is injective (task #175 S1). -/
theorem projTableName_inj {T T' : Name} (h : projTableName T = projTableName T') :
    T = T' := by
  simp only [projTableName, Name.num.injEq, Name.str.injEq] at h
  exact h.1.1

/-- Unfold a successful projection-table lookup to the stored table:
the structure's table is stored, the index is in range, and the entry
is the table's view at it (task #175 S1). -/
theorem Env.findProj?_some {env : Env} {T : Name} {i : Nat}
    {entry : ProjEntry} (h : env.findProj? T i = some entry) :
    ∃ tbl : ProjTable, env.find? (projTableName T) = some (.projInfo tbl) ∧
      i < tbl.numFields ∧ entry = tbl.entry i := by
  unfold Env.findProj? at h
  split at h
  next tbl heq =>
    split at h
    · next hi => exact ⟨tbl, heq, hi, (Option.some.inj h).symm⟩
    · exact nomatch h
  next => exact nomatch h

/-- The lookup at a stored table, in range. -/
theorem Env.findProj?_of_table {env : Env} {T : Name} {tbl : ProjTable}
    (h : env.find? (projTableName T) = some (.projInfo tbl)) {i : Nat}
    (hi : i < tbl.numFields) : env.findProj? T i = some (tbl.entry i) := by
  unfold Env.findProj?
  rw [h]
  exact ite_eq_left hi

/-- No table stored, no entry. -/
theorem Env.findProj?_none_of_fresh {env : Env} {T : Name}
    (h : env.find? (projTableName T) = none) (i : Nat) : env.findProj? T i = none := by
  unfold Env.findProj?
  rw [h]

/-- **The stored table's projection offset** of structure `T` (task
#210 Part A; `0` when no table is stored): what every entry of the
table carries (`Env.findProj?_off`). -/
def Env.projOff (env : Env) (T : Name) : Nat :=
  match env.find? (projTableName T) with
  | some (.projInfo tbl) => tbl.off
  | _ => 0

theorem Env.findProj?_off {env : Env} {T : Name} {i : Nat} {e : ProjEntry}
    (hi : env.findProj? T i = some e) : e.off = env.projOff T := by
  obtain ⟨tbl, hf, -, rfl⟩ := Env.findProj?_some hi
  unfold Env.projOff
  rw [hf]
  rfl

/-- Two entries of one structure's table carry the same projection
offset (task #210 Part A): both are views of the one stored table. -/
theorem Env.findProj?_off_eq {env : Env} {T : Name} {i j : Nat} {e e' : ProjEntry}
    (hi : env.findProj? T i = some e) (hj : env.findProj? T j = some e') : e.off = e'.off := by
  obtain ⟨tbl, hf, -, rfl⟩ := Env.findProj?_some hi
  obtain ⟨tbl', hf', -, rfl⟩ := Env.findProj?_some hj
  obtain rfl : tbl = tbl' := ConstantInfo.projInfo.inj (Option.some.inj (hf.symm.trans hf'))
  rfl

@[simp] theorem ProjTable.entry_levelParams (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).levelParams = tbl.levelParams := rfl
@[simp] theorem ProjTable.entry_numParams (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).numParams = tbl.numParams := rfl
@[simp] theorem ProjTable.entry_body (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).body = tbl.bodies.getD i default := rfl
/-- **The capability arities**: an inductive stored with the unit-like
or the η capability has the `∀`-telescope its capability record's
parameter count names.  A property of the stored declaration alone —
established ONCE at the block's install (the install pins the
former's telescope before storing it, `checkBlockTele`'s
`stripPis (nP + nIdx)`; the basis blocks' types are literal) and consumed by
the structure-η and unit-like rows
(`ConLeche/Model/Caps.lean`) from the invariant rather than re-checked
per call ("invariants over runtime gates"). -/
@[expose] def IndCapsWF (c : ConstantInfo) : Prop :=
  ∀ cv caps, c = .indInfo cv caps →
    (caps.unitlike = true → (cv.type.stripPis caps.unitParams).isSome = true) ∧
    (caps.eta = true → (cv.type.stripPis caps.etaParams).isSome = true)

/-- `IndCapsWF` at an inductive, from the two arity facts. -/
theorem IndCapsWF.of_caps {cv : ConstantVal} {caps : IndCaps}
    (hu : caps.unitlike = true → (cv.type.stripPis caps.unitParams).isSome = true)
    (he : caps.eta = true → (cv.type.stripPis caps.etaParams).isSome = true) :
    IndCapsWF (.indInfo cv caps) := by
  intro cv' caps' heq
  obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj heq
  exact ⟨hu, he⟩

/-- A `stripPis` at a larger count strips at a smaller one. -/
theorem stripPis_isSome_of_le :
    ∀ {k n : Nat} {e : Expr}, k ≤ n → (e.stripPis n).isSome = true →
      (e.stripPis k).isSome = true := by
  intro k
  induction k with
  | zero => intro n e _ _; simp [Expr.stripPis]
  | succ k ih =>
    intro n e hle h
    match n, hle with
    | n + 1, hle =>
      match e, h with
      | .forallE d bo, h =>
        simp only [Expr.stripPis, Option.isSome_map] at h ⊢
        exact ih (by omega) h

/-- Syntactic well-formedness of one stored constant w.r.t. `env`. -/
@[expose] def ConstWF (env : Env) (c : ConstantInfo) : Prop :=
  c.toConstantVal.type.hasFvar = false ∧
  c.toConstantVal.type.allLevelParamsDefined c.toConstantVal.levelParams = true ∧
  c.toConstantVal.type.constsResolve env = true ∧
  c.toConstantVal.type.looseBVarsBounded 0 = true ∧
  (∀ cv value hint, c = .defnInfo cv value hint →
    value.hasFvar = false ∧
    value.allLevelParamsDefined cv.levelParams = true ∧
    value.constsResolve env = true ∧
    value.looseBVarsBounded 0 = true) ∧
  (∀ cv mI rP rules, c = .recInfo cv mI rP rules →
    ∀ r, r ∈ rules →
      (RecRule.rhs r).hasFvar = false ∧
      (RecRule.rhs r).allLevelParamsDefined cv.levelParams = true ∧
      (RecRule.rhs r).constsResolve env = true ∧
      (RecRule.rhs r).looseBVarsBounded 0 = true ∧
      -- a nested rule's datum reads off the recursor type
      -- (`NestedRead`: the pins are well formed in the rule-prefix
      -- context, and the major's domain applies the class's inductive
      -- at the levels to the pins' liftings past the index binders,
      -- followed by the index variables; what the generated stage
      -- stores, `genStage_nestedRead`)
      ∀ lvls pins, RecRule.fire r = .nested lvls pins →
        NestedRead (·.constsResolve env) cv.levelParams cv.type mI rP pins.length lvls pins) ∧
  -- (a theorem's stored value carries NO clause: a theorem is opaque
  -- to reduction and stored by its statement — the value is the
  -- record's own, unread by the kernel and by the invariant)
  -- a projection table's bodies (task #175 S1): closed with respect to
  -- free variables, level parameters within the structure's list,
  -- resolving, and scoped at the parameters and the subject; there
  -- are exactly `numFields` of them
  (∀ tbl, c = .projInfo tbl →
    tbl.bodies.size = tbl.numFields ∧
    ∀ (i : Nat) (b : Expr), tbl.bodies[i]? = some b →
      b.hasFvar = false ∧
      b.allLevelParamsDefined tbl.levelParams = true ∧
      b.constsResolve env = true ∧
      b.looseBVarsBounded (tbl.numParams + 1) = true) ∧
  -- the capability arities (environment-independent)
  IndCapsWF c

/-- Every stored constant is syntactically well-formed. -/
@[expose] def EnvWF (env : Env) : Prop := ∀ c ∈ env.consts, ConstWF env c

/-- The capability arities of a stored inductive, off `EnvWF`. -/
theorem EnvWF.indCaps {env : Env} (henv : EnvWF env) {T : Name}
    {cv : ConstantVal} {caps : IndCaps}
    (h : env.find? T = some (.indInfo cv caps)) :
    (caps.unitlike = true → (cv.type.stripPis caps.unitParams).isSome = true) ∧
    (caps.eta = true → (cv.type.stripPis caps.etaParams).isSome = true) :=
  (henv _ (List.mem_of_find?_eq_some h)).2.2.2.2.2.2.2 cv caps rfl

/-- `find?` on a cons. -/
theorem Env.find?_cons {c : ConstantInfo} {env : Env} {n : Name} :
    Env.find? ⟨c :: env.consts⟩ n = if c.name = n then some c else env.find? n := by
  simp only [Env.find?, List.find?]
  split
  · next h => simp_all
  · next h => simp_all

/-- A cons finds its own head. -/
theorem Env.find?_cons_self (c : ConstantInfo) (env : Env) :
    Env.find? ⟨c :: env.consts⟩ c.name = some c := by
  rw [Env.find?_cons, ite_eq_left rfl]

/-- A cons of a *fresh* head does not find anything new. -/
theorem Env.find?_cons_of_fresh {c : ConstantInfo} {env : Env}
    {n : Name} {ci : ConstantInfo} (hfresh : env.find? c.name = none)
    (h : env.find? n = some ci) :
    Env.find? ⟨c :: env.consts⟩ n = some ci := by
  rw [Env.find?_cons]
  split
  · next heq => rw [heq, h] at hfresh; exact nomatch hfresh
  · exact h

/-- Extending the environment with a fresh constant does not change
successful lookups. -/
theorem Env.find?_cons_of_isSome {c : ConstantInfo} {env : Env} {n : Name}
    (hfresh : env.find? c.name = none) (h : (env.find? n).isSome = true) :
    Env.find? ⟨c :: env.consts⟩ n = env.find? n := by
  rw [Env.find?_cons]
  split
  · next heq => rw [← heq] at h; rw [hfresh] at h; simp at h
  · rfl

/-- A cons at another name does not change a table lookup. -/
theorem Env.findProj?_cons_ne {env : Env} {c₀ : ConstantInfo} {T : Name}
    (hn : c₀.name ≠ projTableName T) (i : Nat) :
    Env.findProj? ⟨c₀ :: env.consts⟩ T i = env.findProj? T i := by
  unfold Env.findProj?
  rw [Env.find?_cons, ite_eq_right hn]

/-- Resolution depends on the environment only through which names it
finds: every name found in `env` being found in `env'` carries
resolution over. -/
theorem Expr.constsResolve_of_find {env env' : Env}
    (hf : ∀ n, (env.find? n).isSome = true → (env'.find? n).isSome = true) :
    ∀ {e : Expr}, e.constsResolve env = true → e.constsResolve env' = true := by
  intro e
  induction e with
  | bvar i => intro h; simp [Expr.constsResolve]
  | sort u => intro h; simp [Expr.constsResolve]
  | const n us =>
    intro h
    simp only [Expr.constsResolve] at h ⊢
    exact hf _ h
  | lit l =>
    cases l with
    | natVal n =>
      intro h
      simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
      exact ⟨⟨hf _ h.1.1, hf _ h.1.2⟩, hf _ h.2⟩
    | strVal s =>
      intro h
      simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hf _ h.1.1.1.1.1.1.1.1.1, hf _ h.1.1.1.1.1.1.1.1.2⟩,
        hf _ h.1.1.1.1.1.1.1.2⟩, hf _ h.1.1.1.1.1.1.2⟩,
        hf _ h.1.1.1.1.1.2⟩, hf _ h.1.1.1.1.2⟩, hf _ h.1.1.1.2⟩,
        hf _ h.1.1.2⟩, hf _ h.1.2⟩, hf _ h.2⟩
  | fvar idx ty ih =>
    intro h
    simp only [Expr.constsResolve] at h ⊢
    exact ih h
  | app f a ihf iha =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty body ihty ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihty h.1, ihbody h.2⟩
  | forallE ty body ihty ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihty h.1, ihbody h.2⟩
  | letE ty val body ihty ihval ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ihty h.1.1, ihval h.1.2⟩, ihbody h.2⟩
  | proj s i e ih =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨hf _ h.1, ih h.2⟩

/-- Resolution is monotone under environment extension. -/
theorem Expr.constsResolve_mono {c : ConstantInfo} {env : Env} :
    ∀ {e : Expr}, e.constsResolve env = true →
      e.constsResolve ⟨c :: env.consts⟩ = true :=
  Expr.constsResolve_of_find fun n h => by
    rw [Env.find?_cons]
    split <;> simp_all

/-- Resolution survives binder opening. -/
theorem Expr.constsResolve_instantiate1 {env : Env} {d : Nat} {ty : Expr}
    (hty : ty.constsResolve env = true) :
    ∀ {e : Expr} (k : Nat), e.constsResolve env = true →
      (e.instantiate1 (.fvar d ty) k).constsResolve env = true := by
  intro e
  induction e <;> intro k h <;> simp_all [Expr.instantiate1, Expr.constsResolve]
  case bvar i =>
    split
    · simpa [Expr.constsResolve] using hty
    · split <;> simp [Expr.constsResolve]

/-- Level instantiation does not change which constants occur. -/
theorem Expr.constsResolve_instantiateLevelParams {env : Env} (ks : List Name)
    (us : List Level) :
    ∀ {e : Expr}, (e.instantiateLevelParams ks us).constsResolve env = e.constsResolve env := by
  intro e
  induction e <;> simp_all [Expr.instantiateLevelParams, Expr.constsResolve]

/-- Resolution survives `piResult` (peeling leading `∀`s keeps every
constant the residual mentions — task #342 L10, the `RecRuleExtra`
transport's clause (S)). -/
theorem Expr.constsResolve_piResult {env : Env} :
    ∀ {e : Expr}, e.constsResolve env = true → e.piResult.constsResolve env = true
  | .forallE _ b, h => by
      have hb : b.constsResolve env = true := by
        simp only [Expr.constsResolve, Bool.and_eq_true] at h
        exact h.2
      exact Expr.constsResolve_piResult (e := b) hb
  | .bvar _, h | .sort _, h | .lit _, h | .const _ _, h | .fvar _ _, h
  | .app _ _, h | .lam _ _, h | .letE _ _ _, h | .proj _ _ _, h => by
      simpa [Expr.piResult] using h

/-- Resolution survives `getAppFn` (peeling an application spine's
head keeps every constant it mentions). -/
theorem Expr.constsResolve_getAppFn {env : Env} :
    ∀ {e : Expr}, e.constsResolve env = true → e.getAppFn.constsResolve env = true
  | .app f _, h => by
      have hf : f.constsResolve env = true := by
        simp only [Expr.constsResolve, Bool.and_eq_true] at h
        exact h.1
      exact Expr.constsResolve_getAppFn (e := f) hf
  | .bvar _, h | .sort _, h | .lit _, h | .const _ _, h | .fvar _ _, h
  | .lam _ _, h | .forallE _ _, h | .letE _ _ _, h | .proj _ _ _, h => by
      simpa [Expr.getAppFn] using h

/-- **A resolving expression's `piResult`'s head constant is stored**
(task #342 L10): the constructor's stored type resolves (`ConstWF`),
so the family name heading its result — the one `iotaCtorNeverProp`
looks up — is stored too, hence never the fresh name of a cons. -/
theorem Expr.find?_isSome_of_piResult_getAppFn_const {env : Env} {e : Expr}
    {T : Name} {us : List Level} (hres : e.constsResolve env = true)
    (heq : e.piResult.getAppFn = .const T us) : (env.find? T).isSome = true := by
  have h2 := Expr.constsResolve_getAppFn (Expr.constsResolve_piResult hres)
  rw [heq] at h2
  simpa [Expr.constsResolve] using h2

/-- Extending with a fresh, well-formed constant preserves `EnvWF`. -/
theorem EnvWF.cons {c : ConstantInfo} {env : Env}
    (henv : EnvWF env)
    (hc : ConstWF ⟨c :: env.consts⟩ c) : EnvWF ⟨c :: env.consts⟩ := by
  intro c' hc'
  rcases List.mem_cons.mp hc' with rfl | hmem
  · exact hc
  · obtain ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩ := henv c' hmem
    refine ⟨h1, h2, Expr.constsResolve_mono h3, h4, fun cv value hint heq =>
      let ⟨g1, g2, g3, g4⟩ := h5 cv value hint heq
      ⟨g1, g2, Expr.constsResolve_mono g3, g4⟩, ?_,
      fun tbl heq =>
        let ⟨g0, g⟩ := h8 tbl heq
        ⟨g0, fun i b hb =>
          let ⟨g1, g2, g3, g4⟩ := g i b hb
          ⟨g1, g2, Expr.constsResolve_mono g3, g4⟩⟩, h9⟩
    intro cv mI rP rules heq r hr
    obtain ⟨g1, g2, g3, g4, g5⟩ := h6 cv mI rP rules heq r hr
    refine ⟨g1, g2, Expr.constsResolve_mono g3, g4, ?_⟩
    intro lvls pins hfr
    obtain ⟨n1, n2, n3, n4⟩ := g5 lvls pins hfr
    exact ⟨n1, n2, fun pin hpin =>
      let ⟨p1, p2, p3, p4⟩ := n3 pin hpin
      ⟨p1, p2, Expr.constsResolve_mono p3, p4⟩, n4⟩

/-- The kernel's name-list distinctness check is `List.Nodup`'s. -/
theorem nodup_of_nameNodup : ∀ {ns : List Name}, ConLeche.Name.nodup ns = true → ns.Nodup
  | [], _ => List.nodup_nil
  | n :: ns, h => by
    simp only [ConLeche.Name.nodup, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_of_nameNodup h.2⟩
    have := h.1
    simp [hm] at this

/-! ## Two `find?` readings -/

/-- A `find?` hit names the stored constant. -/
theorem Env.find?_name {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.name = n := by
  unfold ConLeche.Env.find? at h
  have := List.find?_some h
  simpa using this

/-- A `find?` hit is a stored constant. -/
theorem Env.find?_mem {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci ∈ env.consts := by
  unfold ConLeche.Env.find? at h
  exact List.mem_of_find?_eq_some h

end ConLeche
