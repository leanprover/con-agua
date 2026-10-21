module

public import ConLeche.Verify.Inductives.PosDeriv

public section

/-!
# Official's uniform check, inverted

The install runs official's `check_uniform_ind_occs` BEFORE the
positivity check (`nestUniform`, `Kernel/Inductives/Positivity.lean`):
at every stored constructor, the parameters' domains name no member, and
its root crest (`nestRootCrest`: every whole application `T_m.{lps} p⃗`
replaced by the member's hole) names no member constant.  `nestUniform_inv`
reads the check off the run; the syntactic lemmas below move the
"no member constant" fact through instantiation.
-/

namespace ConLeche

/-! ## The uniform check, inverted -/

/-- `nestUniform` passed: the check at every stored constructor. -/
theorem nestUniform_inv {ctx : NestCtx}
    {ctorss : List (List (ConstantVal × Nat))}
    (h : nestUniform (m := CheckM) ctx ctorss = .ok ()) :
    ∀ cs ∈ ctorss, ∀ c ∈ cs, nestUniformOk ctx c.1 = true := by
  unfold nestUniform at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rename_i hn
    intro cs hcs c hc
    rw [List.findSome?_eq_none_iff] at hn
    have := List.find?_eq_none.mp (hn cs hcs) c hc
    simpa using this

/-- **The canonical crest of a constructor that passed the check names no
member constant.** -/
theorem nestRootCanon_nestOcc_zero {ctx : NestCtx} {cv : ConstantVal}
    (hu : nestUniformOk ctx cv = true) :
    ∃ A, nestRootCanon ctx cv = some A ∧ A.nestOcc ctx.names 0 0 = false := by
  simp only [nestUniformOk, Bool.and_eq_true, Bool.not_eq_true'] at hu
  obtain ⟨-, hb⟩ := hu
  split at hb
  case h_2 => exact nomatch hb
  rename_i A hcr
  exact ⟨A, hcr, by simpa using hb⟩

end ConLeche
