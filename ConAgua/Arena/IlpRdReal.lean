import ConAgua.Arena.IlpRd
import ConAgua.Arena.IndRealIlpL

/-!
# The program's own reading of `inst_lp_fast` meets `IlpRd` (lane `indstaget`, helper `rcC`)

From `StageT` at the base point of `IlpBase` (an `IW` frame keeps it: `StageT.of_iw`), lane
`indproofs4`'s `ilpfF_okT`/`ilpfF_okTA` at the call, its frame `ilpfF_frame`.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

theorem ilpfA_stage : ∀ b ∈ ilpfA, b < 201 ∨ 208 < b := by
  intro b hb
  simp only [ilpfA, List.mem_cons, List.not_mem_nil, or_false] at hb
  left; rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> decide

theorem ilpfC_stage : ∀ x ∈ ilpfC, x.toNat < 202 ∨ 219 < x.toNat := by
  intro x hx
  simp only [ilpfC, List.mem_cons, List.not_mem_nil, or_false] at hx
  left; rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- **`realCall p` meets the `inst_lp_fast` contract** at the call points of `IlpBase m₀ a₀`, from
`StageT` at `(m₀, a₀)`. -/
theorem IlpRd.real {p : Prog} (hIlpf : IlpfF p) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m₀ : Mem} {a₀ : AState} (hT : StageT dn vis fe m₀ a₀) :
    IlpRd (realCall p) dn vis fe (IlpBase m₀ a₀) := by
  rintro k f o l us e ks m m' a r hu he ⟨rfl, hfr⟩ hS hd h
  have hT1 : StageT dn vis fe m a := StageT.of_iw hT hS hfr
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ilpfF_spec p hIlpf k ⟨m, Locals.init []⟩ [f, o, l, us, e]) h
  obtain ⟨x, a', hrun, hK⟩ := ilpfF_okT f o l us e hu he ks m s'.mem a r hW ⟨hT1, hd⟩
  refine ⟨x, a', hrun, ⟨hK.1.stage, hK.2.1, hK.2.2⟩,
    ⟨ilpfA, ilpfC, ilpfA_stage, ilpfC_stage, ilpfF_frame hW⟩, fun hA => ?_⟩
  obtain ⟨-, -, -, -, hA'⟩ := ilpfF_okTA f o l us e hu he ks m s'.mem a r hW ⟨hT1, hA, hd⟩
  exact hA'

theorem IlpFr.real {p : Prog} (hIlpf : IlpfF p) : IlpFr (realCall p) := by
  intro k args m m' r h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ilpfF_spec p hIlpf k ⟨m, Locals.init []⟩ args) h
  exact ⟨ilpfA, ilpfC, ilpfA_stage, ilpfC_stage, ilpfF_frame hW⟩

/-- The same at the twin state of a `StageC` start. -/
theorem IlpRd.realC {p : Prog} (hIlpf : IlpfF p) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {env : ConLeche.Env} {m₀ : Mem} {a₀ : AState}
    (hC : StageC dn vis fe env m₀ a₀) : IlpRd (realCall p) dn vis fe (IlpBase m₀ a₀) :=
  IlpRd.real hIlpf hC.stageT

end L.Ind
