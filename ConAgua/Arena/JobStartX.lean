module

public import ConAgua.Arena.JobStart

@[expose] public section

/-!
# The pool's step with the record pool's growth (lane compare2, the sJ variant)

`recCall_stepX`: `recCall_stepE` over `JobRelX`, the job relation together with the record pool
grown from a fixed memory `M₀` (`recordJob_refX`'s extra post). The sequential compared run needs
the growth across the solution's jobs (`CsKeep.grow`).
-/

namespace L.Arena

open ConRon.Arena ConRon.Bridge

local notation "V" => ConLeche.CheckMode.verified

/-- The job relation, and the record pool grown from `M₀`. -/
def JobRelX (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
    (J : Option ISolution) (I : IStreamIndex) (a₀ : AState) (M₀ : Mem) (m : Mem) (a : AState) : Prop :=
  JobRel pins dn ds J I a₀ m a ∧ ArrExt (erecP M₀) (erecP m)

/-- **`record_job` calls as the pool's step over `JobRelX`.** -/
theorem recCall_stepX {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
    {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} {p : Prog} {J : Option ISolution}
    {I : IStreamIndex}
    (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) (hdn : DnPers dn)
    (hpp : PersPinSets pins) (hds : ds.size < 2 ^ 64)
    {a₀ : AState} (hden : ∀ x ∈ ds.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl a₀.store x = some d)
    (hPD : PinsDenote a₀.store pins pinsP) (hrec : JobSpec pins pinsP J a₀)
    (hcrs : CrsFor pins dn ds p J) (M₀ : Mem) :
    ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < ds.size), JobRelX pins dn ds J I a₀ M₀ r a →
      RecCall p k r r' → (∃ env, FoldOK env (I.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob V pins J I k ds[k] a = .ok ((), a') ∧ JobRelX pins dn ds J I a₀ M₀ r' a' := by
  intro k r r' a hk ⟨⟨a₁, ⟨hJ, hx, hp⟩, hS⟩, hX⟩ ⟨n, rs, hn, hc⟩ hF
  rw [← hS.st] at hF
  have hkw : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt (Nat.lt_trans hk hds)
  have hden' : ∀ x ∈ ds.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl a₁.store x = some d :=
    fun x hx' => by
      obtain ⟨h1, d, h2⟩ := hden x hx'
      exact ⟨h1, d, denoteDecl_pext hx h1 h2⟩
  have hPD' := PinsDenote.pmono hx pins pinsP hpp hPD
  have hk' : (UInt64.ofNat k).toNat < ds.size := by rw [hkw]; exact hk
  have hr := recordJob_refX hP hFD hLD hdn hpp (N := n) hn hk' hJ (hrec.pmono hx) hcrs (by rw [hkw]; exact hF)
    hden' hPD'
  rw [hc] at hr
  obtain ⟨u, a', hrun, ⟨hJ₁, hx₁, hp₁⟩, hX₁⟩ := hr
  have e : recordJob V pins J I (UInt64.ofNat k).toNat ds[(UInt64.ofNat k).toNat] =
      recordJob V pins J I k ds[k] := by simp only [hkw]
  have hrun' : recordJob V pins J I k ds[k] a₁ = .ok ((), a') := by rw [← e]; cases u; exact hrun
  exact ⟨a', by rw [← recordJob_sameEnter hS]; exact hrun', ⟨a', ⟨hJ₁, hx.trans hx₁, hp₁.trans hp⟩,
    SameEnter.refl _⟩, fun i v h => hX₁ i v (hX i v h)⟩

end L.Arena
