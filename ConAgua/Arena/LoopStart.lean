module

public import ConAgua.Arena.CheckerT

@[expose] public section

/-!
# The declaration loop's start

The record pool's name decoder at the loop's start (`dnOf`, injective under `StoreWF`), the
records' level-parameter handles having names under it (`declsLpsDn_dnOf`), and the lookups the
loop's top takes (`LoopTopProg`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

open L.Front (DECL DLP DeclsF)

/-- **The record pool's name decoder at the loop's start**: the start store's persistent names
(the startup interned them with the scratch tier off; the loop's steps only grow the persistent
tier, `LoopMem.dnP`). -/
def dnOf (st : EStore) (k : NIdx) : Option ConLeche.Name :=
  if k.isPersistent then denoteN st.ns k else none

theorem dnOf_inj {st : EStore} (hwf : StoreWF st) : L.Ind.DnInj (dnOf st) := by
  intro x y n hx hy
  obtain ⟨rk, hw⟩ := hwf
  simp only [dnOf] at hx hy
  split at hx
  · split at hy
    · exact ConRon.Arena.denoteN_inj hw.nsWF hx hy
    · cases hy
  · cases hx

theorem denoteNList_mem_some {st : NStore} :
    ∀ {hs : List NIdx} {xs : List ConLeche.Name}, Frontend.denoteNList st hs = some xs →
      ∀ k ∈ hs, (denoteN st k).isSome
  | [], _, _, k, hk => absurd hk (by simp)
  | h :: hs, xs, hd, k, hk => by
    simp only [Frontend.denoteNList] at hd
    cases h1 : denoteN st h with
    | none => rw [h1] at hd; simp at hd
    | some x =>
      cases h2 : Frontend.denoteNList st hs with
      | none => rw [h1, h2] at hd; simp at hd
      | some ys =>
        rcases List.mem_cons.mp hk with rfl | hk
        · simp [h1]
        · exact denoteNList_mem_some h2 k hk

theorem denoteCIList_mem_some {st : EStore} :
    ∀ {cs : List IConstantInfo} {xs : List ConLeche.ConstantInfo},
      Frontend.denoteCIList st cs = some xs → ∀ c ∈ cs, ∃ y, Frontend.denoteCI st c = some y
  | [], _, _, c, hc => absurd hc (by simp)
  | c' :: cs, xs, hd, c, hc => by
    simp only [Frontend.denoteCIList] at hd
    cases h1 : Frontend.denoteCI st c' with
    | none => rw [h1] at hd; simp at hd
    | some x =>
      cases h2 : Frontend.denoteCIList st cs with
      | none => rw [h1, h2] at hd; simp at hd
      | some ys =>
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨x, h1⟩
        · exact denoteCIList_mem_some h2 c hc

/-- **The records' level-parameter handles have names under the start decoder**: every handle of
a denoting persistent record is persistent with a `denoteN` name, which `dnOf` keeps. -/
theorem declsLpsDn_dnOf {st : EStore} {ds : Array IDeclaration}
    (hpd : ∀ x ∈ ds.toList, ConRon.Bridge.PersDecl x)
    (hden : ∃ dsP, ConRon.Bridge.denoteDecls st ds.toList = some dsP) :
    DeclsLpsDn (dnOf st) ds := by
  intro i hi b nP hd cv caps hmem k hk
  obtain ⟨dsP, hD⟩ := hden
  have hm : ds[i] ∈ ds.toList := by simp
  obtain ⟨x, hx⟩ := ConRon.Bridge.denoteDecl_of_mem hD _ hm
  have hp := hpd _ hm
  rw [hd] at hx hp
  simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
  obtain ⟨bs, hbs, -⟩ := hx
  obtain ⟨y, hy⟩ := denoteCIList_mem_some hbs _ hmem
  have hpk : k.isPersistent = true := (hp _ hmem).1.levelParams k hk
  simp only [Frontend.denoteCI] at hy
  cases h1 : Frontend.denoteCV st cv with
  | none => rw [h1] at hy; simp at hy
  | some v =>
  simp only [Frontend.denoteCV] at h1
  cases h2 : Frontend.denoteNList st.ns cv.levelParams with
  | none => rw [h2] at h1; split at h1 <;> simp_all
  | some lps =>
  simp only [dnOf, hpk, ite_true]
  exact denoteNList_mem_some h2 k hk

/-- The lookups the loop's top takes beyond `LoopCallees`: the bracket. -/
structure LoopTopProg (p : Prog) : Prop where
  bracket : BracketProg p

end L.Arena
