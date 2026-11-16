module

public import ConAgua.Arena.IndMaster
public import ConAgua.Arena.EnvFlags
import ConAgua.Arena.DerRel

@[expose] public section

/-!
# The stage relation across the literal flags' stores

`env_push` ends with `flagsSet` (the flag words `CTL[160]`, `CTL[161]`, `EnvFlags.lean`) and
`env_set_flags` is `flagsSet`: the rest of `StageR` (the arena, the core tier, the pins, the
mode, the `IW` pool) does not read the two words, so it carries over to the new environment.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- **`StageR` across `flagsSet`**, at the environment the new memory relates. -/
theorem StageR.of_flags {vis vis' : Word} {fe fe' : IFEnv} {a : AState} {m : Mem} {x y : Word}
    (hS : StageR vis fe m a) (hE : EnvR (flagsSet m x y) vis' fe') :
    StageR vis' fe' (flagsSet m x y) a ∧ IWGrow m (flagsSet m x y) := by
  have hf := flagsSet_frame m x y
  have hA3 : (IW : TieredArray) ∉ ([] : List TieredArray) ∧ (EREC : TieredArray) ∉ ([] : List TieredArray) ∧
      tier1 EREC ∉ ([] : List TieredArray) := by simp
  have hC3 : (129 : Word) ∉ ([160, 161] : List Word) ∧ (130 : Word) ∉ ([160, 161] : List Word) ∧
      (200 : Word) ∉ ([160, 161] : List Word) := by decide
  refine ⟨⟨⟨⟨ArenaR.frame (fun b hb => by simp at hb) (fun x hx => not_mem_arenaCtl x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide))
      hf hS.check.arena.base,
      DerR.frameM _ _ m _ hf (fun b hb => by simp at hb) a hS.check.arena.der⟩,
    hS.check.core.frame (fun b hb => by simp at hb) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide) hf,
    hS.check.pins.frame (fun b hb => by simp at hb) hf, hE,
    hS.check.mode.frame hf (by decide) (by decide)⟩, IWOK.of_keep hf hA3 hC3 hS.iw⟩,
    IWGrow.of_keep hf hA3 hC3⟩

/-- **`StageR` across an `env_push`'s memory** (`ownSet`, then `flagsSet`). -/
theorem StageR.of_ownFlags {vis vis' : Word} {fe fe' : IFEnv} {a : AState} {m : Mem} {w c q x y : Word}
    (hS : StageR vis fe m a) (hE : EnvR (flagsSet (ownSet m w c q) x y) vis' fe') :
    StageR vis' fe' (flagsSet (ownSet m w c q) x y) a ∧ IWGrow m (flagsSet (ownSet m w c q) x y) := by
  have hf : MemFrame [ownArr w] [160, 161] m (flagsSet (ownSet m w c q) x y) :=
    ((ownSet_frame m w c q).mono (fun _ h => h) (fun _ h => by simp at h)).trans
      ((flagsSet_frame _ x y).mono (fun _ h => by simp at h) (fun _ h => h))
  have ha := ownArr_arr w
  have hA : ∀ b ∈ [ownArr w], 140 ≤ b.arr ∧ b.arr ≤ 142 := by
    intro b hb; simp only [List.mem_singleton] at hb; subst hb; omega
  have hlow : ∀ y ∈ arenaArrs, y.arr < 64 := by decide
  have hA3 : (IW : TieredArray) ∉ [ownArr w] ∧ (EREC : TieredArray) ∉ [ownArr w] ∧
      tier1 EREC ∉ [ownArr w] :=
    ⟨fun h => by have := hA _ h; revert this; decide, fun h => by have := hA _ h; revert this; decide,
      fun h => by have := hA _ h; revert this; decide⟩
  have hC3 : (129 : Word) ∉ ([160, 161] : List Word) ∧ (130 : Word) ∉ ([160, 161] : List Word) ∧
      (200 : Word) ∉ ([160, 161] : List Word) := by decide
  have hC : ∀ z ∈ ([160, 161] : List Word), z = 160 ∨ z = 161 := by
    intro z hz; simpa using hz
  refine ⟨⟨⟨⟨ArenaR.frame (fun b hb hm => by have := hlow b hm; have := hA b hb; omega)
      (fun z hz => not_mem_arenaCtl z (by rcases hC z hz with rfl | rfl <;> decide)) hf hS.check.arena.base,
      DerR.frameM _ _ m _ hf (fun b hb => by have := hA b hb; omega) a hS.check.arena.der⟩,
    hS.check.core.frame (fun b hb => .inr (by have := hA b hb; omega))
      (fun z hz => by rcases hC z hz with rfl | rfl <;> decide) hf,
    hS.check.pins.frame (fun b hb => .inr (by have := hA b hb; omega)) hf, hE,
    hS.check.mode.frame hf (by decide) (by decide)⟩, IWOK.of_keep hf hA3 hC3 hS.iw⟩,
    IWGrow.of_keep hf hA3 hC3⟩

end L.Ind
