import ConAgua.Arena.IndTwin

/-!
# `lvl_eq_c`, `lvls_eq_c` under `StageT` with the exact verdict word (lane `indproofs4`, helper `lvl`)

The stub contracts `IndStubs.lvlEqStub_spec` and `RecCheckSpec/TcmLook.lvlsEqStub_spec` decode the verdict
by `decLvlEq` (the word is exactly `0`, `1` or `2`), what the stage's callers test (`r == 2`). Lane
`whnf`'s refinements (`lvlEqC_refines`, `lvlsEqC_refines`, through `IndTwin.lvlEqC_simT`) state the
verdict as `decO r` only. `lvlEqCW_enc`, `lvlsEqCW_enc`: the word is one of the three (a cache hit
returns `1` or `2`, a miss the encoded verdict of `lv_equiv`/`lv_equivs`, lane `levels`' `equivW_ok`).
With them, `lvlEqC_simTE`, `lvlsEqC_simT`: the two calls as `Sim`s under `StageT` with `decLvlEq`
(replacing the two contracts for a caller carrying `StageT`; `lv_leq_top`'s is `IndTwin.lvLeqTop_simT`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem rcdK_res {S : MemoSch} {u v z z₁ : Word} {m₁ m' : Mem}
    (h : rcdK S u v (some (z₁, m₁)) = some (z, m')) : z = 0 ∨ z = z₁ := by
  simp only [rcdK] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact .inl h.1.symm
  · split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact .inr h.1.symm

theorem encO_three (o : Option Bool) : encO o = 0 ∨ encO o = 1 ∨ encO o = 2 := by
  rcases o with _ | _ | _ <;> simp [encO]

theorem hit_three (c : Prop) [Decidable c] :
    ((if c then 1 else 0) + 1 : Word) = 0 ∨ ((if c then 1 else 0) + 1 : Word) = 1 ∨
      ((if c then 1 else 0) + 1 : Word) = 2 := by
  by_cases h : c <;> simp [h]

/-- **`decLvlEq` from `decO`** at a word that is `0`, `1` or `2`. -/
theorem decLvlEq_of_decO {m : Mem} {r : List Word} {x : Option Bool} (hd : decO (r.headD 0) = x)
    (h3 : r.headD 0 = 0 ∨ r.headD 0 = 1 ∨ r.headD 0 = 2) : decLvlEq m r x := by
  unfold decLvlEq
  rcases h3 with h | h | h <;> rw [h] at hd ⊢ <;> subst hd <;> decide

section enc
variable {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
  {M : ModeMaps} {eb : Word}

/-- **`lvl_eq_c`'s word is `0`, `1` or `2`.** -/
theorem lvlEqCW_enc (hS : CoreS dn m a vis fe M eb) (n : Nat) (u v : Word) (hu : HW u) (hv : HW v)
    (lu lv : ConLeche.Level) (hdu : denoteL a.store.ls (decI u) = some lu)
    (hdv : denoteL a.store.ls (decI v) = some lv) (z : Word) (h : lvlEqCW n m u v = some (z, m')) :
    z = 0 ∨ z = 1 ∨ z = 2 := by
  unfold lvlEqCW at h
  by_cases h0 : mfindG lqSch m u v = []
  · simp [h0] at h
  rw [ite_eq_right h0] at h
  by_cases h1 : (mfindG lqSch m u v).headD 0 ≠ 0
  · rw [ite_eq_left h1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hit_three _
  rw [ite_eq_right h1] at h
  rcases hl : lvlEqW n m u v with _ | ⟨z₁, m₁⟩
  · simp [hl, rcdK] at h
  rw [hl] at h
  rcases n with _ | n
  · simp [lvlEqW] at hl
  simp only [lvlEqW] at hl
  have hR₀ : ArenaR (m.set64 CTL 192 0) a :=
    ArenaR.frame (by decide) c192_not_arena (reset_frame m) hS.arena.1
  have hwu : (decI u : LIdx).word.toUInt64 = u := (word_decI _ u hu).mpr rfl
  have hwv : (decI v : LIdx).word.toUInt64 = v := (word_decI _ v hv).mpr rfl
  have hl' := denoteL_lvR hR₀ (decI u) lu hdu
  have hr' := denoteL_lvR hR₀ (decI v) lv hdv
  rw [hwu] at hl'; rw [hwv] at hr'
  obtain ⟨-, hz⟩ := equivW_ok (nameN_rel _ hS.nwf) n _ _ _ _ _ _ _ hl' hr' hl
  rcases rcdK_res h with rfl | rfl
  · exact .inl rfl
  · rw [hz]; exact encO_three _

/-- **`lvls_eq_c`'s word is `0`, `1` or `2`.** -/
theorem lvlsEqCW_enc (hS : CoreS dn m a vis fe M eb) (n : Nat) (us vs : Word) (hu : HW us)
    (hv : HW vs) (z : Word) (h : lvlsEqCW n m us vs = some (z, m')) : z = 0 ∨ z = 1 ∨ z = 2 := by
  unfold lvlsEqCW at h
  by_cases h0 : mfindG lsqSch m us vs = []
  · simp [h0] at h
  rw [ite_eq_right h0] at h
  by_cases h1 : (mfindG lsqSch m us vs).headD 0 ≠ 0
  · rw [ite_eq_left h1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hit_three _
  rw [ite_eq_right h1] at h
  rcases hl : lvlsEqW n m us vs with _ | ⟨z₁, m₁⟩
  · simp [hl, rcdK] at h
  rw [hl] at h
  rcases n with _ | n
  · simp [lvlsEqW] at hl
  simp only [lvlsEqW] at hl
  have hn : ¬ (lsNodeW m us = [] ∨ lsNodeW m vs = []) := fun c => by rw [ite_eq_left c] at hl; cases hl
  rw [ite_eq_right hn] at hl
  obtain ⟨lu, hdu⟩ := hS.den.lsAll _ (by
    obtain ⟨ids, e, -⟩ := lsNodeW_view hS.arena.1 hu (fun e => hn (.inl e)); rw [e]; rfl)
  obtain ⟨lv, hdv⟩ := hS.den.lsAll _ (by
    obtain ⟨ids, e, -⟩ := lsNodeW_view hS.arena.1 hv (fun e => hn (.inr e)); rw [e]; rfl)
  obtain ⟨ids₁, hv₁, hd₁⟩ := denoteLs_view a (decI us) lu hdu
  obtain ⟨ids₂, hv₂, hd₂⟩ := denoteLs_view a (decI vs) lv hdv
  obtain ⟨e₁, t₁, s₁⟩ := lsNodeW_store hS.arena.1 hu (by exact hv₁)
  obtain ⟨e₂, t₂, s₂⟩ := lsNodeW_store hS.arena.1 hv (by exact hv₂)
  rw [e₁, e₂] at hl
  simp only [List.headD_cons, List.tail_cons] at hl
  have hR₀ : ArenaR (m.set64 CTL 192 0) a :=
    ArenaR.frame (by decide) c192_not_arena (reset_frame m) hS.arena.1
  have hpool : (m.set64 CTL 192 0).arr64 POOL = m.arr64 POOL :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hpool1 : (m.set64 CTL 192 0).arr64 POOL1 = m.arr64 POOL1 :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hpoolv := vpool_congr hpool hpool1
  have htop := (hS.arena.1).lit.1.top41
  have hl₁ := lvsR_of_slice hR₀ ids₁ lu _ _ (by rw [hpoolv]; exact s₁) (by omega) hd₁
  have hl₂ := lvsR_of_slice hR₀ ids₂ lv _ _ (by rw [hpoolv]; exact s₂) (by omega) hd₂
  obtain ⟨-, hz⟩ := equivsW_ok (nameN_rel _ hS.nwf) n _ _ _ _ _ _ _ _ _ hl₁ hl₂ hl
  rcases rcdK_res h with rfl | rfl
  · exact .inl rfl
  · rw [hz]; exact encO_three _

end enc

/-- `lvls_eq_c` does not return below the fuel `2`. -/
theorem lvlsEqC_small (p : Prog) (hp : p.lookup "lvls_eq_c" = some lvlsEqCL) (n : Nat) (hn : n < 2)
    (vs : List Word) (m : Mem) : callW p n "lvls_eq_c" vs m = none := by
  rcases Nat.lt_or_ge n 1 with h0 | h1
  · have : n = 0 := by omega
    subst this; exact callW_zero _ _ _ _
  · have : n = 1 := by omega
    subst this
    cases hc : callW p 1 "lvls_eq_c" vs m with
    | none => rfl
    | some q =>
      exfalso
      obtain ⟨t, -, hF⟩ := triple_of_callW (p := p) (n := 1) (f := "lvls_eq_c") (args := vs)
        (s₀ := ⟨m, Locals.init []⟩) (Q := fun _ _ => False) (by
          rw [invoke_eq _ hp]
          simp only [callFn, lvlsEqCL]
          vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
            callW_spec p 0 "lsq_find", callW_spec p 0 "lvls_eq_rec"] <;>
          simp_all [callW_zero]) hc
      exact hF

section sims
variable (p : Prog) (hcl : CoreStageClosed p) (hL : LvlCacheProg p)
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

include hcl hL in
/-- **`lvl_eq_c` under `StageT`, the verdict word exact** (replaces `IndStubs.lvlEqStub_spec` for a
caller carrying `StageT` and the two handles' readbacks). -/
theorem lvlEqC_simTE (n : Nat) {m : Mem} {a : AState} (hS : StageT dn vis fe m a) (u v : Word)
    (hu : H u) (hv : H v) (lu lv : ConLeche.Level) (hdu : denoteL a.store.ls (decI u) = some lu)
    (hdv : denoteL a.store.ls (decI v) = some lv) :
    Sim (callW p n "lvl_eq_c" [u, v] m) (lvlEq? (decI u) (decI v)) a
      (fun r x m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ decLvlEq m' r x) := by
  intro r m' e
  obtain ⟨x, a', hrun, hT', hg, hd, -⟩ :=
    lvlEqC_simT p hcl hL hL.c n hS u v hu hv lu lv hdu hdv r m' e
  refine ⟨x, a', hrun, hT', hg, decLvlEq_of_decO hd ?_⟩
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [lvlEqC_small p hL.c n hn] at e; cases e
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (lvlEqC_spec p hL k _ u v) e
  obtain ⟨M, hC⟩ := hS.core
  exact lvlEqCW_enc hC k u v hu hv lu lv hdu hdv _ hW

include hcl hL in
/-- **`lvls_eq_c` under `StageT`** (replaces `RecCheckSpec/TcmLook.lvlsEqStub_spec` for a caller carrying
`StageT`), from lane `whnf`'s `lvlsEqC_refines`: no readback hypothesis (a returning run read both
handles, `StoreDen.lsAll`). -/
theorem lvlsEqC_simT (n : Nat) {m : Mem} {a : AState} (hS : StageT dn vis fe m a) (us vs : Word)
    (hu : H us) (hv : H vs) :
    Sim (callW p n "lvls_eq_c" [us, vs] m) (lvlsEq? (decI us) (decI vs)) a
      (fun r x m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ decLvlEq m' r x) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · intro r m' h; rw [lvlsEqC_small p hL.cs n hn] at h; cases h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  intro r m' e
  obtain ⟨x, a', hrun, hT', hg, hd, -⟩ := StageT.sim_core hcl (by decide) hS
    (fun s₀ M hC => lvlsEqC_refines p hL k s₀ a dn vis fe M 0 hC us vs hu hv) r m' e
  refine ⟨x, a', hrun, hT', hg, decLvlEq_of_decO hd ?_⟩
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (lvlsEqC_spec p hL k _ us vs) e
  obtain ⟨M, hC⟩ := hS.core
  exact lvlsEqCW_enc hC k us vs hu hv _ hW

end sims

end L.Ind
