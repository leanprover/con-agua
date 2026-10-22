import ConAgua.Arena.IndPartsSpec15
import ConAgua.Arena.IndInstallSpec4

/-!
# Refinements of `IndInstall`, part 5 (lane `indproofs2`, helper `parts`)

`piDomsMentionAny` (through `mentions_any_const`, lane `indproofs`' memo walk) and `blockRawRec`
(the two `anyM`s recursive).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `pi_doms_mention_any` -/

/-- `mentions_any_const`'s model at every exec fuel. -/
def maConstWk : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | k + 1, m, no, nl, e => maConstW k m no nl e

theorem mentionsAnyConst_specK (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hc : p.lookup "sl_contains" = some slContains)
    (hf : p.lookup "ma_find" = some (memoFindG maSch)) (hput : p.lookup "ma_put" = some (memoPutG maSch))
    (hgo : p.lookup "mentions_any_go" = some mentionsAnyGo)
    (hnode : p.lookup "mentions_any_node" = some mentionsAnyNode)
    (hcl : p.lookup "ma_clear" = some (memoClearG maSch))
    (hp : p.lookup "mentions_any_const" = some mentionsAnyConst) (n : Nat) (s₀ : St) (no nl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "mentions_any_const" [no, nl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ maConstWk n s₀.mem no nl e = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases n with
  | zero => rw [invoke_eq _ hp]; simp only [callFn, mentionsAnyConst]; vcgen [exec] <;> grind
  | succ n => exact mentionsAnyConst_spec p hv hc hf hput hgo hnode hcl hp n s₀ no nl e

/-- After the recursive call. -/
def pdmK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

mutual
/-- **The model of `pi_doms_mention_any`.** -/
def pdmW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, no, nl, f, e => if f = 0 then none else pdmK n no nl f m (eViewW m e)
/-- After `e_view`. -/
def pdmK (n : Nat) (no nl f : Word) (m : Mem) (v : List Word) : Option (List Word × Mem) :=
  if v = [] then none
  else if v.headD 0 ≠ 6 then some ([0], m)
  else pdmK2 n no nl f v (maConstWk n m no nl (v.getD 1 0))
/-- After `mentions_any_const`. -/
def pdmK2 (n : Nat) (no nl f : Word) (v : List Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (b, m1) => if b ≠ 0 then some ([1], m1) else pdmK3 (pdmW n m1 no nl (f - 1) (v.getD 2 0))
end

section arms
variable (n : Nat) (m m1 : Mem) (no nl f e b : Word) (v r : List Word)
theorem pdmW_f0 (h : f = 0) : pdmW (n + 1) m no nl f e = none := by simp [pdmW, h]
theorem pdmW_go (h : f ≠ 0) : pdmW (n + 1) m no nl f e = pdmK n no nl f m (eViewW m e) := by
  simp [pdmW, h]
theorem pdmK_nil (h : v = []) : pdmK n no nl f m v = none := by simp [pdmK, h]
theorem pdmK_nf (h : v ≠ []) (h6 : v.headD 0 ≠ 6) : pdmK n no nl f m v = some ([0], m) := by
  simp only [pdmK]; rw [if_neg h, if_pos h6]
theorem pdmK_f (h : v ≠ []) (h6 : ¬ v.headD 0 ≠ 6) :
    pdmK n no nl f m v = pdmK2 n no nl f v (maConstWk n m no nl (v.getD 1 0)) := by
  simp only [pdmK]; rw [if_neg h, if_neg h6]
theorem pdmK2_hit (h : b ≠ 0) : pdmK2 n no nl f v (some (b, m1)) = some ([1], m1) := by
  simp only [pdmK2]; exact if_pos h
theorem pdmK2_miss (h : ¬ b ≠ 0) : pdmK2 n no nl f v (some (b, m1)) =
    pdmK3 (pdmW n m1 no nl (f - 1) (v.getD 2 0)) := by simp only [pdmK2]; exact if_neg h
theorem pdmK3_some : pdmK3 (some (r, m1)) = some ([r.headD 0], m1) := rfl
end arms
attribute [ind_grind] pdmW_f0 pdmW_go pdmK_nil pdmK_nf pdmK_f pdmK2_hit pdmK2_miss pdmK3_some

/-- The lookups of `mentions_any_const`. -/
structure MaProg (p : Prog) : Prop where
  view : p.lookup "e_view" = some eView
  cont : p.lookup "sl_contains" = some slContains
  find : p.lookup "ma_find" = some (memoFindG maSch)
  put : p.lookup "ma_put" = some (memoPutG maSch)
  go : p.lookup "mentions_any_go" = some mentionsAnyGo
  node : p.lookup "mentions_any_node" = some mentionsAnyNode
  clr : p.lookup "ma_clear" = some (memoClearG maSch)
  ma : p.lookup "mentions_any_const" = some mentionsAnyConst

theorem pdm_spec (p : Prog) (hM : MaProg p) (hp : p.lookup "pi_doms_mention_any" = some piDomsMentionAny)
    (n : Nat) : ∀ (s₀ : St) (no nl f e : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_doms_mention_any" [no, nl, f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ pdmW n s₀.mem no nl f e = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ no nl f e; rw [invoke_eq _ hp]; simp only [callFn, piDomsMentionAny]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ no nl f e
    rw [invoke_eq _ hp]
    simp only [callFn, piDomsMentionAny]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, eViewSpec4 p hM.view n,
        mentionsAnyConst_specK p hM.view hM.cont hM.find hM.put hM.go hM.node hM.clr hM.ma n, ih] <;>
      finish (gen := 20)

/-- `e_view`'s first word is the handle's tag (lane `defeq`'s `quick_eViewW_head`). -/
theorem partsEView_head (m : Mem) (h : Word) (hne : L.Ind.eViewW m h ≠ []) :
    (L.Ind.eViewW m h).headD 0 = h >>> 28 := by
  unfold L.Ind.eViewW at hne ⊢
  by_cases c1 : (4294967295 : Word) < h
  · simp [c1] at hne
  by_cases c2 : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [c1, c2] at hne
  simp only [c1, c2, ite_false] at hne ⊢
  by_cases g0 : h >>> 28 = 0
  · simp only [g0, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g0, ite_false] at hne ⊢
  by_cases g1 : h >>> 28 = 1
  · simp only [g1, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g1, ite_false] at hne ⊢
  by_cases g2 : h >>> 28 = 2
  · simp only [g2, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g2, ite_false] at hne ⊢
  by_cases g3 : h >>> 28 = 3
  · simp only [g3, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g3, ite_false] at hne ⊢
  by_cases g4 : h >>> 28 = 4
  · simp only [g4, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g4, ite_false] at hne ⊢
  by_cases g5 : h >>> 28 = 5
  · simp only [g5, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g5, ite_false] at hne ⊢
  by_cases g6 : h >>> 28 = 6
  · simp only [g6, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g6, ite_false] at hne ⊢
  by_cases g7 : h >>> 28 = 7
  · simp only [g7, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g7, ite_false] at hne ⊢
  by_cases g8 : h >>> 28 = 8
  · simp only [g8, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g8, ite_false] at hne ⊢
  by_cases g9 : h >>> 28 = 9
  · simp only [g9, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g9, ite_false] at hne ⊢
  exact absurd rfl hne

/-- **`pi_doms_mention_any`'s model refines `piDomsMentionAny`.** -/
theorem pdmW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {no nl : Word}
    {names : List NIdx} (n : Nat) : ∀ (m : Mem) (a : AState) (f e : Word) (mp : Std.HashMap EIdx Bool),
    StageR dn vis fe m a → H e → DecB (fun m => decHL m no.toNat nl.toNat) m names →
    no.toNat + nl.toNat ≤ iwTop m → maMR m mp →
    Sim (pdmW n m no nl f e) (ConRon.Arena.piDomsMentionAny names f.toNat (decE e)) a
      (fun r b m' a' => r = [if b then 1 else 0] ∧ a' = a ∧ (∃ mp', maMR m' mp') ∧
        StageR dn vis fe m' a ∧ IWGrow m m') := by
  induction n with
  | zero => intro m a f e mp _ _ _ _ _ r m' h; simp [pdmW] at h
  | succ n ih =>
    intro m a f e mp hS he hns hnb hM r m' h
    by_cases hf : f = 0
    · rw [pdmW_f0 n m no nl f e hf] at h; cases h
    rw [pdmW_go n m no nl f e hf] at h
    obtain ⟨F, hF⟩ : ∃ F, f.toNat = F + 1 :=
      ⟨f.toNat - 1, by have : f.toNat ≠ 0 := fun e => hf (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
    by_cases hv : eViewW m e = []
    · rw [pdmK_nil (h := hv)] at h; cases h
    have hhd := partsEView_head m e hv
    rw [hF]
    by_cases h6 : (eViewW m e).headD 0 ≠ 6
    · rw [pdmK_nf (h := hv) (h6 := h6)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have htag : ¬ ((decE e).tag == ETag.forallE) = true := by
        simp only [beq_iff_eq]; rw [decE_tag_forall _ he]; rw [← hhd]; exact h6
      refine ⟨false, a, ?_, rfl, rfl, ⟨mp, hM⟩, hS, IWGrow.refl _⟩
      simp only [ConRon.Arena.piDomsMentionAny, htag, if_false]; rfl
    have hg6 : e >>> 28 = 6 := by rw [← hhd]; simpa using h6
    rw [pdmK_f (h := hv) (h6 := h6)] at h
    obtain ⟨hvok, hew⟩ := eViewW_forall m e hg6 hv
    have hR := hS.1.arena.1
    obtain ⟨-, hty, hb⟩ := view_forall m a hR e he hvok hg6
    have hvb := viewBind_forall m a hR e he hvok hg6
    have htag : ((decE e).tag == ETag.forallE) = true := by
      simp only [beq_iff_eq]; exact (decE_tag_forall _ he).mpr hg6
    rw [hew] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    have hns' := hns.get (OMono.decHL _ _)
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    obtain ⟨ws, hws, hnm', hwlt⟩ := slR_of_decHL m _ _ _ hns' (by omega)
    rw [ofNat_toNat_word, ofNat_toNat_word] at hws
    cases hma : maConstWk n m no nl (rdW (m.arr64 FAREC) (idxW e * 4 + tierW e * 2)) with
    | none => rw [hma] at h; simp [pdmK2] at h
    | some x =>
    obtain ⟨b, m1⟩ := x
    rw [hma] at h
    cases n with
    | zero => simp [maConstWk] at hma
    | succ n' =>
    obtain ⟨c, hrun, hbc, hM1, hS1, hg1⟩ := maConstW_ok n' dn fe vis m m1 a no nl _ b ws mp hma hS hty hws hwlt hM
    simp only [ConRon.Arena.piDomsMentionAny, htag, if_true, StateT.run_bind, viewBind_run' _ a, hvb]
    rw [hnm']
    simp only [except_ok_bind, StateT.run_bind, hrun]
    by_cases hb0 : b ≠ 0
    · rw [pdmK2_hit (h := hb0)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hc : c = true := by rw [← hbc]; simpa using hb0
      subst hc
      exact ⟨true, a, rfl, rfl, rfl, ⟨_, hM1⟩, hS1, hg1⟩
    rw [pdmK2_miss (h := hb0)] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    have hc : c = false := by rw [← hbc]; simpa using hb0
    subst hc
    simp only [Bool.false_eq_true, if_false]
    cases h2 : pdmW (n' + 1) m1 no nl (f - 1) (rdW (m.arr64 FAREC) (idxW e * 4 + tierW e * 2 + 1)) with
    | none => rw [h2] at h; cases h
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    rw [h2, pdmK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hf1 : (f - 1).toNat = F := partsPred_of hF
    obtain ⟨b2, a2, hr2, hR2, ha2, hM2, hS2, hg2⟩ := ih m1 a (f - 1) _ ∅ hS1 hb (hns.grow (OMono.decHL _ _) hg1)
      (Nat.le_trans hnb hg1.1) hM1 r2 m2 h2
    rw [hf1, ha2, hnm'] at hr2
    exact ⟨b2, a, hr2, by rw [hR2]; rfl, rfl, hM2, hS2, hg1.trans hg2⟩

end L.Ind
