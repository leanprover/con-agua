import ConAgua.Arena.IndInstallSpec.PartsAt
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndPartsSpec.RecTW
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr

/-!
# BlockRawRec: `ConRon.Arena.blockRawRec`, `ConRon.Arena.piDomsMentionAny`

The refinement theorems `piDomsMentionAny_refines`, `blockRawRec_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

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
  simp only [pdmK]; rw [ite_eq_right h, ite_eq_left h6]
theorem pdmK_f (h : v ≠ []) (h6 : ¬ v.headD 0 ≠ 6) :
    pdmK n no nl f m v = pdmK2 n no nl f v (maConstWk n m no nl (v.getD 1 0)) := by
  simp only [pdmK]; rw [ite_eq_right h, ite_eq_right h6]
theorem pdmK2_hit (h : b ≠ 0) : pdmK2 n no nl f v (some (b, m1)) = some ([1], m1) := by
  simp only [pdmK2]; exact ite_eq_left h
theorem pdmK2_miss (h : ¬ b ≠ 0) : pdmK2 n no nl f v (some (b, m1)) =
    pdmK3 (pdmW n m1 no nl (f - 1) (v.getD 2 0)) := by simp only [pdmK2]; exact ite_eq_right h
theorem pdmK3_some : pdmK3 (some (r, m1)) = some ([r.headD 0], m1) := rfl
end arms
attribute [ind_grind] pdmW_f0 pdmW_go pdmK_nil pdmK_nf pdmK_f pdmK2_hit pdmK2_miss pdmK3_some

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
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have htag : ¬ ((decE e).tag == ETag.forallE) = true := by
        simp only [beq_iff_eq]; rw [decE_tag_forall _ he]; rw [← hhd]; exact h6
      refine ⟨false, a, ?_, rfl, rfl, ⟨mp, hM⟩, hS, IWGrow.refl _⟩
      simp only [ConRon.Arena.piDomsMentionAny, htag]; rfl
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
    rcases hma : maConstWk n m no nl (tfld m FORALL (tierW e) (idxW e) 0) with _ | ⟨b, m1⟩
    · rw [hma] at h; simp [pdmK2] at h
    rw [hma] at h
    cases n with
    | zero => simp [maConstWk] at hma
    | succ n' =>
    obtain ⟨c, hrun, hbc, hM1, hS1, hg1⟩ := maConstW_ok n' dn fe vis m m1 a no nl _ b ws mp hma hS hty hws hwlt hM
    simp only [ConRon.Arena.piDomsMentionAny, htag, ite_true, StateT.run_bind, viewBind_run' _ a, hvb]
    rw [hnm']
    simp only [except_ok_bind, StateT.run_bind, hrun]
    by_cases hb0 : b ≠ 0
    · rw [pdmK2_hit (h := hb0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hc : c = true := by rw [← hbc]; simpa using hb0
      subst hc
      exact ⟨true, a, rfl, rfl, rfl, ⟨_, hM1⟩, hS1, hg1⟩
    rw [pdmK2_miss (h := hb0)] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    have hc : c = false := by rw [← hbc]; simpa using hb0
    subst hc
    simp only [Bool.false_eq_true, ite_false]
    obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl; rw [pdmK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hf1 : (f - 1).toNat = F := partsPred_of hF
    obtain ⟨b2, a2, hr2, hR2, ha2, hM2, hS2, hg2⟩ := ih m1 a (f - 1) _ ∅ hS1 hb (hns.grow (OMono.decHL _ _) hg1)
      (Nat.le_trans hnb hg1.1) hM1 r2 m2 h2
    rw [hf1, ha2, hnm'] at hr2
    exact ⟨b2, a, hr2, by rw [hR2]; rfl, rfl, hM2, hS2, hg1.trans hg2⟩

/-- **`pi_doms_mention_any` refines `piDomsMentionAny`** (through `mentions_any_const`'s walk;
the names a handle slice below the top; any well-formed `mentions_any` memo on entry). -/
@[refines ConRon.Arena.piDomsMentionAny]
theorem piDomsMentionAny_refines (p : Prog) (hM : MaProg p)
    (hp : p.lookup "pi_doms_mention_any" = some piDomsMentionAny) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (no nl f e : Word) (names : List NIdx)
    (mp : Std.HashMap EIdx Bool) (hS : StageR dn vis fe s₀.mem a₀) (he : H e)
    (hns : DecB (fun m => decHL m no.toNat nl.toNat) s₀.mem names) (hnb : no.toNat + nl.toNat ≤ iwTop s₀.mem)
    (hmp : maMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_doms_mention_any" [no, nl, f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.piDomsMentionAny names f.toNat (decE e)) a₀ ∧
      r = [if AM.res (ConRon.Arena.piDomsMentionAny names f.toNat (decE e)) a₀ then 1 else 0] ∧
      AM.st (ConRon.Arena.piDomsMentionAny names f.toNat (decE e)) a₀ = a₀ ∧
      (∃ mp', maMR s'.mem mp') ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ :=
  triple_post (pdm_spec p hM hp n s₀ no nl f e) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hr, hst, hM', hS', hg⟩ := Sim.run (pdmW_sim n s₀.mem a₀ f e mp hS he hns hnb hmp) hm
    ⟨hl, hok, hr, hst, hM', by rw [← hst] at hS'; rw [hst] at hS'; exact hS', hg⟩

/-- After the element's test. -/
def brrK (_n : Nat) (rest : Mem → Option (List Word × Mem)) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => if r.headD 0 ≠ 0 then some ([1], m1) else pdmK3 (rest m1)

/-- **The model of `block_raw_rec_member`.** -/
def brmW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, no, nl, coff, clen =>
    if clen = 0 then some ([0], m)
    else brrK n (fun m1 => brmW n m1 no nl (coff + 1) (clen - 1))
      (pdmW n m no nl CWF (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) coff) + 3)))

/-- **The model of `block_raw_rec_go`.** -/
def brgoW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, no, nl, moff, mlen =>
    if mlen = 0 then some ([0], m)
    else brrK n (fun m1 => brgoW n m1 no nl (moff + 1) (mlen - 1))
      (brmW n m no nl (rdW (m.arr64 IW) (rdW (m.arr64 IW) moff + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) moff + 3)))

section arms
variable (n : Nat) (m m1 : Mem) (no nl coff clen moff mlen : Word) (r : List Word)
  (rest : Mem → Option (List Word × Mem))
theorem brrK_hit (h : r.headD 0 ≠ 0) : brrK n rest (some (r, m1)) = some ([1], m1) := by
  simp only [brrK]; exact ite_eq_left h
theorem brrK_miss (h : ¬ r.headD 0 ≠ 0) : brrK n rest (some (r, m1)) = pdmK3 (rest m1) := by
  simp only [brrK]; exact ite_eq_right h
theorem brmW_nil (h : clen = 0) : brmW (n + 1) m no nl coff clen = some ([0], m) := by simp [brmW, h]
theorem brmW_cons (h : clen ≠ 0) : brmW (n + 1) m no nl coff clen =
    brrK n (fun m1 => brmW n m1 no nl (coff + 1) (clen - 1))
      (pdmW n m no nl CWF (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) coff) + 3))) := by
  simp [brmW, h]
theorem brgoW_nil (h : mlen = 0) : brgoW (n + 1) m no nl moff mlen = some ([0], m) := by simp [brgoW, h]
theorem brgoW_cons (h : mlen ≠ 0) : brgoW (n + 1) m no nl moff mlen =
    brrK n (fun m1 => brgoW n m1 no nl (moff + 1) (mlen - 1))
      (brmW n m no nl (rdW (m.arr64 IW) (rdW (m.arr64 IW) moff + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) moff + 3))) := by simp [brgoW, h]
end arms
attribute [ind_grind] brrK_hit brrK_miss brmW_nil brmW_cons brgoW_nil brgoW_cons

theorem brm_spec (p : Prog) (hM : MaProg p) (hpd : p.lookup "pi_doms_mention_any" = some piDomsMentionAny)
    (hp : p.lookup "block_raw_rec_member" = some blockRawRecMember) (n : Nat) :
    ∀ (s₀ : St) (no nl coff clen : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_raw_rec_member" [no, nl, coff, clen]
    ⦃fun r s' => LocEq s' s₀ ∧ brmW n s₀.mem no nl coff clen = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ no nl coff clen; rw [invoke_eq _ hp]; simp only [callFn, blockRawRecMember]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ no nl coff clen
    rw [invoke_eq _ hp]
    simp only [callFn, blockRawRecMember]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, pdm_spec p hM hpd n, ih] <;>
      finish (gen := 20) [rdW_eq, CWF]

theorem brgo_spec (p : Prog) (hM : MaProg p) (hpd : p.lookup "pi_doms_mention_any" = some piDomsMentionAny)
    (hm : p.lookup "block_raw_rec_member" = some blockRawRecMember)
    (hp : p.lookup "block_raw_rec_go" = some blockRawRecGo) (n : Nat) :
    ∀ (s₀ : St) (no nl moff mlen : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_raw_rec_go" [no, nl, moff, mlen]
    ⦃fun r s' => LocEq s' s₀ ∧ brgoW n s₀.mem no nl moff mlen = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ no nl moff mlen; rw [invoke_eq _ hp]; simp only [callFn, blockRawRecGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ no nl moff mlen
    rw [invoke_eq _ hp]
    simp only [callFn, blockRawRecGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, brm_spec p hM hpd hm n, ih] <;>
      finish (gen := 20) [rdW_eq]

/-- The post of the memo walks: the result a `Bool` word, the twin's state kept, a memo left. -/
def RawR {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (m : Mem) (a : AState) :
    List Word → Bool → Mem → AState → Prop :=
  fun r b m' a' => r = [if b then 1 else 0] ∧ a' = a ∧ (∃ mp', maMR m' mp') ∧ StageR dn vis fe m' a ∧ IWGrow m m'

/-- **One element of an `anyM`** (`brrK`): the element's test, then, if it fails, the rest. -/
theorem brrK_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {n : Nat}
    {rest : Mem → Option (List Word × Mem)} {mo : Option (List Word × Mem)} {hd tl : AM Bool} {m : Mem}
    {a : AState} (h1 : Sim mo hd a (RawR (dn := dn) (vis := vis) (fe := fe) m a))
    (h2 : ∀ m1 mp1, StageR dn vis fe m1 a → IWGrow m m1 → maMR m1 mp1 →
      Sim (rest m1) tl a (RawR (dn := dn) (vis := vis) (fe := fe) m1 a)) :
    Sim (brrK n rest mo) (do let b ← hd; if b then pure true else tl) a
      (RawR (dn := dn) (vis := vis) (fe := fe) m a) := by
  refine Sim.bindK (K := brrK n rest) (body := fun r1 m1 => if r1.headD 0 ≠ 0 then some ([1], m1)
    else pdmK3 (rest m1)) rfl (fun _ _ => rfl) h1 ?_
  rintro r1 b m1 a1 ⟨rfl, rfl, ⟨mp1, hM1⟩, hS1, hg1⟩
  cases b with
  | true =>
    simp only [ite_true, show (1 : Word) ≠ 0 by decide, List.headD_cons, ne_eq, not_false_eq_true]
    exact Sim.ret ⟨rfl, rfl, ⟨mp1, hM1⟩, hS1, hg1⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false, List.headD_cons, ne_eq, not_true_eq_false]
    refine Sim.congr (op := tl >>= pure) ?_ (bind_pure _)
    refine Sim.bindK (K := pdmK3) (body := fun r m => some ([r.headD 0], m)) rfl (fun _ _ => rfl)
      (h2 m1 mp1 hS1 hg1 hM1) ?_
    rintro r2 b2 m2 a2 ⟨rfl, rfl, hM2, hS2, hg2⟩
    exact Sim.ret ⟨rfl, rfl, hM2, hS2, hg1.trans hg2⟩

/-- **`block_raw_rec_member`'s model refines a member's `ctors.anyM`.** -/
theorem brmW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {no nl : Word}
    {names : List NIdx} (n : Nat) : ∀ (m : Mem) (a : AState) (coff clen : Word) (cs : List (IConstantVal × Nat))
    (mp : Std.HashMap EIdx Bool),
    StageR dn vis fe m a → DecB (fun m => decPL m (decCN m) coff.toNat clen.toNat) m cs →
    (clen = 0 ∨ coff.toNat + clen.toNat ≤ iwTop m) → DecB (fun m => decHL m no.toNat nl.toNat) m names →
    no.toNat + nl.toNat ≤ iwTop m → maMR m mp →
    Sim (brmW n m no nl coff clen)
      (cs.anyM fun c => ConRon.Arena.piDomsMentionAny names coreWalkFuel c.1.type) a
      (RawR (dn := dn) (vis := vis) (fe := fe) m a) := by
  induction n with
  | zero => intro m a coff clen cs mp _ _ _ _ _ _ r m' h; simp [brmW] at h
  | succ n ih =>
    intro m a coff clen cs mp hS hcs0 hcb hns hnb hM
    by_cases hl : clen = 0
    · rw [brmW_nil n m no nl coff clen hl]
      subst hl
      have : cs = [] := by have := decPL_length _ hcs0; simpa using this
      subst this
      exact Sim.ret ⟨rfl, rfl, ⟨mp, hM⟩, hS, IWGrow.refl _⟩
    rw [brmW_cons n m no nl coff clen hl]
    have hcs : PSlR decCN cs coff clen m := ⟨hcs0, hcb.resolve_left hl⟩
    obtain ⟨pc, ⟨cv, nF⟩, cs', rfl, hw, hpb, hc0, hcs'⟩ := partsPSl_cons hcs hl
    obtain ⟨⟨cvp, hcvp, hcv⟩, -⟩ := decCN_some (show decCN (truncM m) pc = some (cv, nF) from hc0)
    obtain ⟨hcw, hcvb, -⟩ := partsIwRd hcvp (UInt64.toNat_ofNat_of_lt' hpb)
    obtain ⟨htyl, htye⟩ := partsCVType hcv (UInt64.toNat_ofNat_of_lt' hcvb)
    rw [hw, hcw, partsAnyM_cons]
    have h1 := pdmW_sim (names := names) n m a CWF _ mp hS htyl hns hnb hM
    rw [CWF_eq, show decE (rdW (m.arr64 EREC) (UInt64.ofNat cvp + 3)) = cv.type from htye] at h1
    exact brrK_sim h1 fun m1 mp1 hS1 hg1 hM1 => ih m1 a (coff + 1) (clen - 1) cs' mp1 hS1
      (hcs'.grow decCN_mono hg1).1 (Or.inr (hcs'.grow decCN_mono hg1).2) (hns.grow (OMono.decHL _ _) hg1)
      (Nat.le_trans hnb hg1.1) hM1

/-- **`block_raw_rec_go`'s model refines the members' `anyM`.** -/
theorem brgoW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {no nl : Word}
    {names : List NIdx} (n : Nat) : ∀ (m : Mem) (a : AState) (moff mlen : Word) (ms : List MemberShape)
    (mp : Std.HashMap EIdx Bool),
    StageR dn vis fe m a → DecB (fun m => decPL m (decMS m) moff.toNat mlen.toNat) m ms →
    (mlen = 0 ∨ moff.toNat + mlen.toNat ≤ iwTop m) → DecB (fun m => decHL m no.toNat nl.toNat) m names →
    no.toNat + nl.toNat ≤ iwTop m → maMR m mp →
    Sim (brgoW n m no nl moff mlen)
      (ms.anyM fun ms => ms.ctors.anyM fun c => ConRon.Arena.piDomsMentionAny names coreWalkFuel c.1.type) a
      (RawR (dn := dn) (vis := vis) (fe := fe) m a) := by
  induction n with
  | zero => intro m a moff mlen ms mp _ _ _ _ _ _ r m' h; simp [brgoW] at h
  | succ n ih =>
    intro m a moff mlen ms mp hS hms0 hmb hns hnb hM
    by_cases hl : mlen = 0
    · rw [brgoW_nil n m no nl moff mlen hl]
      subst hl
      have : ms = [] := by have := decPL_length _ hms0; simpa using this
      subst this
      exact Sim.ret ⟨rfl, rfl, ⟨mp, hM⟩, hS, IWGrow.refl _⟩
    rw [brgoW_cons n m no nl moff mlen hl]
    have hms : PSlR decMS ms moff mlen m := ⟨hms0, hmb.resolve_left hl⟩
    obtain ⟨pc, ms0, ms', rfl, hw, hpb, hm0, hms'⟩ := partsPSl_cons hms hl
    have hd0 : decMS (truncM m) pc = some ms0 := hm0
    simp only [decMS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hd0
    obtain ⟨cvp, -, cvT, -, nIdx, -, ctors, hct, rfl⟩ := hd0
    obtain ⟨o, l, ho, hl', hdc, hcb⟩ := partsAt decCN_mono hct
    have hpw : (UInt64.ofNat pc).toNat = pc := UInt64.toNat_ofNat_of_lt' hpb
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    have hp2 : (UInt64.ofNat pc + 2).toNat = pc + 2 := by
      have := partsIwLt ho; rw [UInt64.toNat_add, hpw]; simp; omega
    have hp3 : (UInt64.ofNat pc + 3).toNat = pc + 3 := by
      have := partsIwLt hl'; rw [UInt64.toNat_add, hpw]; simp; omega
    obtain ⟨how, -, -⟩ := partsIwRd ho hp2
    obtain ⟨hlw, -, -⟩ := partsIwRd hl' (by rw [hp3])
    rw [hw, how, hlw, ofNat_toNat_word, ofNat_toNat_word, partsAnyM_cons]
    exact brrK_sim (brmW_sim n m a o l ctors mp hS hdc hcb hns hnb hM) fun m1 mp1 hS1 hg1 hM1 =>
      ih m1 a (moff + 1) (mlen - 1) ms' mp1 hS1 (hms'.grow decMS_mono hg1).1
        (Or.inr (hms'.grow decMS_mono hg1).2) (hns.grow (OMono.decHL _ _) hg1) (Nat.le_trans hnb hg1.1) hM1

/-- **The model of `block_raw_rec`** (at exec fuel `n + 1`). -/
def brrW (n : Nat) (m : Mem) (p : Word) : Option (List Word × Mem) :=
  match memberNamesW n m p with
  | none => none
  | some (r1, m1) =>
    match brgoW n m1 (r1.headD 0) (r1.tail.headD 0) (rdW (m1.arr64 IW) p) (rdW (m1.arr64 IW) (p + 1)) with
    | none => none
    | some (r2, m2) => some ([r2.headD 0], m2)

theorem brr_spec (p : Prog) (hM : MaProg p) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "member_names_copy" = some memberNamesCopy)
    (hn : p.lookup "block_shape_member_names" = some blockShapeMemberNames)
    (hpd : p.lookup "pi_doms_mention_any" = some piDomsMentionAny)
    (hm : p.lookup "block_raw_rec_member" = some blockRawRecMember)
    (hg : p.lookup "block_raw_rec_go" = some blockRawRecGo)
    (hp : p.lookup "block_raw_rec" = some blockRawRec) (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_raw_rec" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ brrW n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockRawRec]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      blockShapeMemberNames_spec p ha hc hn n, brgo_spec p hM hpd hm hg n] <;>
    finish (gen := 20) [brrW, rdW_eq]

/-- **`block_raw_rec` refines `blockRawRec`** (through `mentions_any_const`'s walk; the members'
slice of the shape record below the pool's top, `hsrc`; any well-formed `mentions_any` memo on
entry). -/
@[refines ConRon.Arena.blockRawRec]
theorem blockRawRec_refines (p : Prog) (hM : MaProg p) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "member_names_copy" = some memberNamesCopy)
    (hn : p.lookup "block_shape_member_names" = some blockShapeMemberNames)
    (hpd : p.lookup "pi_doms_mention_any" = some piDomsMentionAny)
    (hm : p.lookup "block_raw_rec_member" = some blockRawRecMember)
    (hg : p.lookup "block_raw_rec_go" = some blockRawRecGo)
    (hp : p.lookup "block_raw_rec" = some blockRawRec) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (q : Word) (bs : BlockShape)
    (mp : Std.HashMap EIdx Bool) (hS : StageR dn vis fe s₀.mem a₀)
    (hq : DecB (fun m => decBS m q.toNat) s₀.mem bs)
    (hsrc : ∀ o l, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l → o + l ≤ iwTop s₀.mem)
    (hmp : maMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_raw_rec" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.blockRawRec ⟨bs⟩) a₀ ∧
      AM.st (ConRon.Arena.blockRawRec ⟨bs⟩) a₀ = a₀ ∧
      r = [if AM.res (ConRon.Arena.blockRawRec ⟨bs⟩) a₀ then 1 else 0] ∧
      (∃ mp', maMR s'.mem mp') ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (brr_spec p hM ha hc hn hpd hm hg hp n s₀ q) ?_
  rintro r s' ⟨hl, hm'⟩
  have hT : iwTop s₀.mem < 2 ^ 64 := (rdW (s₀.mem.arr64 CTL) 200).toNat_lt
  obtain ⟨hI1, hE1, hsz, hEs, hcl⟩ := hS.2
  have hqt : decBS (truncM s₀.mem) q.toNat = some bs := hq
  have hq' : decBS s₀.mem q.toNat = some bs := hq.get (decBS_mono _)
  obtain ⟨hmem, -, -, -, -, -, hpr⟩ := decBS_some hqt
  have hq8 : q.toNat + 8 < iwTop s₀.mem := by
    simp only [iwB, bool?, Option.map_eq_some_iff] at hpr
    obtain ⟨w, hw, -⟩ := hpr
    exact (truncM_iw_get hw).1
  obtain ⟨o, l, ho, hlw, hdm, hob0⟩ := partsAt decMS_mono hmem
  have hoN : iwN s₀.mem q.toNat = some o.toNat := by rw [← iwN_truncM (by omega)]; exact ho
  have hlN : iwN s₀.mem (q.toNat + 1) = some l.toNat := by rw [← iwN_truncM (by omega)]; exact hlw
  have hdm' : decPL (truncM s₀.mem) (decMS (truncM s₀.mem)) o.toNat l.toNat = some bs.members := hdm
  have hptr : ∀ o' l' j v, iwN s₀.mem q.toNat = some o' → iwN s₀.mem (q.toNat + 1) = some l' → j < l' →
      iwN s₀.mem (o' + j) = some v → v < iwTop s₀.mem := by
    intro o' l' j v h1 h2 hj hv
    rw [hoN] at h1; rw [hlN] at h2
    simp only [Option.some.injEq] at h1 h2; subst h1 h2
    obtain ⟨v', hv', hms⟩ := decPL_getH (truncM s₀.mem) hdm' j hj
    have hlt := partsIwLt hv'
    rw [iwN_truncM hlt, hv] at hv'
    simp only [Option.some.injEq] at hv'; subst hv'
    obtain ⟨⟨c, hc', -⟩, -, -⟩ := decMS_some hms
    exact partsIwLt hc'
  unfold brrW at hm'
  rcases h1 : memberNamesW n s₀.mem q with _ | ⟨r1, m1⟩
  · rw [h1] at hm'; cases hm'
  rw [h1] at hm'
  simp only at hm'
  obtain ⟨hr1, hd1, hg1, hf1, ht1⟩ := memberNamesW_dec h1 hsz hcl hq' (by omega) hsrc hptr
  have hroom := memberNamesW_room h1 hsz
  have hk : bs.k = l.toNat := by rw [BlockShape.k, decPL_length _ hdm']
  obtain ⟨hlr, -, -⟩ := partsIwRd hlw (show (q + 1).toNat = q.toNat + 1 by rw [UInt64.toNat_add]; simp; omega)
  have hS1 : StageR dn vis fe m1 a₀ := stage_frame_iw hS hf1 (by
    rw [← ht1, hk]; rw [hlr, ofNat_toNat_word] at hroom; simp only [iwTop] at hroom ⊢; omega)
  subst hr1
  simp only [List.headD_cons, List.tail_cons] at hm'
  obtain ⟨how, -, -⟩ := partsIwRd ho rfl
  rw [partsRdIW_grow hg1 (by omega), partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)] at hm'
  have hoW : rdW (s₀.mem.arr64 IW) q = o := by rw [how, ofNat_toNat_word]
  rw [hoW, hlr, ofNat_toNat_word] at hm'
  have hkW : (UInt64.ofNat bs.k).toNat = bs.k := by rw [hk]; simp
  have hsim := brgoW_sim (no := rdW (s₀.mem.arr64 CTL) 200) (nl := UInt64.ofNat bs.k) (names := bs.memberNames) n m1 a₀ o l bs.members mp hS1
    ((show DecB (fun m => decPL m (decMS m) o.toNat l.toNat) s₀.mem bs.members from hdm).grow
      (OMono.decPL decMS_mono _ _) hg1)
    (hob0.imp_right fun h => Nat.le_trans h hg1.1)
    (by rw [hkW]; exact decHL_decB hd1 (Nat.le_of_eq ht1)) (by rw [hkW]; omega)
    (memoRG_frame maSch maSch_wf bmKey (fun w : Word => w != 0) [IW] [200] (by decide) (by simp [maSch])
      s₀.mem m1 hf1 mp hmp)
  rcases h2 : brgoW n m1 (rdW (s₀.mem.arr64 CTL) 200) (UInt64.ofNat bs.k) o l with _ | ⟨r2, m2⟩
  · rw [h2] at hm'; cases hm'
  rw [h2] at hm'
  obtain ⟨rfl, hm2⟩ := Prod.mk.inj (Option.some.inj hm')
  obtain ⟨b, a', hrun, hR⟩ := hsim r2 m2 h2
  obtain ⟨hr2, ha', hM2, hS2, hg2⟩ := hR
  subst ha'
  have hrun' : (ConRon.Arena.blockRawRec ⟨bs⟩).run a' = .ok (b, a') := hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  rw [hm2] at hM2 hS2 hg2
  refine ⟨hl, hok, hst, by rw [hres, hr2]; rfl, hM2, hS2, hg1.trans hg2⟩

end L.Ind

end
