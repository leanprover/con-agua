module

public import ConAgua.Arena.RecClassSpec.MnW
public import ConAgua.Arena.RecClassSpec.RuProg
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndRealAbsSim
import ConAgua.Arena.LdRd
import ConAgua.Arena.RecClassSpec.MjW
import ConAgua.Arena.RecClassSpec.PiBWRoom
import ConAgua.Arena.RecClassSpec.Rec2AppendWDec
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.RecClass

@[expose] public section

/-!
# PrefixBinders: `ConRon.Arena.ClassGen.prefixBinders`

The refinement theorems `classGenPrefixBinders_refines` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Models -/

def fcK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

theorem fcK_some (r : List Word) (m : Mem) : fcK (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl

attribute [ind_grind] fcK_some

l_model findCtorGo_spec (p : Prog) (h : PbProg p)
  fns [h.fcg ↦ fcgW list]
  grind [arena_grind]

l_model findCtor_spec (p : Prog) (h : PbProg p)
  fns [h.fc ↦ fcW list]
  specs [findCtorGo_spec p h n]
  grind [arena_grind]

/-- **The slot walk is its models `psW`, `smW`, `snW`** (generated; fuel `n`). -/
l_model slots_spec (p : Prog) (h : PbProg p)
  fns [h.psg ↦ psW list, h.psm ↦ smW list, h.psn ↦ snW list]
  specs [findCtor_spec p h n, classGenMotiveTy_spec p h.toMtProg n, classGenMinorTy_spec p h.toMnProg n,
    slCons_specW p h.alloc h.copy h.cons n]
  grind [arena_grind] finish [] gen 20

l_model prefixBinders_spec (p : Prog) (h : PbProg p)
  fns [h.pb ↦ gpbW list]
  specs [ftdsF_spec p h.ad n, (slots_spec p h n).1, slAppend_specW p h.alloc h.copy h.app n]
  grind [arena_grind]

/-! ## Finding the constructor -/

/-- What `find_ctor(_go)` returns. -/
def FcRes (m : Mem) (r : List Word) : Option ClassCtor → Prop
  | none => r.headD 0 = 0
  | some X => r.headD 0 = 1 ∧ DecB (fun m => decCC m (r.tail.headD 0).toNat) m X

theorem fcgW_ok (n : Nat) : ∀ (m m' : Mem) (io il cn : Word) (r : List Word) (xs : List ClassCtor),
    fcgW n m io il cn = some (r, m') → DecB (fun m => decPL m (decCC m) io.toNat il.toNat) m xs → H cn →
    (m.arr64 IW).size < 2 ^ 64 →
    m' = m ∧ FcRes m r (xs.find? (fun x => x.cv.name == decI cn)) := by
  induction n with
  | zero => intro m m' io il cn r xs h; simp [fcgW] at h
  | succ n ih =>
  intro m m' io il cn r xs h hxs hcn hsz
  by_cases hl : il = 0
  · rw [fcgW.arm1 (hc1 := hl)] at h
    cases h
    have : xs = [] := by
      have := decPL_length _ (hxs.get (OMono.decPL (fun q => decCC_mono q) _ _))
      rw [hl] at this; exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst this
    exact ⟨rfl, rfl⟩
  have hl0 : il.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
  obtain ⟨k, hk⟩ : ∃ k, il.toNat = k + 1 := ⟨il.toNat - 1, by omega⟩
  have hxs' : decPL (truncM m) (decCC (truncM m)) io.toNat (k + 1) = some xs := by rw [← hk]; exact hxs
  obtain ⟨p, X0, rest, rfl, hp, hX0, hrest⟩ := decPL_cons hxs'
  obtain ⟨hpt, hpm⟩ := rec2IwN_trunc hp
  obtain ⟨ep, tp⟩ := rec2RdN (w := io) (k := 0) (by simpa using hpm) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at ep
  have hX0m : decCC m (UInt64.ofNat p : Word).toNat = some X0 := by
    rw [tp]; exact (show DecB (fun m => decCC m p) m X0 from hX0).get (decCC_mono _)
  obtain ⟨w, ew, hwH, hwd⟩ := rec2CCName hX0m hsz
  by_cases hhit : w = cn
  · subst hhit
    rw [fcgW.arm2 (hc1 := hl) (hc2 := by rw [ep, ew])] at h
    cases h
    refine ⟨rfl, ?_⟩
    have : (X0.cv.name == decI w) = true := by rw [← hwd]; simp
    simp only [List.find?_cons, this]
    exact ⟨rfl, by rw [ep]; simp only [List.headD_cons, List.tail_cons]; rw [tp]; exact hX0⟩
  · rw [fcgW.arm3 (hc1 := hl) (hc2 := by rw [ep, ew]; exact hhit)] at h
    obtain ⟨⟨r', m''⟩, hr, h⟩ := of_K h rfl
    rw [fcgW.k_class_gen_prefix_binders_find_ctor_go.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have := iwN_lt hpm
    have hio1 : (io + 1).toNat = io.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hil1 : (il - 1).toNat = k := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    obtain ⟨hm, hres⟩ := ih m m'' (io + 1) (il - 1) cn r' rest hr (by rw [hio1, hil1]; exact hrest) hcn hsz
    subst hm
    refine ⟨rfl, ?_⟩
    have : (X0.cv.name == decI cn) = false := by
      rw [← hwd]; simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun e => hhit (decI_inj hwH hcn e)
    simp only [List.find?_cons, this]
    exact hres

theorem fcW_ok (n : Nat) (m m' : Mem) (g c cn : Word) (r : List Word) (G : ClassGen)
    (h : fcW n m g c cn = some (r, m')) (hG : DecB (fun m => decCG m g.toNat) m G) (hcn : H cn)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    m' = m ∧ FcRes m r ((G.ctors.getD c.toNat []).find? (fun x => x.cv.name == decI cn)) := by
  rcases n with _ | n
  · simp [fcW] at h
  have hG' : decCG (truncM m) g.toNat = some G := hG
  simp only [decCG, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hG'
  obtain ⟨nP, hnP, ps, hps, cls, hcls, ft, hft, sl, hsl, cts, hcts, el, hel, pre, hpre, rfl⟩ := hG'
  obtain ⟨co, cl, hco, hcl, hctd⟩ := decAt_some hcts
  obtain ⟨hcot, hcom⟩ := rec2IwN_trunc hco
  obtain ⟨hclt, hclm⟩ := rec2IwN_trunc hcl
  obtain ⟨e9, t9⟩ := rec2RdN (w := g) (k := 9) hcom hsz
  obtain ⟨e10, t10⟩ := rec2RdN (w := g) (k := 10) (by simpa [Nat.add_assoc] using hclm) hsz
  simp only [show UInt64.ofNat 9 = (9 : Word) from rfl, show UInt64.ofNat 10 = (10 : Word) from rfl] at e9 e10
  have hlen := decPL_length _ hctd
  by_cases hc : rdW (m.arr64 IW) (g + 10) ≤ c
  · rw [fcW.arm1 (hc1 := hc)] at h
    cases h
    have : cts.length ≤ c.toNat := by rw [hlen, ← t10]; rw [e10] at hc; exact UInt64.le_iff_toNat_le.mp hc
    refine ⟨rfl, ?_⟩
    have hn : cts.getD c.toNat [] = [] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
    rw [hn]
    rfl
  rw [fcW.arm2 (hc1 := hc)] at h
  have hcl' : c.toNat < cl := by
    rw [e10] at hc; have := UInt64.lt_iff_toNat_lt.mp (by simpa using hc); rwa [t10] at this
  obtain ⟨lp, hlp, hlpd⟩ := decPL_getH (truncM m) hctd c.toNat hcl'
  obtain ⟨-, hlpm⟩ := rec2IwN_trunc hlp
  obtain ⟨xo, xl, hio, hil, hdx⟩ := decAt_some hlpd
  obtain ⟨-, hiom⟩ := rec2IwN_trunc hio
  obtain ⟨-, hilm⟩ := rec2IwN_trunc hil
  have elp : rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 9) + c) = UInt64.ofNat lp := by
    rw [e9]; simpa using (rec2RdN (w := UInt64.ofNat co) (k := c.toNat) (by rw [t9]; exact hlpm) hsz).1
  have lplt := (iwN_rdW hlpm (by have := iwN_lt hlpm; omega)).2
  obtain ⟨eio, -⟩ := rec2RdN (w := UInt64.ofNat lp) (k := 0) (by simpa [UInt64.toNat_ofNat_of_lt' lplt] using hiom) hsz
  obtain ⟨eil, -⟩ := rec2RdN (w := UInt64.ofNat lp) (k := 1)
    (by simpa [UInt64.toNat_ofNat_of_lt' lplt] using hilm) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero,
    show UInt64.ofNat 1 = (1 : Word) from rfl] at eio eil
  rw [elp, eio, eil] at h
  obtain ⟨⟨r', m''⟩, hr, h⟩ := of_K h rfl
  rw [fcW.k_class_gen_prefix_binders_find_ctor_go.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have iolt := (iwN_rdW hiom (by have := iwN_lt hiom; omega)).2
  have illt := (iwN_rdW hilm (by have := iwN_lt hilm; omega)).2
  obtain ⟨hm, hres⟩ := fcgW_ok n m m'' _ _ cn r' (cts[c.toNat]'(by omega)) hr
    (by rw [UInt64.toNat_ofNat_of_lt' iolt, UInt64.toNat_ofNat_of_lt' illt]; exact hdx) hcn hsz
  subst hm
  refine ⟨rfl, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show c.toNat < cts.length by omega), Option.getD_some]
  exact hres

theorem rec2DecCS_mot {m : Mem} {p : Nat} {key : ClassKey} (h : decCS m p = some (.motive key)) :
    iwN m p = some 0 := by
  rw [decCS] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, h⟩ := h
  match t, h with
  | 0, _ => exact ht
  | 1, h => simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h; obtain ⟨_, _, _, _, _, _, h⟩ := h; cases h
  | (_ + 2), h => simp at h

theorem rec2DecCS_min {m : Mem} {p c : Nat} {C : NIdx} {ihs : List (Nat × Nat)}
    (h : decCS m p = some (.minor c C ihs)) :
    iwN m p = some 1 ∧ iwN m (p + 1) = some c ∧ iwH m (p + 2) = some C := by
  rw [decCS] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, h⟩ := h
  match t, h with
  | 0, h => simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h; obtain ⟨_, _, _, _, h⟩ := h; cases h
  | 1, h =>
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨c', hc, C', hC, ihs', -, he⟩ := h
    cases he
    exact ⟨ht, hc, hC⟩
  | (_ + 2), h => simp at h

theorem rec2Count_succ (sl : List ClassSlot) (s : Nat) (hs : s < sl.length) :
    ((sl.take (s + 1)).filter rec2IsMot).length =
      ((sl.take s).filter rec2IsMot).length + (if rec2IsMot sl[s] then 1 else 0) := by
  rw [List.take_add_one, List.filter_append, List.length_append, List.getElem?_eq_getElem hs]
  simp only [Option.toList_some]
  cases h : rec2IsMot sl[s] <;> simp [List.filter, h]

/-- The common tail of a slot: the rest of the walk, then the cons. -/
theorem pfTail {vis : Word} {fe : IFEnv} {m m1 : Mem} {a1 : AState}
    (n : Nat) (ty : Word) (hty : H ty) (_hS1 : StageR vis fe m1 a1) (hg1 : IWGrow m m1)
    (rest : Option (List Word × Mem)) (opR : AM (Option (List EIdx)))
    (hrest : RSim rest opR a1
      (fun b a' o => StageR vis fe b.2 a' ∧ IWGrow m1 b.2 ∧ decIHO b.2 b.1 o ∧ AbsOK b.2)) :
    RSim (psW.k_class_gen_prefix_binders_slot_motive (smW.k_class_gen_prefix_binders_slots_go n ty rest)) (do
      let __do_lift ← opR
      match __do_lift with
      | none => pure none
      | some rest => pure (some (decI ty :: rest))) a1
      (fun b a' o => StageR vis fe b.2 a' ∧ IWGrow m b.2 ∧ decIHO b.2 b.1 o ∧ AbsOK b.2) := by
  refine RSim.bind (K := fun o => psW.k_class_gen_prefix_binders_slot_motive (smW.k_class_gen_prefix_binders_slots_go n ty o)) rfl hrest ?_
  rintro ⟨r2, m2⟩ o a2 - ⟨hS2, hg2, ho, hA2⟩
  dsimp only at hS2 hg2 ho
  rcases o with _ | rl
  · rw [smW.k_class_gen_prefix_binders_slots_go.arm1 (hc1 := ho)]; exact RSim.pure_some ⟨hS2, hg1.trans hg2, rfl, hA2⟩
  obtain ⟨h21, hd2, hb2⟩ := ho
  rw [smW.k_class_gen_prefix_binders_slots_go.arm2 (hc1 := by rw [h21]; decide)]
  refine RSim.lstep (K := fun o => psW.k_class_gen_prefix_binders_slot_motive (smW.k_sl_cons o)) rfl fun ⟨r3, m3⟩ h3 => ?_
  obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage h3 hS2 hb2 hty hd2
  simp only [smW.k_sl_cons.arm1, psW.k_class_gen_prefix_binders_slot_motive.arm1, List.headD_cons, List.tail_cons]
  exact RSim.pure_some ⟨hS3, hg1.trans (hg2.trans hg3), ⟨rfl, by simpa using hd3,
    by simp only [List.tail_cons, List.headD_cons]; exact Nat.le_of_eq ht3⟩, consW_afr h3 hA2⟩

theorem psW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (G : ClassGen) (g : Word)
    (hns : G.nP + G.slots.length < 2 ^ 64) (n : Nat) :
    ∀ (m : Mem) (a : AState) (s mc : Word), StageR vis fe m a → DecB (fun m => decCG m g.toNat) m G →
    s.toNat ≤ G.slots.length → mc.toNat = ((G.slots.take s.toNat).filter rec2IsMot).length → AbsOK m →
    RSim (psW n m g s mc) (ConRon.Arena.ClassGen.prefixBinders.slotsGo G s.toNat (G.slots.drop s.toNat)) a
      (fun b a' o => StageR vis fe b.2 a' ∧ IWGrow m b.2 ∧ decIHO b.2 b.1 o ∧ AbsOK b.2) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro m a s mc hS hG hsl hmc hA
  rcases n with _ | n
  · intro b hb; simp [psW] at hb
  have hsz := hS.iw.iwSize
  obtain ⟨hnP, hslots⟩ := rec2CG_get (hG.get (decCG_mono _))
  obtain ⟨so, sl, hso, hsl', hsls⟩ := decAt_some hslots
  have hlen := decPL_length m hsls
  obtain ⟨e8, t8⟩ := rec2RdN (w := g) (k := 8) (by simpa [Nat.add_assoc] using hsl') hsz
  obtain ⟨e7, t7⟩ := rec2RdN (w := g) (k := 7) hso hsz
  obtain ⟨e0, t0⟩ := rec2RdN (w := g) (k := 0) (by simpa using hnP) hsz
  simp only [show UInt64.ofNat 8 = (8 : Word) from rfl, show UInt64.ofNat 7 = (7 : Word) from rfl,
    show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at e8 e7 e0
  by_cases hend : rdW (m.arr64 IW) (g + 8) ≤ s
  · rw [psW.arm1 (hc1 := hend)]
    have : G.slots.length ≤ s.toNat := by
      rw [e8] at hend; have := UInt64.le_iff_toNat_le.mp hend; rw [t8] at this; omega
    rw [List.drop_eq_nil_of_le this, ConRon.Arena.ClassGen.prefixBinders.slotsGo.eq_1]
    exact RSim.pure_some ⟨hS, IWGrow.refl m, ⟨rfl, by simp [decHL, hslice?], by simp⟩, hA⟩
  have hlt : s.toNat < G.slots.length := by
    rw [e8] at hend
    have : ¬ (UInt64.ofNat sl : Word).toNat ≤ s.toNat := fun x => hend (UInt64.le_iff_toNat_le.mpr x)
    rw [t8] at this; omega
  obtain ⟨p, hp, hdp⟩ := decPL_getH m hsls s.toNat (by omega)
  have plt := (iwN_rdW hp (by have := iwN_lt hp; omega)).2
  have ep : rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s) = UInt64.ofNat p := by
    rw [e7]; simpa using (rec2RdN (w := UInt64.ofNat so) (k := s.toNat) (by rw [t7]; exact hp) hsz).1
  have hs1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hd : (rdW (m.arr64 IW) g + s).toNat = G.nP + s.toNat := by
    rw [e0, UInt64.toNat_add, t0]; omega
  rw [List.drop_eq_getElem_cons (by omega)]
  generalize hslot : G.slots[s.toNat]'(by omega) = slot at hdp
  have hcnt := rec2Count_succ G.slots s.toNat (by omega)
  rw [hslot] at hcnt
  cases slot with
  | motive key =>
    have h0 := rec2DecCS_mot hdp
    obtain ⟨e00, -⟩ := rec2RdN (w := UInt64.ofNat p) (k := 0) (by simpa [UInt64.toNat_ofNat_of_lt' plt] using h0) hsz
    simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at e00
    rw [psW.arm2 (hc1 := hend) (hc2 := by rw [ep, e00]), ConRon.Arena.ClassGen.prefixBinders.slotsGo.eq_2]
    rcases n with _ | n
    · intro b hb; simp [smW, psW.k_class_gen_prefix_binders_slot_motive] at hb
    rw [smW.arm1]
    have hm := motW_sim dn vis fe n m a g mc (rdW (m.arr64 IW) g + s) G hS hG hA
    rw [hmc, hd] at hm
    refine RSim.bind (K := fun o => psW.k_class_gen_prefix_binders_slot_motive (smW.k_class_gen_motive_ty n g s mc o))
      (by rw [smW.k_class_gen_motive_ty.none, psW.k_class_gen_prefix_binders_slot_motive.none]) hm ?_
    rintro ⟨r1, m1⟩ o a1 - ⟨⟨hS1, hg1, ho⟩, hA1⟩
    dsimp only at hS1 hg1 ho
    rcases o with _ | ty
    · rw [smW.k_class_gen_motive_ty.arm1 (hc1 := ho)]; exact RSim.pure_some ⟨hS1, hg1, rfl, hA1⟩
    obtain ⟨h11, htyH, htyd⟩ := ho
    rw [smW.k_class_gen_motive_ty.arm2 (hc1 := by rw [h11]; decide)]
    dsimp only
    rw [← htyd]
    have hmcs : mc.toNat ≤ s.toNat := by
      rw [hmc]; exact Nat.le_trans (List.length_filter_le _ _) (by simp; omega)
    have hmc1 : (mc + 1).toNat = mc.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hr := ih n (by omega) m1 a1 (s + 1) (mc + 1) hS1 (hG.grow (decCG_mono _) hg1) (by omega)
      (by rw [hmc1, hs1, hcnt, hmc]; simp [rec2IsMot]) hA1
    rw [hs1] at hr
    exact pfTail n _ htyH hS1 hg1 _ _ hr
  | minor c C ihs =>
    obtain ⟨h1, hc, hC⟩ := rec2DecCS_min hdp
    have hp' : (UInt64.ofNat p : Word).toNat = p := UInt64.toNat_ofNat_of_lt' plt
    obtain ⟨e01, -⟩ := rec2RdN (w := UInt64.ofNat p) (k := 0) (by simpa [hp'] using h1) hsz
    obtain ⟨ec, tc⟩ := rec2RdN (w := UInt64.ofNat p) (k := 1) (by rw [hp']; exact hc) hsz
    obtain ⟨cw, ecw, hcwH, hcwd⟩ := iwH_rdW_at (w := UInt64.ofNat p) (k := 2) (by rw [hp']; exact hC) hsz
    simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero, show UInt64.ofNat 1 = (1 : Word) from rfl,
      show UInt64.ofNat 2 = (2 : Word) from rfl] at e01 ec ecw
    rw [psW.arm3 (hc1 := hend) (hc2 := by rw [ep, e01]; decide), ConRon.Arena.ClassGen.prefixBinders.slotsGo.eq_3]
    rw [ep, ec, ecw]
    rcases n with _ | n
    · intro b hb; simp [snW, psW.k_class_gen_prefix_binders_slot_motive] at hb
    rw [snW.arm1]
    refine RSim.lstep (K := fun o => psW.k_class_gen_prefix_binders_slot_motive (snW.k_class_gen_prefix_binders_find_ctor n g s mc _ _ o))
      (by rw [snW.k_class_gen_prefix_binders_find_ctor.none, psW.k_class_gen_prefix_binders_slot_motive.none])
      fun ⟨r4, m4⟩ h4 => ?_
    obtain ⟨hm4, hres⟩ := fcW_ok n m m4 g _ cw r4 G h4 hG hcwH hsz
    subst m4
    rw [tc, hcwd] at hres
    cases hf : (G.ctors.getD c []).find? (fun x => x.cv.name == C) with
    | none =>
      rw [hf] at hres
      rw [snW.k_class_gen_prefix_binders_find_ctor.arm1 (hc1 := hres)]
      simp only [pure_bind]
      exact RSim.pure_some ⟨hS, IWGrow.refl m, rfl, hA⟩
    | some X =>
    rw [hf] at hres
    obtain ⟨h41, hX⟩ := hres
    rw [snW.k_class_gen_prefix_binders_find_ctor.arm2 (hc1 := by rw [h41]; decide)]
    simp only []
    have hm := mnW_sim dn vis fe n m a g (UInt64.ofNat c) (r4.tail.headD 0) (rdW (m.arr64 IW) g + s) G X hS hG hns hX hA
    rw [tc, hd] at hm
    refine RSim.bind (K := fun o => psW.k_class_gen_prefix_binders_slot_motive (snW.k_class_gen_minor_ty n g s mc o))
      (by rw [snW.k_class_gen_minor_ty.none, psW.k_class_gen_prefix_binders_slot_motive.none]) hm ?_
    rintro ⟨r1, m1⟩ o a1 - ⟨⟨hS1, hg1, ho⟩, hA1⟩
    dsimp only at hS1 hg1 ho
    rcases o with _ | ty
    · rw [snW.k_class_gen_minor_ty.arm1 (hc1 := ho)]; exact RSim.pure_some ⟨hS1, hg1, rfl, hA1⟩
    obtain ⟨h11, htyH, htyd⟩ := ho
    rw [snW.k_class_gen_minor_ty.arm2 (hc1 := by rw [h11]; decide)]
    dsimp only
    rw [← htyd]
    have hr := ih n (by omega) m1 a1 (s + 1) mc hS1 (hG.grow (decCG_mono _) hg1) (by omega)
      (by rw [hs1, hcnt, hmc]; simp [rec2IsMot]) hA1
    rw [hs1] at hr
    exact pfTail n _ htyH hS1 hg1 _ _ hr

theorem gpbW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem) (a : AState)
    (g : Word) (G : ClassGen) (hS : StageR vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hA : AbsOK m) :
    RSim (gpbW n m g) (ConRon.Arena.ClassGen.prefixBinders G) a
      (fun b a' x => KP vis fe m decIHO b a' x ∧ AbsOK b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [gpbW.arm1]
  unfold ConRon.Arena.ClassGen.prefixBinders
  rw [rec2MapM_genBinder]
  have hsz := hS.iw.iwSize
  have hG' : decCG (truncM m) g.toNat = some G := hG
  simp only [decCG, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hG'
  obtain ⟨nP, hnP, ps, hps, cls, hcls, ft, hft, sl, hsl, cts, hcts, el, hel, pre, hpre, hGe⟩ := hG'
  obtain ⟨o1, l1, h1, h2, hpd⟩ := decAt_some hps
  obtain ⟨-, h1m⟩ := rec2IwN_trunc h1
  obtain ⟨-, h2m⟩ := rec2IwN_trunc h2
  obtain ⟨e1, t1⟩ := rec2RdN (w := g) (k := 1) h1m hsz
  obtain ⟨e2, t2⟩ := rec2RdN (w := g) (k := 2) (by simpa [Nat.add_assoc] using h2m) hsz
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl] at e1 e2
  rw [e1, e2]
  have hpar : decHL m o1 l1 = some G.params := by
    rw [← hGe]; exact (show DecB (fun m => (decHL m o1 l1 : Option (List EIdx))) m ps from hpd).get (OMono.decHL _ _)
  have hpb : 0 < l1 → o1 + l1 ≤ iwTop m := by
    intro hl
    have hpd' : decHL (truncM m) o1 l1 = some ps := hpd
    have hs : (iwA (truncM m)).size ≤ iwTop m := by
      apply Nat.le_of_not_lt
      intro h
      have := truncM_iw_get? m (iwTop m)
      rw [ite_eq_right (Nat.lt_irrefl _), Array.getElem?_eq_getElem h] at this
      cases this
    rcases decHL_le hpd' with h0 | h0
    · omega
    · exact Nat.le_trans h0 hs
  refine RSim.bind (K := gpbW.k_fvar_type_ds n g) rfl (RSim.withF ((ftdsF_ok dn vis fe _ _ G.params).sim
      ⟨hS, by rw [t1, t2]; exact hpar, by rw [t1, t2]; exact hpb⟩) (fun _ hb => ftdsF_afr hb)) ?_
  rintro ⟨r1, m1⟩ pbs a1 - ⟨⟨hS1, hg1, hpbs, hpbb⟩, hf1⟩
  dsimp only at hS1 hg1 hpbs hpbb
  simp only [getD_zero, Nat.zero_add, getD_one] at hpbs hpbb
  rw [gpbW.k_fvar_type_ds.arm1]
  have hps := psW_sim dn vis fe G g hns n m1 a1 0 0 hS1 (hG.grow (decCG_mono _) hg1) (by simp) (by simp)
    (hf1 hA)
  simp only [UInt64.toNat_zero, List.drop_zero] at hps
  refine RSim.bind (K := gpbW.k_class_gen_prefix_binders_slots_go n (r1.headD 0) (r1.tail.headD 0)) rfl hps ?_
  rintro ⟨r2, m2⟩ o a2 - ⟨hS2, hg2, ho, hA2⟩
  dsimp only at hS2 hg2 ho
  rcases o with _ | sbs
  · rw [gpbW.k_class_gen_prefix_binders_slots_go.arm1 (hc1 := ho)]; exact RSim.pure_some ⟨⟨hS2, hg1.trans hg2, rfl⟩, hA2⟩
  obtain ⟨h21, hsb, hsbb⟩ := ho
  rw [gpbW.k_class_gen_prefix_binders_slots_go.arm2 (hc1 := by rw [h21]; decide)]
  refine RSim.lstep (K := gpbW.k_sl_append) rfl fun ⟨r3, m3⟩ h3 => ?_
  obtain ⟨hS3, hg3, hd3, hb3⟩ := rec2AppendW_dec h3 hS2 ((decHL_decB hpbs hpbb).grow (OMono.decHL _ _) hg2) hsb hsbb
  rw [gpbW.k_sl_append.arm1]
  exact RSim.pure_some ⟨⟨hS3, hg1.trans (hg2.trans hg3), rfl, by simpa using hd3, by simpa using hb3⟩,
    appendW_afr h3 hA2⟩

/-- **`class_gen_prefix_binders` refines `ClassGen.prefixBinders`** (through the stubs of
`class_gen_motive_ty`, `class_gen_minor_ty` and `fvar_type_ds`): the parameters' binders, then
every slot's, a slice below the top. -/
@[refines ConRon.Arena.ClassGen.prefixBinders]
theorem classGenPrefixBinders_refines (p : Prog) (hp : PbProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g : Word) (G : ClassGen)
    (hS : StageR vis fe s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_prefix_binders" [g]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.prefixBinders G) a₀ ∧
      KP vis fe s₀.mem decIHO (r, s'.mem) (AM.st (ConRon.Arena.ClassGen.prefixBinders G) a₀)
        (AM.res (ConRon.Arena.ClassGen.prefixBinders G) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (prefixBinders_spec p hp n s₀ g) fun _ _ ⟨hl, hw⟩ =>
    let h := (gpbW_sim dn vis fe n _ a₀ g G hS hG hns hA).am hw
    ⟨hl, h.1, h.2.1, h.2.2⟩

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem loc_init13 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: r) 13 =
      x13 := rfl
theorem loc_init14 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: r)
      14 = x14 := rfl
theorem loc_init15 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) (r : List Word) :
    Locals.init
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: r)
      15 = x15 := rfl

l_model findSlotGo_spec (p : Prog) (h : RuProg p)
  fns [h.fsg ↦ fsgW list]
  grind [arena_grind]

l_model pvarsGo_spec (p : Prog) (h : RuProg p)
  fns [h.pv ↦ pvW list]
  specs [rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n,
    slotVar_spec p h.pw h.sf h.sp h.isort h.fvf h.fvp h.ifv h.sv n, slCons_specW p h.alloc h.copy h.cons n]
  grind [arena_grind] finish [rdW_eq] gen 20

/-! ## One call -/

l_model call1Close_spec (p : Prog) (h : RuProg p)
  fns [h.c1c ↦ c1cW list]
  specs [ftdsF_spec p h.ad n, closeLams_spec p h.db h.lf h.lp h.il h.mkl h.cl h.ab n]
  grind [arena_grind]

l_model call1Tail_spec (p : Prog) (h : RuProg p)
  fns [h.c1t ↦ c1tW list]
  specs [rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, mknF_spec p h.ad n,
    internConst_spec p h.cf h.cp h.ic n, slAppend_specW p h.alloc h.copy h.app n,
    slSnoc_specW p h.alloc h.copy h.snoc n, call1Close_spec p h n]
  grind [arena_grind]

/-- **`class_gen_rule_call1` is its model `c1W`** (generated). -/
l_model call1_spec (p : Prog) (h : RuProg p)
  fns [h.c1 ↦ c1W list]
  specs [rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, rec2IhParts_specF p h.ihp h.ad h.opf n,
    classRecOf_spec p h.cro n, call1Tail_spec p h n]
  grind [arena_grind] finish [] gen 20 trace

theorem c1W_tail_eq : c1W.k_class_gen_rule_call1_tail = fcK := by
  funext o; cases o <;> rfl

/-! ## The calls -/

/-- **`class_gen_rule_calls_go` is its model `cgW`** (generated). -/
l_model callsGo_spec (p : Prog) (h : RuProg p)
  fns [h.cg ↦ cgW list]
  specs [call1_spec p h n, slCons_specW p h.alloc h.copy h.cons n]
  grind [arena_grind] extra [ld64_rd_spec]

section cgArms
variable (n : Nat) (m : Mem) (g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i : Word)

/-- A field that is not a recursive call: the walk goes on. -/
theorem cgW_ord (h : ¬ nn = 0) (ht : ¬ isTag m x i = 1) :
    cgW (n + 1) m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i =
      cgW.k_class_gen_rule_calls_go_2
        (cgW n m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e (nn - 1) (i + 1)) := by
  by_cases hi : i < rdW (m.arr64 IW) (x + 3)
  · rw [cgW.arm2 (hc1 := h) (hc2 := hi), cgW.j1.arm2 (hc1 := by simpa [isTag, hi] using ht)]
  · rw [cgW.arm3 (hc1 := h) (hc2 := hi), cgW.j1.arm2 (hc1 := by simp)]

/-- A recursive field: its call, then the walk. -/
theorem cgW_rec (h : ¬ nn = 0) (ht : isTag m x i = 1) :
    cgW (n + 1) m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i =
      cgW.k_class_gen_rule_call1 n g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i
        (c1W n m g (rdW (m.arr64 IW) (isKp m x i + 1)) (rdW (m.arr64 IW) (isKp m x i + 2)) wso wsl fvso fvsl
          pvo pvl rlvls rco rcl cgo cgl i e) := by
  have hi : i < rdW (m.arr64 IW) (x + 3) := by
    by_cases hi : i < rdW (m.arr64 IW) (x + 3)
    · exact hi
    · simp [isTag, hi] at ht
  rw [cgW.arm2 (hc1 := h) (hc2 := hi), cgW.j1.arm1 (hc1 := by simpa [isTag, hi] using ht)]
  rfl
end cgArms

/-! ## The closing, the body, the rule -/

l_model ruleClose_spec (p : Prog) (h : RuProg p)
  fns [h.rc ↦ grcW list]
  specs [slotVar_spec p h.pw h.sf h.sp h.isort h.fvf h.fvp h.ifv h.sv n,
    slAppend_specW p h.alloc h.copy h.app n, mknF_spec p h.ad n, ftdsF_spec p h.ad n,
    closeLams_spec p h.db h.lf h.lp h.il h.mkl h.cl h.ab n]
  grind [arena_grind]

l_model ruleBody_spec (p : Prog) (h : RuProg p)
  fns [h.rb ↦ rbW list]
  specs [targetPiDomsWith_spec p h.ev h.copy h.alloc h.cons h.tpd h.hi1 n, pvarsGo_spec p h n,
    callsGo_spec p h n, ruleClose_spec p h n]
  grind [arena_grind]

def ruK2 (n : Nat) (g rco rcl cgo cgl rlvls x rP s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0], m2)
    else fcK (rbW n m2 g rco rcl cgo cgl rlvls x rP s (r2.tail.headD 0) (r2.tail.tail.headD 0))

def ruK1 (n : Nat) (g rco rcl cgo cgl rlvls x rP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0], m1)
    else ruK2 n g rco rcl cgo cgl rlvls x rP (r1.tail.headD 0)
      (opfF m1 [rdW (m1.arr64 IW) (x + 1), rdW (m1.arr64 IW) (x + 4), rP])

section arms2
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (next : Mem → Option (List Word × Mem))
  (g x so sl j c cn rP i v e app fvso fvsl pvo pvl rlvls xso xsl idxo idxl r t tele wso wsl rco rcl cgo cgl
    nn s fo fl ihso ihsl body sv rc fx : Word) (r1 r2 r3 r4 r5 r6 : List Word)
theorem ruK1_fail (h : r1.headD 0 = 0) : ruK1 n g rco rcl cgo cgl rlvls x rP (some (r1, m1)) = some ([0, 0], m1) := by
  rw [ruK1, ite_eq_left h]
theorem ruK1_ok (h : r1.headD 0 ≠ 0) : ruK1 n g rco rcl cgo cgl rlvls x rP (some (r1, m1)) =
    ruK2 n g rco rcl cgo cgl rlvls x rP (r1.tail.headD 0)
      (opfF m1 [rdW (m1.arr64 IW) (x + 1), rdW (m1.arr64 IW) (x + 4), rP]) := by
  rw [ruK1, ite_eq_right h]
theorem ruK2_fail (h : r2.headD 0 = 0) : ruK2 n g rco rcl cgo cgl rlvls x rP s (some (r2, m2)) = some ([0, 0], m2) := by
  rw [ruK2, ite_eq_left h]
theorem ruK2_ok (h : r2.headD 0 ≠ 0) : ruK2 n g rco rcl cgo cgl rlvls x rP s (some (r2, m2)) =
    fcK (rbW n m2 g rco rcl cgo cgl rlvls x rP s (r2.tail.headD 0) (r2.tail.tail.headD 0)) := by
  rw [ruK2, ite_eq_right h]
end arms2

attribute [ind_grind] ruK1_fail ruK1_ok ruK2_fail ruK2_ok

end L.Ind

end

end
