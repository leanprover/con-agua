import ConAgua.Arena.IndSumSpec.DecHLTake
import ConAgua.Arena.IndSumSpec.Row

/-!
# StructCtorResidOk: `ConRon.Arena.structCtorResidOk`

The refinement theorems `structCtorResidOk_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The model -/

/-- The three tests, as the L code combines them. -/
def srRes (fn hd al nP nIdx e3 : Word) : Word :=
  (if fn = hd then 1 else 0) &&& (if al = nP + nIdx then 1 else 0) &&& e3

/-- After `struct_ps_at`: the prefix comparison. -/
def srK5 (k : Nat) (nP nIdx hd fn ao al : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rp, m5) =>
    if rp.tail.headD 0 ≤ al then
      match eqW k m5 ao (rp.tail.headD 0) (rp.headD 0) (rp.tail.headD 0) with
      | none => none
      | some e => some ([srRes fn hd al nP nIdx e], m5)
    else some ([srRes fn hd al nP nIdx 0], m5)
/-- After `get_app_args`. -/
def srK4 (k : Nat) (nP o nIdx hd fn : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m4) => srK5 k nP nIdx hd fn (ra.headD 0) (ra.tail.headD 0) (psAtW k m4 o nP)
/-- After `get_app_fn`. -/
def srK3 (k : Nat) (nP o nIdx cbody hd : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, m3) => srK4 k nP o nIdx hd (rf.headD 0) (gaaF m3 [CWF, cbody])
/-- After `intern_const`. -/
def srK2 (k : Nat) (nP o nIdx cbody : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hd, m2) =>
    if 4294967296 ≤ hd then none else srK3 k nP o nIdx cbody hd (gafF m2 [CWF, cbody])
/-- After `param_levels`. -/
def srK1 (k : Nat) (T nP o nIdx cbody : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => srK2 k nP o nIdx cbody (ceinternW m1 T (r1.headD 0))
/-- **The model of `struct_ctor_resid_ok`.** -/
def srW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | k + 1, m, T, lo, ll, nP, o, nIdx, cbody => srK1 k T nP o nIdx cbody (plW k m lo ll)

section arms
variable (k : Nat) (m m1 m2 m3 m4 m5 : Mem) (T lo ll nP o nIdx cbody hd fn ao al : Word)
  (r1 rf ra rp : List Word)
theorem srW_succ : srW (k + 1) m T lo ll nP o nIdx cbody = srK1 k T nP o nIdx cbody (plW k m lo ll) := rfl
theorem srK1_some : srK1 k T nP o nIdx cbody (some (r1, m1)) =
    srK2 k nP o nIdx cbody (ceinternW m1 T (r1.headD 0)) := rfl
theorem srK2_big (h : 4294967296 ≤ hd) : srK2 k nP o nIdx cbody (some (hd, m2)) = none := by
  simp [srK2, h]
theorem srK2_ok (h : ¬ 4294967296 ≤ hd) : srK2 k nP o nIdx cbody (some (hd, m2)) =
    srK3 k nP o nIdx cbody hd (gafF m2 [CWF, cbody]) := by simp only [srK2, ite_eq_right h]
theorem srK3_some : srK3 k nP o nIdx cbody hd (some (rf, m3)) =
    srK4 k nP o nIdx hd (rf.headD 0) (gaaF m3 [CWF, cbody]) := rfl
theorem srK4_some : srK4 k nP o nIdx hd fn (some (ra, m4)) =
    srK5 k nP nIdx hd fn (ra.headD 0) (ra.tail.headD 0) (psAtW k m4 o nP) := rfl
theorem srK5_le (h : rp.tail.headD 0 ≤ al) : srK5 k nP nIdx hd fn ao al (some (rp, m5)) =
    (match eqW k m5 ao (rp.tail.headD 0) (rp.headD 0) (rp.tail.headD 0) with
      | none => none
      | some e => some ([srRes fn hd al nP nIdx e], m5)) := by simp only [srK5, ite_eq_left h]
theorem srK5_gt (h : ¬ rp.tail.headD 0 ≤ al) : srK5 k nP nIdx hd fn ao al (some (rp, m5)) =
    some ([srRes fn hd al nP nIdx 0], m5) := by simp only [srK5, ite_eq_right h]
end arms

grind_pattern [ind_grind] srW_succ => srW (k + 1) m T lo ll nP o nIdx cbody
grind_pattern [ind_grind] srK1_some => srK1 k T nP o nIdx cbody (some (r1, m1))
grind_pattern [ind_grind] srK2_big => srK2 k nP o nIdx cbody (some (hd, m2))
grind_pattern [ind_grind] srK2_ok => srK2 k nP o nIdx cbody (some (hd, m2))
grind_pattern [ind_grind] srK3_some => srK3 k nP o nIdx cbody hd (some (rf, m3))
grind_pattern [ind_grind] srK4_some => srK4 k nP o nIdx hd fn (some (ra, m4))
grind_pattern [ind_grind] srK5_le => srK5 k nP nIdx hd fn ao al (some (rp, m5))
grind_pattern [ind_grind] srK5_gt => srK5 k nP nIdx hd fn ao al (some (rp, m5))

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hg : p.lookup "sl_get" = some slGet)
  (hpf : p.lookup "param_find" = some paramFind) (hpp : p.lookup "param_push" = some paramPush)
  (hip : p.lookup "intern_param" = some internParam)
  (hplg : p.lookup "param_levels_go" = some paramLevelsGoL)
  (hpl : p.lookup "param_levels" = some paramLevelsL) (hil : IlF p)
  (hcf : p.lookup "const_find" = some constFind) (hcp : p.lookup "const_push" = some constPush)
  (hic : p.lookup "intern_const" = some internConst)
  (hbf : p.lookup "bvar_find" = some bvarFind) (hbp : p.lookup "bvar_push" = some bvarPush)
  (hib : p.lookup "intern_bvar" = some internBVar)
  (hpg : p.lookup "struct_ps_at_go" = some structPsAtGoL)
  (hps : p.lookup "struct_ps_at" = some structPsAtL)
  (heq : p.lookup "sl_eq" = some slEq)
  (hp : p.lookup "struct_ctor_resid_ok" = some structCtorResidOkL) (had : AdF p)
include ha hc hsc hg hpf hpp hip hplg hpl hil hcf hcp hic hbf hbp hib hpg hps heq hp had

theorem srW_spec (k : Nat) (s₀ : St) (T lo ll nP o nIdx cbody : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "struct_ctor_resid_ok" [T, lo, ll, nP, o, nIdx, cbody]
    ⦃fun r s' => LocEq s' s₀ ∧ srW k s₀.mem T lo ll nP o nIdx cbody = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structCtorResidOkL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        plW_spec p ha hc hsc hg hpf hpp hip hplg hpl hil k, internConst_spec p hcf hcp hic k,
        gafF_spec p had k, gaaF_spec p had k,
        psAtW_spec p ha hc hsc hbf hbp hib hpg hps k, slEq_spec p heq k] <;>
      finish (gen := 20) [srRes]

end spec

/-! ## The relational lemma -/

theorem plW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k : Nat)
    (m m' : Mem) (a : AState) (o l : Word) (lps : List NIdx) (r : List Word)
    (h : plW k m o l = some (r, m')) (hS : StageR dn vis fe m a)
    (hd : decHL m o.toNat l.toNat = some lps) (hb : o.toNat + l.toNat < 2 ^ 64)
    (ht : o.toNat + l.toNat ≤ iwTop m) :
    ∃ x a', (paramLevels lps).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      H (r.headD 0) ∧ decI (r.headD 0) = x := by
  cases k with
  | zero => cases h
  | succ k =>
  rw [plW_succ] at h
  obtain ⟨r1, m1, h1, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  rw [plK4_some] at h
  obtain ⟨r2, m2, h2, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  rw [plK5_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨us, a1, hrun1, hS1, hg1, hd1, -⟩ := plgW_ok dn vis fe k _ _ _ _ _ _ _ h1 hS hd hb ht
  obtain ⟨x, a2, hrun2, hS2, hg2, hH, hx⟩ :=
    ilF_ok dn vis fe (r1.headD 0) (r1.tail.headD 0) us m1 _ a1 r2 h2 ⟨hS1, hd1⟩
  refine ⟨x, a2, ?_, hS2, hg1.trans hg2, by simpa using hH, by simpa using hx⟩
  simp only [paramLevels, StateT.run_bind, hrun1]
  exact hrun2

theorem srRes_ok (fn hd al nP nIdx e : Word) (b1 b2 b3 : Bool)
    (h1 : (fn = hd) ↔ b1 = true) (h2 : (al = nP + nIdx) ↔ b2 = true) (h3 : e = if b3 then 1 else 0) :
    (srRes fn hd al nP nIdx e != 0) = (b1 && b2 && b3) ∧ (srRes fn hd al nP nIdx e).toNat ≤ 1 := by
  unfold srRes
  cases b1 <;> cases b2 <;> cases b3 <;> simp_all <;> decide

theorem srW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k : Nat)
    (m m' : Mem) (a : AState) (T lo ll nP o nIdx cbody : Word) (r : List Word) (lps : List NIdx)
    (h : srW k m T lo ll nP o nIdx cbody = some (r, m')) (hS : StageR dn vis fe m a)
    (hT : H T) (hcb : H cbody) (hd : decHL m lo.toNat ll.toNat = some lps)
    (hb : lo.toNat + ll.toNat < 2 ^ 64) (ht : lo.toNat + ll.toNat ≤ iwTop m)
    (hon : o.toNat + nP.toNat < 2 ^ 64) (hni : nP.toNat + nIdx.toNat < 2 ^ 64) :
    ∃ x a', (structCtorResidOk (decI T) lps nP.toNat o.toNat nIdx.toNat (decI cbody)).run a =
      .ok (x, a') ∧ KeepPost dn vis fe decW0B m m' a' r x := by
  cases k with
  | zero => cases h
  | succ k =>
  rw [srW_succ] at h
  obtain ⟨r1, m1, h1, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  rw [srK1_some] at h
  obtain ⟨us, a1, hrun1, hS1, hg1, hus, husd⟩ := plW_ok dn vis fe k m m1 a lo ll lps r1 h1 hS hd hb ht
  obtain ⟨hd', m2, h2, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  by_cases hbig : 4294967296 ≤ hd'
  · rw [srK2_big k m2 nP o nIdx cbody hd' hbig] at h; cases h
  rw [srK2_ok k m2 nP o nIdx cbody hd' hbig] at h
  have hd32 : hd'.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ hd'.toNat := hbig; omega
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internConst_stage hS1 T (r1.headD 0) hT hus h2
  obtain ⟨rf, m3, h3, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  rw [srK3_some] at h
  obtain ⟨fnv, a3, hrun3, hS3, hg3, hf32, hfd⟩ := gafF_ok dn vis fe CWF cbody hcb m2 m3 a2 rf h3 hS2
  obtain ⟨ra, m4, h4, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  rw [srK4_some] at h
  obtain ⟨args, a4, hrun4, hS4, hg4, hargs, hat⟩ :=
    gaaF_ok dn vis fe CWF cbody hcb m3 m4 a3 ra h4 hS3
  obtain ⟨rp, m5, h5, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  obtain ⟨ps, a5, hrun5, hS5, hg5, hps, hpt⟩ := psAtW_stage dn vis fe k m4 m5 a4 o nP rp h5 hS4 hon
  have eA0 : ra.getD 0 0 = ra.headD 0 := by cases ra <;> rfl
  have eA1 : ra.getD 1 0 = ra.tail.headD 0 := by
    cases ra with | nil => rfl | cons _ t => cases t <;> rfl
  simp only [eA0, eA1] at hargs hat
  have hargs5 := decHL_grow hg5 hat ▸ hargs
  have hal := decHL_length m5 (by simpa using hargs5)
  have hpl := decHL_length m5 hps
  have eP1 : rp[1]?.getD 0 = rp.tail.headD 0 := by
    cases rp with | nil => rfl | cons _ t => cases t <;> rfl
  have eR1 : ra[1]?.getD 0 = ra.tail.headD 0 := by
    cases ra with | nil => rfl | cons _ t => cases t <;> rfl
  try simp only [eP1] at hpl
  try simp only [eR1] at hal
  have hsz5 := hS5.2.2.2.1
  have hit5 := hS5.2.1
  -- the twin's run up to the final `pure`
  have hrun : ∀ v, (structCtorResidOk (decI T) lps nP.toNat o.toNat nIdx.toNat (decI cbody)).run a =
      .ok (v, a5) ↔ v = (fnv == decI hd' && args.length == nP.toNat + nIdx.toNat &&
        args.take ps.length == ps) := by
    intro v
    rw [husd] at hrun2
    rw [CWF_eq] at hrun3 hrun4
    rw [decE_eq] at hrun2
    simp only [StateT.run] at hrun1 hrun2 hrun3 hrun4 hrun5
    simp only [structCtorResidOk, StateT.run, bind, StateT.bind, hrun1, hrun2, hrun3, hrun4, hrun5,
      pure, StateT.pure, Except.pure, Except.bind, Except.ok.injEq, Prod.mk.injEq, and_true]
    exact eq_comm
  have hfn : (rf.headD 0 = hd') ↔ (fnv == decI hd') = true := by
    rw [beq_iff_eq, ← hfd]
    exact ⟨fun e => by rw [e], fun e => decI_inj hf32 hd32 e⟩
  have hln : (ra.tail.headD 0 = nP + nIdx) ↔ (args.length == nP.toNat + nIdx.toNat) = true := by
    have e1' : ra[1]?.getD 0 = ra.tail.headD 0 := by
      cases ra with | nil => rfl | cons _ t => cases t <;> rfl
    rw [beq_iff_eq, hal]
    try rw [e1']
    constructor
    · intro e; rw [e, UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa using hni)]
    · intro e; apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa using hni)]
      exact e
  have hat5 : (ra.headD 0).toNat + (ra.tail.headD 0).toNat ≤ iwTop m5 := by
    have := hg5.1; omega
  have hgall := (((hg1.trans hg2).trans hg3).trans hg4).trans hg5
  by_cases hle : rp.tail.headD 0 ≤ ra.tail.headD 0
  · rw [srK5_le k m5 nP nIdx hd' (rf.headD 0) (ra.headD 0) (ra.tail.headD 0) rp hle] at h
    have hle' : (rp.tail.headD 0).toNat ≤ (ra.tail.headD 0).toNat := UInt64.le_iff_toNat_le.mp hle
    cases he : eqW k m5 (ra.headD 0) (rp.tail.headD 0) (rp.headD 0) (rp.tail.headD 0) with
    | none => rw [he] at h; cases h
    | some e =>
    rw [he] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have htk := decHL_take hargs5 _ hle'
    obtain ⟨ws1, hs1, hm1, hb1⟩ := slR_of_decHL m5 _ _ _ htk (by omega)
    obtain ⟨ws2, hs2, hm2, hb2⟩ := slR_of_decHL m5 _ _ _ hps (by omega)
    simp only [UInt64.ofNat_toNat] at hs1 hs2
    have heq := eqW_ok k m5 _ _ _ _ e ws1 ws2 hs1 hs2 he
    have hb3 : e = if (args.take ps.length == ps) then 1 else 0 := by
      rw [heq, hpl]
      have := map_decI_inj (k := .expr) ws1 ws2 hb1 hb2
      by_cases hw : ws1 = ws2
      · rw [ite_eq_left hw]
        have ht : args.take (rp.tail.headD 0).toNat = ps := by rw [hm1, hm2, hw]
        rw [ht]; simp
      · rw [ite_eq_right hw]
        have hne : args.take (rp.tail.headD 0).toNat ≠ ps := by
          rw [hm1, hm2]; exact fun h' => hw (this.mp h')
        rw [show (args.take (rp.tail.headD 0).toNat == ps) = false from by simpa using hne]
        rfl
    refine ⟨_, a5, (hrun _).mpr rfl, hS5, hgall, ?_⟩
    exact srRes_ok _ _ _ _ _ _ _ _ _ hfn hln hb3
  · rw [srK5_gt k m5 nP nIdx hd' (rf.headD 0) (ra.headD 0) (ra.tail.headD 0) rp hle] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hgt : (ra.tail.headD 0).toNat < (rp.tail.headD 0).toNat := by
      have : ¬ (rp.tail.headD 0).toNat ≤ (ra.tail.headD 0).toNat :=
        fun h' => hle (UInt64.le_iff_toNat_le.mpr h')
      omega
    have hb3 : (0 : Word) = if (args.take ps.length == ps) then 1 else 0 := by
      have hne : args.take ps.length ≠ ps := by
        intro h'
        have := congrArg List.length h'
        rw [List.length_take] at this
        omega
      simp [hne]
    refine ⟨_, a5, (hrun _).mpr rfl, hS5, hgall, ?_⟩
    exact srRes_ok _ _ _ _ _ _ _ _ _ hfn hln hb3

section census
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hg : p.lookup "sl_get" = some slGet)
  (hpf : p.lookup "param_find" = some paramFind) (hpp : p.lookup "param_push" = some paramPush)
  (hip : p.lookup "intern_param" = some internParam)
  (hplg : p.lookup "param_levels_go" = some paramLevelsGoL)
  (hpl : p.lookup "param_levels" = some paramLevelsL) (hil : IlF p)
  (hcf : p.lookup "const_find" = some constFind) (hcp : p.lookup "const_push" = some constPush)
  (hic : p.lookup "intern_const" = some internConst)
  (hbf : p.lookup "bvar_find" = some bvarFind) (hbp : p.lookup "bvar_push" = some bvarPush)
  (hib : p.lookup "intern_bvar" = some internBVar)
  (hpg : p.lookup "struct_ps_at_go" = some structPsAtGoL)
  (hps : p.lookup "struct_ps_at" = some structPsAtL)
  (heq : p.lookup "sl_eq" = some slEq)
  (hp : p.lookup "struct_ctor_resid_ok" = some structCtorResidOkL) (had : AdF p)
include ha hc hsc hg hpf hpp hip hplg hpl hil hcf hcp hic hbf hbp hib hpg hps heq hp had

/-- **`struct_ctor_resid_ok` refines `structCtorResidOk`** (through the stubs `get_app_fn`,
`get_app_args`, `intern_ls_iw`). -/
@[refines ConRon.Arena.structCtorResidOk]
theorem structCtorResidOk_refines (k : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (T lo ll nP o nIdx cbody : Word)
    (lps : List NIdx) (hS : StageR dn vis fe s₀.mem a₀) (hT : H T) (hcb : H cbody)
    (hd : decHL s₀.mem lo.toNat ll.toNat = some lps) (hb : lo.toNat + ll.toNat < 2 ^ 64)
    (ht : lo.toNat + ll.toNat ≤ iwTop s₀.mem) (hon : o.toNat + nP.toNat < 2 ^ 64)
    (hni : nP.toNat + nIdx.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "struct_ctor_resid_ok" [T, lo, ll, nP, o, nIdx, cbody]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (structCtorResidOk (decI T) lps nP.toNat o.toNat nIdx.toNat (decI cbody)) a₀ ∧
      KeepPost dn vis fe decW0B s₀.mem s'.mem
        (AM.st (structCtorResidOk (decI T) lps nP.toNat o.toNat nIdx.toNat (decI cbody)) a₀) r
        (AM.res (structCtorResidOk (decI T) lps nP.toNat o.toNat nIdx.toNat (decI cbody)) a₀); ⊤⦄ := by
  refine triple_post (srW_spec p ha hc hsc hg hpf hpp hip hplg hpl hil hcf hcp hic hbf hbp hib hpg hps
    heq hp had k s₀ T lo ll nP o nIdx cbody) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hpost⟩ := srW_ok dn vis fe k _ _ _ _ _ _ _ _ _ _ _ _ hm hS hT hcb hd hb ht hon hni
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hpost⟩

end census

/-! ## The walk memos across the sum-check pieces (lane `indproofs4`, helper `memo`) -/

theorem pinternW_afr {m m' : Mem} {u r : Word} (h : pinternW m u = some (r, m')) : AFr m m' := by
  exact AFr.of_frame (consInternM_frame paramCS_wf h) (by simp [ConsSch.wset, paramCS, PREC, PSLOT, PINS, memoFreeA])
    (by simp [paramCS, memoFreeC])

theorem plgW_afr : ∀ (k : Nat) (m m' : Mem) (o l : Word) (r : List Word), plgW k m o l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, h => by simp [plgW] at h
  | k + 1, m, m', o, l, r, h => by
    simp only [plgW, plK0.eq_def, plK1.eq_def, plK2.eq_def, plK3.eq_def] at h
    afr_auto h [allocW_afr, pinternW_afr, plgW_afr k _ _ _ _ _, consW_afr]

theorem ilF_afr {m m' : Mem} {args r : List Word} (h : ilF m args = some (r, m')) : AFr m m' :=
  AFr.of_frame (ilF_frame h)

theorem plW_afr {k : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : plW k m o l = some (r, m')) :
    AFr m m' := by
  cases k with
  | zero => simp [plW] at h
  | succ k =>
  simp only [plW, plW.plK4.eq_def, plW.plK5.eq_def] at h
  afr_auto h [plgW_afr _ _ _ _ _ _, ilF_afr]

theorem psGoW_afr : ∀ (n : Nat) (m m' : Mem) (o nP N k : Word) (r : List Word),
    psGoW n m o nP N k = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, h => by simp [psGoW] at h
  | n + 1, m, m', o, nP, N, k, r, h => by
    simp only [psGoW, psK0.eq_def, psK1.eq_def, psK2.eq_def, psK3.eq_def] at h
    afr_auto h [psGoW_afr n _ _ _ _ _ _ _, binternW_afr, allocW_afr, consW_afr]

theorem psAtW_afr {n : Nat} {m m' : Mem} {o nP : Word} {r : List Word} (h : psAtW n m o nP = some (r, m')) :
    AFr m m' := by
  cases n with
  | zero => simp [psAtW] at h
  | succ n =>
    simp only [psAtW, psK3.eq_def] at h
    afr_auto h [psGoW_afr _ _ _ _ _ _ _ _]

theorem srW_afr : ∀ (k : Nat) (m m' : Mem) (T lo ll nP o nIdx cbody : Word) (r : List Word),
    srW k m T lo ll nP o nIdx cbody = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [srW] at h
  | k + 1, m, m', T, lo, ll, nP, o, nIdx, cbody, r, h => by
    simp only [srW, srK1.eq_def, srK2.eq_def, srK3.eq_def, srK4.eq_def, srK5.eq_def] at h
    afr_auto h [plW_afr, ceinternW_afr, (fun h => AFr.of_frame (gafF_frame h)), gaaF_afr, psAtW_afr]

end L.Ind

end
