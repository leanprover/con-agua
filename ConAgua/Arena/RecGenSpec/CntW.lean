module

public import ConAgua.Verdict.IndBRec1
public import ConAgua.Arena.RecGenSpec.KeysProg
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndSumSpec.StructProjArgP
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.RecGen
import ConAgua.L.WordOff

@[expose] public section

/-!
# CntW

`clsCons`, `check_block_classes_keys`' unified model `ckkE` and its refinement `ckk_ref`, and the lemmas
only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`sl_cons` of a decoded record onto a decoded slice** (its model's run), with its frame. -/
theorem clsConsW {α : Type} {f : Mem → Nat → Option α}
    (hf : ∀ q, OMono (fun m => f m q)) {vis : Word} {fe : IFEnv}
    {a : AState} {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List α} {y : α}
    (h : consW n m x o l = some (r, m')) (hS : StageR vis fe m a)
    (hxs : PSlR f xs o l m) (hy : DecB (fun m => f m x.toNat) m y) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ PSlR f (y :: xs) (r.headD 0) (r.tail.headD 0) m' ∧
      MFr [] [] m m' := by
  obtain ⟨hS', hg, hd, htop⟩ := partsConsPL hf h hS hxs.bound hxs.dec hy
  exact ⟨hS', hg, ⟨hd, Nat.le_of_eq htop⟩, consW_mfr h⟩

/-- **`sl_cons` of a decoded record onto a decoded slice**, with its frame. -/
theorem clsCons {p : Prog} (hP : KeysProg p) {n : Nat} {α : Type} {f : Mem → Nat → Option α}
    (hf : ∀ q, OMono (fun m => f m q)) {vis : Word} {fe : IFEnv}
    {a : AState} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List α} {y : α}
    (h : callW p n "sl_cons" [x, o, l] m = some (r, m')) (hS : StageR vis fe m a)
    (hxs : PSlR f xs o l m) (hy : DecB (fun m => f m x.toNat) m y) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ PSlR f (y :: xs) (r.headD 0) (r.tail.headD 0) m' ∧
      MFr [] [] m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slCons_specW p hP.rx.ha hP.copy hP.cons n _ x o l) h
  exact clsConsW hf hW hS hxs hy

/-! ## `check_block_classes_keys`: one model and one refinement for both outcomes -/

/-- **`check_block_classes_keys`' unified model**: `class_key_of` through its unified model,
`sl_cons` (outside the verdict closure) lifted. -/
l_model ckkE_spec (p : Prog) (hP : KeysProg p)
  fns [hP.keys ↦ ckkE]
  specs [classKeyOfE_spec p hP.toKofProg n, slCons_specW p hP.rx.ha hP.copy hP.cons n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `check_block_classes_keys` gives besides the twin's keys `ks` (from `m`): the keys'
slice `[r₀, r₁]`, the stage invariant, the growth, the frame. -/
structure CkkPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (r : List Word)
    (m' : Mem) (ks : List ClassKey) (a' : AState) : Prop where
  stage : StageR vis fe m' a'
  grow : IWGrow m m'
  keys : PSlR decCK ks (r.headD 0) (r.tail.headD 0) m'
  pos : PosMR m'

/-- **`check_block_classes_keys` refines `ks.mapM (classKeyOf nP params)`, both outcomes**:
`class_key_of` by `kof_ref`, `sl_cons` outside the verdict closure. -/
theorem ckk_ref {p : Prog} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (nP po pl : Word) (pfvs : List EIdx) (n : Nat) :
    ∀ (m : Mem) (a : AState) (ko kl : Word) (ks : List ClassKey),
    StageR vis fe m a → DecB (fun m => decHL m po.toNat pl.toNat) m pfvs →
    po.toNat + pl.toNat ≤ iwTop m → PSlR decCK ks ko kl m → PosMR m →
    RefE (closedNV p _root_.L.Checker.nvFns = true) (ckkE p n m nP po pl ko kl)
      (ks.mapM (ConRon.Arena.classKeyOf nP.toNat pfvs)) a
      (fun v x a' => CkkPost dn vis fe m v.1 v.2 x a') := by
  induction n with
  | zero => intro m a ko kl ks _ _ _ _ _; rw [ckkE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n ih =>
  intro m a ko kl ks hS hpf hpb hks hPm
  by_cases hkl : kl = 0
  · rw [ckkE.arm1 p n m nP po pl ko kl hkl]
    have : ks = [] := by
      have h := hks.1; simp only [DecB, hkl] at h
      simpa [decPL] using h.symm
    subst this
    exact RefE.ret rfl ⟨hS, IWGrow.refl m, PSlR.nil decCK m, hPm⟩
  obtain ⟨q, k0, ks', rfl, hw, hqb, hdk, hks'⟩ := partsPSl_cons hks hkl
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  rw [ckkE.arm2 p n m nP po pl ko kl hkl, hw]
  simp only [List.mapM_cons]
  -- `class_key_of`
  have h1 := kof_ref (p := p) (nP := nP) dn fe vis n hS (hpf.get (OMono.decHL _ _)) hpb (by rw [hq']; exact hdk) hPm
  rcases h1' : classKeyOfE p n m nP po pl (UInt64.ofNat q) with e1 | ⟨r1, m1⟩
  · rw [h1'] at h1
    rw [ckkE.k_class_key_of.none]; exact RefE.bind_left h1
  rw [h1'] at h1
  obtain ⟨x1, a1, hrun1, hR1⟩ := h1
  dsimp only at hR1
  rw [ckkE.k_class_key_of.arm1]
  refine RefE.bind_right hrun1 ?_
  have hg1 := hR1.grow
  -- the rest
  have h2 := ih m1 a1 (ko + 1) (kl - 1) ks' hR1.stage (hpf.grow (OMono.decHL _ _) hg1)
    (Nat.le_trans hpb hg1.iw) (hks'.grow decCK_mono hg1) hR1.pos
  rcases h2' : ckkE p n m1 nP po pl (ko + 1) (kl - 1) with e2 | ⟨r2, m2⟩
  · rw [h2'] at h2
    rw [ckkE.k_check_block_classes_keys.none]; exact RefE.bind_left h2
  rw [h2'] at h2
  obtain ⟨xs, a2, hrun2, hR2⟩ := h2
  dsimp only at hR2
  rw [ckkE.k_check_block_classes_keys.arm1]
  refine RefE.bind_right hrun2 ?_
  -- `sl_cons`
  refine RefE.onlySim (fun _ => ckkE.k_sl_cons.none ..) (fun _ _ h => h) fun r3 m3 h3 => ?_
  rw [ckkE.k_sl_cons.arm1]
  obtain ⟨hS3, hg3, hd3, hf3⟩ := clsConsW decCK_mono h3 hR2.stage hR2.keys
    (hR1.key.grow (decCK_mono _) hR2.grow)
  exact RefE.ret rfl ⟨hS3, (hg1.trans hR2.grow).trans hg3, by simpa using hd3, hR2.pos.fr hf3⟩

/-! ## One class per member: `check_block_classes_count`, `check_block_classes_one_per_member` -/

/-- After the rest's count. -/
def cntK (m : Mem) (o w : Word) : Option Word → Option Word
  | none => none
  | some r => some (if rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 8) = w then r + 1 else r)

/-- **The model of `check_block_classes_count(o, l, w)`.** -/
def cntW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, o, l, w => if l = 0 then some 0 else cntK m o w (cntW n m (o + 1) (l - 1) w)

section arms
variable (n : Nat) (m : Mem) (o l w r : Word)
theorem cntW_nil (h : l = 0) : cntW (n + 1) m o l w = some 0 := by simp [cntW, h]
theorem cntW_cons (h : l ≠ 0) : cntW (n + 1) m o l w = cntK m o w (cntW n m (o + 1) (l - 1) w) := by
  simp [cntW, h]
theorem cntK_hit (h : rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 8) = w) : cntK m o w (some r) = some (r + 1) := by
  simp [cntK, h]
theorem cntK_miss (h : rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 8) ≠ w) : cntK m o w (some r) = some r := by
  simp [cntK, h]
end arms
attribute [ind_grind] cntW_nil cntW_cons cntK_hit cntK_miss

theorem cnt_spec (p : Prog) (hp : p.lookup "check_block_classes_count" = some checkBlockClassesCount)
    (n : Nat) : ∀ (s₀ : St) (o l w : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_classes_count" [o, l, w]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ cntW n s₀.mem o l w = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o l w; rw [invoke_eq _ hp]; simp only [callFn, checkBlockClassesCount]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l w
    rw [invoke_eq _ hp]
    simp only [callFn, checkBlockClassesCount]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)

/-- The twin's per-member count. -/
def memCount (ms : List TargetMajor) (t : Nat) : Nat := (ms.filter (·.member == some t)).length

theorem cntW_ok (n : Nat) : ∀ (m : Mem) (o l w r : Word) (ms : List TargetMajor),
    cntW n m o l w = some r → decPL m (decTM m) o.toNat l.toNat = some ms →
    o.toNat + l.toNat < 2 ^ 64 → (m.arr64 IW).size < 2 ^ 64 → w ≠ 0 →
    r.toNat = memCount ms (w.toNat - 1) ∧ r.toNat ≤ l.toNat := by
  induction n with
  | zero => intro m o l w r ms h; simp [cntW] at h
  | succ n ih =>
    intro m o l w r ms h hd hb hsz hw
    by_cases hl : l = 0
    · rw [cntW_nil n m o l w hl] at h
      simp only [Option.some.injEq] at h
      subst h
      have hz : l.toNat = 0 := by rw [hl]; rfl
      rw [hz] at hd
      simp [decPL] at hd
      subst hd
      simp [memCount]
    · obtain ⟨hsum, hco1⟩ := toNat_succ_of_lt hb hl
      obtain ⟨l1, hl1⟩ : ∃ l1, l.toNat = l1 + 1 := ⟨l.toNat - 1, by
        have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
        omega⟩
      rw [hl1] at hd
      obtain ⟨pp, t, ys, rfl, hp, hx, hys⟩ := decPL_cons hd
      have hrd := iwN_rdW hp (by omega)
      rw [UInt64.ofNat_toNat] at hrd
      obtain ⟨k, hk, hmem⟩ := decTM_member hx
      have hk8 := iwN_lt hk
      have hk' := iwN_rdW hk (by omega)
      have e8 : UInt64.ofNat pp + 8 = UInt64.ofNat (pp + 8) := by rw [UInt64.ofNat_add]; rfl
      have hrd8 : rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 8) = UInt64.ofNat k := by
        rw [hrd.1, e8]; exact hk'.1
      have hys' : decPL m (decTM m) (o + 1).toNat (l - 1).toNat = some ys := by
        have hl1' : (l - 1).toNat = l1 := by omega
        rw [hco1, hl1']; exact hys
      rcases hc : cntW n m (o + 1) (l - 1) w with _ | r1
      · rw [cntW_cons n m o l w hl, hc] at h; simp [cntK] at h
      rw [cntW_cons n m o l w hl, hc] at h
      obtain ⟨h1, h1l⟩ := ih m (o + 1) (l - 1) w r1 ys hc hys' (by omega) hsz hw
      have hl1' : (l - 1).toNat = l1 := by omega
      have hw0 : w.toNat ≠ 0 := fun e => hw (UInt64.toNat_inj.mp (by simpa using e))
      have hiff : (UInt64.ofNat k = w) ↔ (t.member == some (w.toNat - 1)) = true := by
        rw [hmem]
        constructor
        · intro e
          have : k = w.toNat := by rw [← e, UInt64.toNat_ofNat_of_lt' hk'.2]
          subst this
          simp [decON, hw0]
        · intro e
          have : k ≠ 0 ∧ k - 1 = w.toNat - 1 := by
            simp only [decON] at e
            split at e
            · simp at e
            · simp at e; omega
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_ofNat_of_lt' hk'.2]; omega
      by_cases he : UInt64.ofNat k = w
      · rw [cntK_hit (h := by rw [hrd8]; exact he)] at h
        simp only [Option.some.injEq] at h
        subst h
        have hr1 : (r1 + 1).toNat = r1.toNat + 1 :=
          L.toNat_add_of_lt _ _ (by rw [show (1 : Word).toNat = 1 from rfl]; have := l.toNat_lt; omega)
        refine ⟨?_, by omega⟩
        rw [hr1, h1]
        simp [memCount, hiff.mp he]
      · rw [cntK_miss (h := by rw [hrd8]; exact he)] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨?_, by omega⟩
        rw [h1]
        have : ¬ (t.member == some (w.toNat - 1)) = true := fun e => he (hiff.mpr e)
        simp [memCount, this]

mutual
/-- **The model of `check_block_classes_one_per_member(j, k, o, l)`.** -/
def opmW : Nat → Mem → Word → Word → Word → Word → Option Word
  | 0, _, _, _, _, _ => none
  | n + 1, m, j, k, o, l => if k ≤ j then some 1 else opmK n m j k o l (cntW n m o l (j + 1))
/-- After the count. -/
def opmK (n : Nat) (m : Mem) (j k o l : Word) : Option Word → Option Word
  | none => none
  | some c => if c ≠ 1 then some 0 else opmW n m (j + 1) k o l
end

section arms
variable (n : Nat) (m : Mem) (j k o l c : Word)
theorem opmW_done (h : k ≤ j) : opmW (n + 1) m j k o l = some 1 := by simp [opmW, h]
theorem opmW_step (h : ¬ k ≤ j) : opmW (n + 1) m j k o l = opmK n m j k o l (cntW n m o l (j + 1)) := by
  simp [opmW, h]
theorem opmK_bad (h : c ≠ 1) : opmK n m j k o l (some c) = some 0 := by simp [opmK, h]
theorem opmK_good (h : ¬ c ≠ 1) : opmK n m j k o l (some c) = opmW n m (j + 1) k o l := by
  simp only [opmK]; rw [ite_eq_right h]
end arms
attribute [ind_grind] opmW_done opmW_step opmK_bad opmK_good

theorem opm_spec (p : Prog) (hc : p.lookup "check_block_classes_count" = some checkBlockClassesCount)
    (hp : p.lookup "check_block_classes_one_per_member" = some checkBlockClassesOnePerMember)
    (n : Nat) : ∀ (s₀ : St) (j k o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_classes_one_per_member" [j, k, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ opmW n s₀.mem j k o l = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ j k o l; rw [invoke_eq _ hp]; simp only [callFn, checkBlockClassesOnePerMember]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ j k o l
    rw [invoke_eq _ hp]
    simp only [callFn, checkBlockClassesOnePerMember]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, cnt_spec p hc n, ih] <;>
      finish (gen := 20)

theorem opmW_ok (n : Nat) : ∀ (m : Mem) (j k o l r : Word) (ms : List TargetMajor),
    opmW n m j k o l = some r → decPL m (decTM m) o.toNat l.toNat = some ms →
    o.toNat + l.toNat < 2 ^ 64 → (m.arr64 IW).size < 2 ^ 64 →
    (r != 0) = (List.range' j.toNat (k.toNat - j.toNat)).all (fun t => memCount ms t == 1) := by
  induction n with
  | zero => intro m j k o l r ms h; simp [opmW] at h
  | succ n ih =>
    intro m j k o l r ms h hd hb hsz
    by_cases hkj : k ≤ j
    · rw [opmW_done n m j k o l hkj] at h
      simp only [Option.some.injEq] at h
      subst h
      have : k.toNat - j.toNat = 0 := by have := UInt64.le_iff_toNat_le.mp hkj; omega
      rw [this]; rfl
    rw [opmW_step n m j k o l hkj] at h
    have hjk : j.toNat < k.toNat := by
      have : ¬ k.toNat ≤ j.toNat := fun e => hkj (UInt64.le_iff_toNat_le.mpr e)
      omega
    have hj1 : (j + 1).toNat = j.toNat + 1 :=
      L.toNat_add_of_lt _ _ (by rw [show (1 : Word).toNat = 1 from rfl]; have := k.toNat_lt; omega)
    obtain ⟨c, hc, h⟩ := of_K h (by simp only [opmK])
    obtain ⟨hc1, -⟩ := cntW_ok n m o l (j + 1) c ms hc hd hb hsz
      (fun e => by have := congrArg UInt64.toNat e; rw [hj1] at this; simp at this)
    rw [hj1, Nat.add_sub_cancel] at hc1
    have hsplit : List.range' j.toNat (k.toNat - j.toNat) =
        j.toNat :: List.range' (j.toNat + 1) (k.toNat - (j.toNat + 1)) := by
      rw [show k.toNat - j.toNat = (k.toNat - (j.toNat + 1)) + 1 by omega, List.range'_succ]
    rw [hsplit, List.all_cons]
    by_cases h1 : c ≠ 1
    · rw [opmK_bad (h := h1)] at h
      simp only [Option.some.injEq] at h
      subst h
      have : (memCount ms j.toNat == 1) = false := by
        rw [← hc1]; simp only [beq_eq_false_iff_ne, ne_eq]
        intro e; exact h1 (UInt64.toNat_inj.mp (by rw [e]; rfl))
      simp [this]
    · rw [opmK_good (h := h1)] at h
      have hc1' : c = 1 := by simpa using h1
      have : (memCount ms j.toNat == 1) = true := by rw [← hc1, hc1']; rfl
      rw [this, Bool.true_and, ← hj1]
      exact ih m (j + 1) k o l r ms h hd hb hsz

end L.Ind

end
