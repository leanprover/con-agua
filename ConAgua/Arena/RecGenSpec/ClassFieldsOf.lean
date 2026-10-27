import ConAgua.Arena.RecClassSpec.ClassNPcOf
import ConAgua.Arena.RecClassSpec.PiBWRoom
import ConAgua.Arena.RecGenSpec.CfhW
import ConAgua.Arena.RecGenSpec.CfoProg
import ConAgua.Arena.IndPartsSpec.BlockCounts

/-!
# ClassFieldsOf: `ConRon.Arena.classFieldsOf`

The refinement theorems `classFieldsOf_refines` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- After the rest: the cons. -/
def cfgK7 (n : Nat) (cf : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) => cfgK6 (consW n m6 cf (r6.headD 0) (r6.tail.headD 0))

/-- After the record: the rest (`rest`, the recursive call), then the cons. -/
def cfgK5 (n : Nat) (rest : Mem → Option (List Word × Mem)) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => cfgK7 n (r5.headD 0) (rest m5)

/-- After `pi_binders`: the recursive field's record. -/
def cfgK4 (n : Nat) (rest : Mem → Option (List Word × Mem)) (cls : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => cfgK5 n rest (recW m4 3 [1, cls, r4.tail.headD 0])

/-- After the hits: the field's kind. -/
def cfgK3 (n : Nat) (rest : Mem → Option (List Word × Mem)) (w occ : Word) (m2 : Mem) :
    Option (Word × Word) → Option (List Word × Mem)
  | none => none
  | some (hc, cls) =>
    if occ = 0 ∧ hc = 0 then cfgK5 n rest (recW m2 1 [0])
    else if occ ≠ 0 ∧ hc = 1 then cfgK4 n rest cls (piBW n m2 CWF w)
    else none

/-- After `nest_occ`. -/
def cfgK2 (n : Nat) (rest : Mem → Option (List Word × Mem)) (io il i w : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (occ, m2) => cfgK3 n rest w occ m2 (cfhW n m2 io il i)

/-- After `fvar_type_d`. -/
def cfgK1 (n : Nat) (rest : Mem → Option (List Word × Mem)) (mo ml io il i : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => cfgK2 n rest io il i (r1.headD 0) (noConstWf n m1 mo ml 0 0 (r1.headD 0))

/-- **The model of `class_fields_of_go`.** -/
def cfgW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, mo, ml, io, il, i, fo, fl =>
    if fl = 0 then some ([0, 0], m)
    else cfgK1 n (fun m5 => cfgW n m5 mo ml io il (i + 1) (fo + 1) (fl - 1)) mo ml io il i
      (ftdF m [rdW (m.arr64 IW) fo])

section arms
variable (n : Nat) (m m1 m2 m4 m5 : Mem) (rest : Mem → Option (List Word × Mem))
  (mo ml io il i fo fl w occ hc cls : Word) (r1 r4 r5 : List Word)
theorem cfgW_nil (h : fl = 0) : cfgW (n + 1) m mo ml io il i fo fl = some ([0, 0], m) := by
  simp [cfgW, h]
theorem cfgW_cons (h : ¬ fl = 0) : cfgW (n + 1) m mo ml io il i fo fl =
    cfgK1 n (fun m5 => cfgW n m5 mo ml io il (i + 1) (fo + 1) (fl - 1)) mo ml io il i
      (ftdF m [rdW (m.arr64 IW) fo]) := by
  simp [cfgW, h]
theorem cfgK1_some : cfgK1 n rest mo ml io il i (some (r1, m1)) =
    cfgK2 n rest io il i (r1.headD 0) (noConstWf n m1 mo ml 0 0 (r1.headD 0)) := rfl
theorem cfgK2_some : cfgK2 n rest io il i w (some (occ, m2)) = cfgK3 n rest w occ m2 (cfhW n m2 io il i) := rfl
theorem cfgK3_ord (h : occ = 0 ∧ hc = 0) :
    cfgK3 n rest w occ m2 (some (hc, cls)) = cfgK5 n rest (recW m2 1 [0]) := by
  rw [cfgK3, ite_eq_left h]
theorem cfgK3_rec (h0 : ¬ (occ = 0 ∧ hc = 0)) (h : occ ≠ 0 ∧ hc = 1) :
    cfgK3 n rest w occ m2 (some (hc, cls)) = cfgK4 n rest cls (piBW n m2 CWF w) := by
  rw [cfgK3, ite_eq_right h0, ite_eq_left h]
theorem cfgK3_bad (h0 : ¬ (occ = 0 ∧ hc = 0)) (h : ¬ (occ ≠ 0 ∧ hc = 1)) :
    cfgK3 n rest w occ m2 (some (hc, cls)) = none := by
  rw [cfgK3, ite_eq_right h0, ite_eq_right h]
theorem cfgK4_some : cfgK4 n rest cls (some (r4, m4)) = cfgK5 n rest (recW m4 3 [1, cls, r4.tail.headD 0]) := rfl
theorem cfgK5_some : cfgK5 n rest (some (r5, m5)) = cfgK7 n (r5.headD 0) (rest m5) := rfl
theorem cfgK7_some (cf : Word) (r6 : List Word) (m6 : Mem) :
    cfgK7 n cf (some (r6, m6)) = cfgK6 (consW n m6 cf (r6.headD 0) (r6.tail.headD 0)) := rfl
theorem cfgK6_some (r7 : List Word) (m7 : Mem) :
    cfgK6 (some (r7, m7)) = some ([r7.headD 0, r7.tail.headD 0], m7) := rfl
end arms

grind_pattern [ind_grind] cfgW_nil => cfgW (n + 1) m mo ml io il i fo fl
grind_pattern [ind_grind] cfgW_cons => cfgW (n + 1) m mo ml io il i fo fl
grind_pattern [ind_grind] cfgK1_some => cfgK1 n rest mo ml io il i (some (r1, m1))
grind_pattern [ind_grind] cfgK2_some => cfgK2 n rest io il i w (some (occ, m2))
grind_pattern [ind_grind] cfgK3_ord => cfgK3 n rest w occ m2 (some (hc, cls))
grind_pattern [ind_grind] cfgK3_rec => cfgK3 n rest w occ m2 (some (hc, cls))
grind_pattern [ind_grind] cfgK3_bad => cfgK3 n rest w occ m2 (some (hc, cls))
grind_pattern [ind_grind] cfgK4_some => cfgK4 n rest cls (some (r4, m4))
grind_pattern [ind_grind] cfgK5_some => cfgK5 n rest (some (r5, m5))
grind_pattern [ind_grind] cfgK7_some => cfgK7 n cf (some (r6, m6))
grind_pattern [ind_grind] cfgK6_some => cfgK6 (some (r7, m7))

theorem classFieldsOfGo_spec (p : Prog) (h : CfoProg p) (n : Nat) :
    ∀ (s₀ : St) (mo ml io il i fo fl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fields_of_go" [mo, ml, io, il, i, fo, fl]
    ⦃fun r s' => LocEq s' s₀ ∧ cfgW n s₀.mem mo ml io il i fo fl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ mo ml io il i fo fl; rw [invoke_eq _ h.go]; simp only [callFn, classFieldsOfGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ mo ml io il i fo fl
    rw [invoke_eq _ h.go]
    simp only [callFn, classFieldsOfGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        ftdF_spec0 p h.ftd n, nestOcc_spec' p h.no n, classFieldsOfHits_spec p h.hits n,
        iwAlloc_specW p h.alloc n, piBinders_spec' p h.alloc h.copy h.no.hv h.cons h.pb n,
        rec3_specW p h.alloc n h.r3, slCons_specW p h.alloc h.copy h.cons n, ih] <;>
      finish (gen := 20) [recW, wrIW]

/-! ## `class_fields_of_go` refines `classFieldsOf` -/

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}

/-- `pi_binders` as a simulation, with its write set. -/
theorem rec2SimPiBinders (n : Nat) (hS : StageR dn vis fe m a) {h : Word} (hh : H h) :
    RSim (piBW n m CWF h) (ConRon.Arena.piBinders coreWalkFuel (decI h)) a
      (fun b a' x => a' = a ∧ StageR dn vis fe b.2 a ∧ IWGrow m b.2 ∧ MemFrame [IW] [200] m b.2 ∧
        decHL b.2 (b.1.headD 0).toNat (b.1.tail.headD 0).toNat = some x.1) := by
  intro b hb
  obtain ⟨x, a', hrun, hS', hg, hd, -⟩ := simPiBinders n hS hh b hb
  obtain ⟨rs, m'⟩ := b
  obtain ⟨bs, e, hrun2, -, -, -, -, -, hf, -⟩ :=
    piBW_ok n m m' a CWF h rs hS.1.arena.1 hb hh hS.2.2.2.1 hS.2.2.2.2.2
  rw [CWF_eq, decE_eq] at hrun2
  have : (x, a') = ((bs, e), a) := by rw [hrun] at hrun2; injection hrun2
  cases this
  exact ⟨(bs, e), a, hrun, rfl, hS', hg, hf, hd⟩

end sims

theorem AgreeA.refl (b : Nat) (m : Mem) : AgreeA b m m :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem AgreeA.mono {b b' : Nat} {m m' : Mem} (hb : b ≤ b') (h : AgreeA b m m') : AgreeA b' m m' :=
  ⟨h.1, h.2.1, fun i hb' hi => h.2.2.1 i (Nat.le_trans hb hb') hi, h.2.2.2⟩

theorem AgreeA.iwH {k : IdxKind} {b : Nat} {m m' : Mem} (h : AgreeA b m m') {i : Nat} (hb : b ≤ i)
    (hi : i < iwTop m) : (iwH m' i : Option (Idx k)) = iwH m i := by
  simp only [L.Ind.iwH, hd?, iwA]; rw [h.2.2.1 i hb hi]

namespace StabA
variable {α : Type} {b : Nat} {f : Mem → Option α} {m m' : Mem} {x : α}
theorem get (h : StabA b f m x) : f m = some x := h m (AgreeA.refl b m)
theorem grow (h : StabA b f m x) (hg : AgreeA b m m') : StabA b f m' x := fun m'' h' => h m'' (hg.trans h')
theorem mono {b' : Nat} (hb : b ≤ b') (h : StabA b' f m x) : StabA b f m x := fun m' h' => h m' (h'.mono hb)
theorem stabD (h : StabA b f m x) : StabD f m x := fun m' hg => h m' (AgreeA.of_grow hg)
end StabA

/-- A constant decoded below the tops is stable above any bound (it lives in `EREC`). -/
theorem stabA_decCVp {m : Mem} {q : Nat} {x : IConstantVal} (h : DecB (fun m => decCVp m q) m x) (b : Nat) :
    StabA b (fun m => decCVp m q) m x := by
  intro m' hA
  have h' : decCV (erA (truncM m)) q = some x := h
  show decCV (erA m') q = some x
  refine ArrExt.decCV (fun i v hv => ?_) h'
  obtain ⟨hi, hv'⟩ := truncM_er_get hv
  simp only [erA] at hv' ⊢; rw [hA.2.2.2 i hi]; exact hv'

namespace SPLA
variable {α : Type} {b : Nat} {dec : Mem → Nat → Option α} {m m' : Mem} {o l : Nat} {xs : List α}

theorem nil (o : Nat) (ho : o ≤ iwTop m) : SPLA b dec m o 0 [] :=
  ⟨.inl rfl, by omega, [], by simp [decNL], FA2.nil⟩

theorem grow (h : SPLA b dec m o l xs) (hA : AgreeA b m m') : SPLA b dec m' o l xs := by
  obtain ⟨h1, h2, ps, hps, hf⟩ := h
  exact ⟨h1, Nat.le_trans h2 hA.1, ps, by rw [decNL_agree ⟨h1, h2, ps, hps, hf⟩ hA]; exact hps,
    FA2.imp (fun _ _ hq => hq.grow hA) hf⟩

theorem mono {b' : Nat} (hb : b ≤ b') (h : SPLA b' dec m o l xs) : SPLA b dec m o l xs := by
  obtain ⟨h1, h2, ps, hps, hf⟩ := h
  exact ⟨h1.imp id (Nat.le_trans hb), h2, ps, hps, FA2.imp (fun _ _ hq => hq.mono hb) hf⟩

theorem toSPL (h : SPLA b dec m o l xs) : SPL dec m o l xs := by
  obtain ⟨-, h2, ps, hps, hf⟩ := h
  exact ⟨h2, ps, hps, FA2.imp (fun _ _ hq => hq.stabD) hf⟩

/-- `sl_cons` of a pointer decoding stably above `b` onto a slice stable above `b`, at a top from
`b` on. -/
theorem cons {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {x ow lw : Word} {r : List Word} {y : α} (h : consW n m x ow lw = some (r, m'))
    (hS : StageR dn vis fe m a) (hl : SPLA b dec m ow.toNat lw.toNat xs) (hbt : b ≤ iwTop m)
    (hy : StabA b (fun m => dec m x.toNat) m y) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      SPLA b dec m' (r.headD 0).toNat (r.tail.headD 0).toNat (y :: xs) := by
  obtain ⟨h1, h2, ps, hps, hf⟩ := hl
  obtain ⟨hr, -, -, -, -, -⟩ := consW_decN h hS.2.2.2.1 hS.2.2.2.2.2 h2 hps
  obtain ⟨hS', hg, hdn, htop⟩ := consW_stageN h hS h2 hps
  refine ⟨hS', hg, .inr ?_, by omega, x.toNat :: ps, hdn,
    FA2.cons (hy.grow (AgreeA.of_grow hg)) (FA2.imp (fun _ _ hq => hq.grow (AgreeA.of_grow hg)) hf)⟩
  rw [hr]; exact hbt

end SPLA

/-- A one- or three-word record at the top decodes stably above any bound up to that top. -/
theorem rec2RecW_decCF_A {m m' : Mem} {k : Word} {ws r : List Word} {y : ClassField} {b : Nat}
    (h : recW m k ws = some (r, m')) (hc : 200 < (m.arr64 CTL).size) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hk : k.toNat = ws.length) (hb : b ≤ iwTop m)
    (hy : ∀ m'', (∀ j (hj : j < ws.length), iwN m'' ((r.headD 0).toNat + j) = some (ws[j]'hj).toNat) →
      decCF m'' (r.headD 0).toNat = some y) :
    StabA b (fun m => decCF m (r.headD 0).toNat) m' y := by
  obtain ⟨hr, hget, -, -, htop, -⟩ := recW_post h hc hsz hk
  subst hr
  intro m'' hA
  refine hy m'' fun j hj => ?_
  have hlt : (rdW (m.arr64 CTL) 200).toNat + j < iwTop m' := by rw [htop]; simp [iwTop]; omega
  simp only [List.headD_cons]
  rw [hA.iwN (by simp only [iwTop] at hb; omega) hlt]
  simp only [L.Ind.iwN, nat?, iwA, hget j hj, List.getElem?_eq_getElem hj, Option.map_some]

/-- The post of `class_fields_of(_go)`: the stage relation, growth, the fields' kinds a stable slice,
`nest_occ`'s memo relation at some map, and the write set outside the other walk memos (lane
`indproofs4`, helper `cls`: `class_ctor_of` carries `RcMR` across the call); the kinds' slice and
records lie above the entry's top (`SPLA`, for `class_ctors_of`'s writes into its result slots). -/
def CfoQ (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (b : List Word × Mem)
    (a' : AState) (ks : List ClassField) : Prop :=
  StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧
    SPLA (iwTop m) decCF b.2 (b.1.headD 0).toNat (b.1.tail.headD 0).toNat ks ∧
    (∃ mp, noMR b.2 mp) ∧ MFr [NOM] [204, 205] m b.2

/-- The common tail of both arms: the record, the rest, the cons. -/
theorem cfgTail {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {n : Nat} {m m2 : Mem}
    {a2 : AState} {k : Word} {ws : List Word} {y : ClassField} {mp : Std.HashMap EIdx Bool}
    {rest : Mem → Option (List Word × Mem)} {opR : AM (List ClassField)}
    (hS2 : StageR dn vis fe m2 a2) (hg2 : IWGrow m m2) (hM2 : noMR m2 mp) (hf2 : MFr [NOM] [204, 205] m m2)
    (hk : k.toNat = ws.length)
    (hy : ∀ m'', (∀ j (hj : j < ws.length), iwN m'' ((rdW (m2.arr64 CTL) 200).toNat + j) = some (ws[j]'hj).toNat) →
      decCF m'' (rdW (m2.arr64 CTL) 200).toNat = some y)
    (hrest : ∀ m5, StageR dn vis fe m5 a2 → IWGrow m2 m5 → noMR m5 mp → RSim (rest m5) opR a2 (CfoQ dn vis fe m5)) :
    RSim (cfgK5 n rest (recW m2 k ws)) (do let r ← opR; pure (y :: r)) a2 (CfoQ dn vis fe m) := by
  refine RSim.lstep (K := cfgK5 n rest) rfl fun ⟨r5, m5⟩ h5 => ?_
  have hc := hS2.2.2.2.2.2
  have hsz := hS2.2.2.2.1
  obtain ⟨hr5, -, hg5, hf5, htop5, hroom5⟩ := recW_post h5 hc hsz hk
  have hS5 := stage_frame_iw hS2 hf5 (by omega)
  have hy5 := rec2RecW_decCF_A (b := iwTop m) h5 hc hsz hk hg2.1 (by rw [hr5]; exact hy)
  rw [cfgK5_some]
  refine RSim.bind (K := cfgK7 n (r5.headD 0)) rfl (hrest m5 hS5 hg5 (rec2NoMR_iw hf5 hM2)) ?_
  rintro ⟨r6, m6⟩ ks a6 - ⟨hS6, hg6, hsp6, ⟨mp6, hM6⟩, hf6⟩
  dsimp only at hS6 hg6 hsp6 hM6 hf6
  rw [cfgK7_some]
  refine RSim.lstep (K := cfgK6) rfl fun ⟨r7, m7⟩ h7 => ?_
  obtain ⟨hS7, hg7, hsp7⟩ := SPLA.cons h7 hS6 (hsp6.mono (Nat.le_trans hg2.1 hg5.1))
    (Nat.le_trans hg2.1 (Nat.le_trans hg5.1 hg6.1)) (hy5.grow (AgreeA.of_grow hg6))
  obtain ⟨-, hsb, ps, hps, -⟩ := hsp6
  obtain ⟨-, -, -, hf7, -⟩ := consW_decN h7 hS6.2.2.2.1 hS6.2.2.2.2.2 hsb hps
  rw [cfgK6_some]
  exact RSim.pure_some ⟨hS7, hg2.trans (hg5.trans (hg6.trans hg7)), by simpa using hsp7, ⟨mp6,
    rec2NoMR_iw hf7 hM6⟩, hf2.trans ((MFr.of_iw hf5).up.trans (hf6.trans (MFr.of_iw hf7).up))⟩

theorem cfgW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (bsh : BlockShape)
    (ihs : List (Nat × Nat)) (n : Nat) :
    ∀ (m : Mem) (a : AState) (mo ml io il i fo fl : Word) (fs : List EIdx) (mp0 : Std.HashMap EIdx Bool),
    StageR dn vis fe m a →
    decHL m mo.toNat ml.toNat = some bsh.memberNames → mo.toNat + ml.toNat ≤ iwTop m →
    StabD (fun m => decPL m (decNN m) io.toNat il.toNat) m ihs → io.toNat + il.toNat < 2 ^ 64 →
    decHL m fo.toNat fl.toNat = some fs → fo.toNat + fl.toNat ≤ iwTop m →
    i.toNat + fl.toNat < 2 ^ 64 → noMR m mp0 →
    RSim (cfgW n m mo ml io il i fo fl) (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a
      (CfoQ dn vis fe m) := by
  induction n with
  | zero => intros; exact RSim.none
  | succ n ih =>
  intro m a mo ml io il i fo fl fs mp0 hS hmn hmb hih hib hfs hfb hi hM
  have hsz := hS.2.2.2.1
  have htop := hS.2.1
  by_cases hfl : fl = 0
  · rw [cfgW_nil (h := hfl)]
    obtain rfl : fs = [] := by
      have := decHL_length m hfs; rw [hfl] at this; exact List.eq_nil_of_length_eq_zero (by simpa using this)
    rw [ConRon.Arena.classFieldsOf]
    exact RSim.pure_some ⟨hS, IWGrow.refl m,
      (by simpa using SPLA.nil (b := iwTop m) (dec := decCF) (m := m) 0 (by omega)), ⟨mp0, hM⟩, MFr.refl _ _ _⟩
  rw [cfgW_cons (h := hfl)]
  obtain ⟨w0, fs', rfl, hw0, hw0H, hfs'⟩ := decHL_cons hfs hfl (by omega)
  subst hw0
  obtain ⟨hsum, hfo1⟩ := toNat_succ_of_lt (o := fo) (l := fl) (by omega) hfl
  have hfl1 : (fl - 1).toNat + 1 = fl.toNat := by omega
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [ConRon.Arena.classFieldsOf]
  refine RSim.bind (K := cfgK1 n _ mo ml io il i) rfl (simFvarTypeD hS hw0H) ?_
  rintro ⟨r1, m1⟩ w a1 h1 ⟨hS1, hg1, hwH, hwd⟩
  dsimp only at hS1 hg1 hwH hwd
  subst hwd
  rw [cfgK1_some]
  have hM1 := rec2NoMR_ftd h1 hM
  refine RSim.bind (K := cfgK2 n _ io il i (r1.headD 0)) rfl
    (rec2SimNestOcc hS1 hwH (by rw [decHL_grow hg1 hmb]; exact hmn) (by omega) hM1 n) ?_
  rintro ⟨occ, m2⟩ b a2 - ⟨ha2, hob, hM2, hS2, hg2, hf2⟩
  subst a2
  dsimp only at hob hM2 hS2 hg2 hf2
  have hf12 : MFr [NOM] [204, 205] m m2 := (MFr.of_frame (ftdF_frame h1) (by simp) (by simp)).up.trans hf2
  rw [cfgK2_some]
  have hg12 := hg1.trans hg2
  refine RSim.lstep (K := cfgK3 n _ (r1.headD 0) occ m2) rfl fun ⟨hc, cls⟩ h3 => ?_
  obtain ⟨hcnt, hcls⟩ := cfhW_ok n m2 io il i hc cls ihs h3 (hih m2 hg12) hib hS2.2.2.2.1
  have hrest : ∀ m5, StageR dn vis fe m5 a1 → IWGrow m2 m5 → noMR m5 ∅ →
      RSim (cfgW n m5 mo ml io il (i + 1) (fo + 1) (fl - 1))
        (ConRon.Arena.classFieldsOf bsh ihs (i.toNat + 1) fs') a1 (CfoQ dn vis fe m5) := by
    intro m5 hS5 hg5 hM5
    have hg := hg12.trans hg5
    have := ih m5 a1 mo ml io il (i + 1) (fo + 1) (fl - 1) fs' ∅ hS5
      (by rw [decHL_grow hg hmb]; exact hmn) (Nat.le_trans hmb hg.1) (hih.grow hg) hib
      (by rw [decHL_grow hg (by omega)]; exact hfs') (by have := hg.1; omega) (by omega) hM5
    rwa [hi1] at this
  by_cases hA : occ = 0 ∧ hc = 0
  · rw [cfgK3_ord (h := hA)]
    have hb : b = false := by rw [← hob, hA.1]; rfl
    have hlen : (List.filter (fun h => h.1 == i.toNat) ihs).length = 0 := by rw [← hcnt, hA.2]; rfl
    subst hb
    simp only [hlen, Bool.not_false, Bool.true_and, beq_self_eq_true, ite_true]
    refine cfgTail hS2 hg12 hM2 hf12 rfl ?_ hrest
    intro m'' hw
    have := hw 0 (by simp)
    simp only [decCF]; simp at this; rw [this]; rfl
  by_cases hB : occ ≠ 0 ∧ hc = 1
  · rw [cfgK3_rec (h0 := hA) (h := hB)]
    have hb : b = true := by rw [← hob]; simpa using hB.1
    have hlen : (List.filter (fun h => h.1 == i.toNat) ihs).length = 1 := by rw [← hcnt, hB.2]; rfl
    subst hb
    obtain ⟨hh, hhs⟩ := List.length_eq_one_iff.mp hlen
    obtain ⟨hcl, hcl64⟩ := hcls hh hhs
    simp only [hhs, Bool.not_true, Bool.false_and, Bool.true_and,
      ite_false, Bool.false_eq_true]
    refine RSim.bind (K := cfgK4 n _ cls) rfl (rec2SimPiBinders n hS2 hwH) ?_
    rintro ⟨r4, m4⟩ ⟨bs, e⟩ a4 - ⟨rfl, hS4, hg4, hf4, hd4⟩
    dsimp only at hS4 hg4 hf4 hd4
    rw [cfgK4_some]
    have hbl : bs.length = (r4.tail.headD 0).toNat := decHL_length _ hd4
    refine cfgTail hS4 (hg12.trans hg4) (rec2NoMR_iw hf4 hM2) (hf12.trans (MFr.of_iw hf4).up) rfl ?_
      (fun m5 hS5 hg5 hM5 => hrest m5 hS5 (hg4.trans hg5) hM5)
    intro m'' hw
    have h0 := hw 0 (by simp)
    have h1 := hw 1 (by simp)
    have h2 := hw 2 (by simp)
    simp at h0 h1 h2
    simp only [decCF, h0, h1, h2, List.getD_cons_zero, hcl, UInt64.toNat_ofNat_of_lt' hcl64, hbl]
    rcases r4 with _ | ⟨x0, _ | ⟨x1, t⟩⟩ <;> rfl
  rw [cfgK3_bad (h0 := hA) (h := hB)]
  exact RSim.none

/-! ## `class_fields_of` -/

l_model classFieldsOf_spec (p : Prog) (h : CfoProg p)
  fns [h.cfo ↦ cfoW]
  specs [blockShapeMemberNames_spec p h.alloc h.mnc h.mn n, classFieldsOfGo_spec p h n]
  grind [arena_grind] simp []

theorem cfoW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (bsh : BlockShape)
    (ihs : List (Nat × Nat)) (n : Nat) (m : Mem) (a : AState) (q io il i fo fl : Word) (fs : List EIdx)
    (mp0 : Std.HashMap EIdx Bool) (hS : StageR dn vis fe m a) (hb : BSOK m q.toNat bsh)
    (hih : StabD (fun m => decPL m (decNN m) io.toNat il.toNat) m ihs) (hib : io.toNat + il.toNat < 2 ^ 64)
    (hfs : decHL m fo.toNat fl.toNat = some fs) (hfb : fo.toNat + fl.toNat ≤ iwTop m)
    (hi : i.toNat + fl.toNat < 2 ^ 64) (hM : noMR m mp0) :
    RSim (cfoW n m q io il i fo fl) (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a (CfoQ dn vis fe m) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rw [cfoW.arm1]
  refine RSim.lstep (K := cfoW.k_block_shape_member_names n io il i fo fl) rfl fun ⟨r1, m1⟩ h1 => ?_
  have ht := hb.ptop
  have hsz := hS.2.2.2.1
  have hts : iwTop m ≤ (m.arr64 IW).size := hS.2.1
  have hf1 := (memberNamesW_dec h1 hsz hS.2.2.2.2.2 hb.dec (by omega) hb.2.1 hb.2.2).2.2.2.1
  obtain ⟨hS1, hg1, -, hd1, ht1⟩ := memberNamesW_stage h1 hS hb
  rw [cfoW.k_block_shape_member_names.arm1]
  refine RSim.bindPure (K := cfoW.k_class_fields_of_go) rfl (cfgW_sim dn vis fe bsh ihs n m1 a _ _ io il i fo fl fs mp0 hS1 hd1
    (by omega) (hih.grow hg1) hib (by rw [decHL_grow hg1 hfb]; exact hfs) (Nat.le_trans hfb hg1.1) hi
    (rec2NoMR_iw hf1 hM)) ?_
  rintro ⟨r2, m2⟩ ks a2 - ⟨hS2, hg2, hsp2, hM2, hf2⟩
  rw [cfoW.k_class_fields_of_go.arm1]
  exact RSim.pure_some ⟨hS2, hg1.trans hg2, by simpa using hsp2.mono hg1.1, hM2, (MFr.of_iw hf1).up.trans hf2⟩

/-- **`class_fields_of` refines `classFieldsOf`** (through the stub `fvar_type_d`): the fields' kinds
are a stable slice of `ClassField` records; `nest_occ`'s memo relation is needed before and holds
after (at some map). -/
@[refines ConRon.Arena.classFieldsOf]
theorem classFieldsOf_refines (p : Prog) (hp : CfoProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (q io il i fo fl : Word) (bsh : BlockShape)
    (ihs : List (Nat × Nat)) (fs : List EIdx) (mp0 : Std.HashMap EIdx Bool)
    (hS : StageR dn vis fe s₀.mem a₀) (hb : BSOK s₀.mem q.toNat bsh)
    (hih : StabD (fun m => decPL m (decNN m) io.toNat il.toNat) s₀.mem ihs) (hib : io.toNat + il.toNat < 2 ^ 64)
    (hfs : decHL s₀.mem fo.toNat fl.toNat = some fs) (hfb : fo.toNat + fl.toNat ≤ iwTop s₀.mem)
    (hi : i.toNat + fl.toNat < 2 ^ 64) (hM : noMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fields_of" [q, io, il, i, fo, fl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a₀ ∧
      CfoQ dn vis fe s₀.mem (r, s'.mem) (AM.st (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a₀)
        (AM.res (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a₀); ⊤⦄ :=
  triple_post (classFieldsOf_spec p hp n s₀ q io il i fo fl) fun _ _ ⟨hl, hw⟩ =>
    ⟨hl, (cfoW_sim dn vis fe bsh ihs n _ a₀ q io il i fo fl fs mp0 hS hb hih hib hfs hfb hi hM).am hw⟩

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

local notation "V" => ConLeche.CheckMode.verified

/-- A fresh `rec6` record (at or above `b`) of parts stable above `b` decodes stably above `b` as a
`ClassCtor`. -/
theorem rec6_decCC {m m' : Mem} {q : Word} {cvw nFw ko kl tyD tyN : Word} {cv : IConstantVal}
    {kinds : List ClassField} {b : Nat}
    (hget : ∀ j < 6, (m'.arr64 IW)[q.toNat + j]? = [cvw, nFw, ko, kl, tyD, tyN][j]?)
    (hq : q.toNat + 6 ≤ iwTop m') (hb : b ≤ q.toNat) (hg : IWGrow m m')
    (hcv : DecB (fun m => decCVp m cvw.toNat) m cv)
    (hks : SPLA b decCF m ko.toNat kl.toNat kinds) (hD : H tyD) (hN : H tyN) :
    StabA b (fun m => decCC m q.toNat) m' ⟨cv, nFw.toNat, kinds, decI tyD, decI tyN⟩ := by
  intro m'' hA
  have hA0 : AgreeA b m m'' := (AgreeA.of_grow hg).trans hA
  have hw : ∀ j (hj : j < 6), iwN m'' (q.toNat + j) =
      some ([cvw, nFw, ko, kl, tyD, tyN][j]'(by simpa using hj)).toNat := fun j hj => by
    rw [hA.iwN (by omega) (by omega)]
    simp only [iwN, nat?, iwA]
    rw [hget j hj, List.getElem?_eq_getElem (by simp; omega)]; rfl
  have h0 := hw 0 (by omega)
  have h1 := hw 1 (by omega)
  have h2 := hw 2 (by omega)
  have h3 := hw 3 (by omega)
  have hhD : (iwH m'' (q.toNat + 4) : Option EIdx) = some (decI tyD) := by
    rw [hA.iwH (by omega) (by omega)]
    simp only [iwH, hd?, iwA]
    rw [hget 4 (by omega)]
    simp [hD]
  have hhN : (iwH m'' (q.toNat + 5) : Option EIdx) = some (decI tyN) := by
    rw [hA.iwH (by omega) (by omega)]
    simp only [iwH, hd?, iwA]
    rw [hget 5 (by omega)]
    simp [hN]
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3
  have e1 : decCVp m'' cvw.toNat = some cv := stabA_decCVp hcv b m'' hA0
  have e3 := hks.stab m'' hA0
  simp only [decCC, decAt, h0, Nat.add_assoc, Nat.reduceAdd, h1, h2, h3, Option.bind_eq_bind,
    Option.bind_some, e1, e3, hhD, hhN]
  rfl

end L.Ind

end

end
