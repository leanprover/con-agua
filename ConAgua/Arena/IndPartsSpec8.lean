import ConAgua.Arena.IndPartsSpec7
import ConAgua.Arena.RecClassSpec
import ConAgua.Arena.IndRealNames
import ConAgua.Arena.IndPartsSpec4

/-!
# Refinements of `IndParts`, part 8 (lane `indproofs2`, helper `parts`): the block split, relations

The relational lemmas of `block_split_recs`, `block_split_ctors`, `block_split` (models in
`IndPartsSpec7.lean`) and the shared pieces: the block decoded below the tops
(`DecB (decEBlk dn · off l)`), a constant record's kind and fields (`partsCI_fields`), a fresh
record read back below the top (`partsFresh`), `sl_cons` of a pointer onto a decoded pointer slice
(`partsConsPL`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The block below the tops -/

theorem partsErNat_mono (i : Nat) : OMono (fun m => nat? (erA m) i) := ⟨fun _ _ _ he h => he.2.nat? h⟩

theorem decEBlk_mono (dn : NIdx → Option ConLeche.Name) (off l : Nat) :
    OMono (fun m => decEBlk dn m off l) :=
  OMono.mapM (fun j => OMono.bind (partsErNat_mono (off + j))
    (fun q => (⟨fun _ _ _ he h => he.2.decCI h⟩ : OMono (fun m => decCI (erA m) dn q)))) _

/-- A constant record's kind word. -/
def ciKind : IConstantInfo → Nat
  | .axiomInfo _ => 0
  | .defnInfo .. => 1
  | .thmInfo _ => 2
  | .indInfo .. => 3
  | .ctorInfo .. => 4
  | .recInfo .. => 5

theorem ciKind_lt (x : IConstantInfo) : ciKind x < 7 := by cases x <;> simp [ciKind]

/-- The kind word compared with a small constant. -/
theorem ciKind_w (x : IConstantInfo) (k : Nat) (hk : k < 7) :
    UInt64.ofNat (ciKind x) = UInt64.ofNat k ↔ ciKind x = k := by
  constructor
  · intro e
    have := congrArg UInt64.toNat e
    have h1 := ciKind_lt x
    rw [UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega),
      UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)] at this
    exact this
  · intro e; rw [e]

/-- **A decoded constant record's kind and the fields the split reads.** -/
theorem partsCI_fields {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat}
    {ci : IConstantInfo} (h : decCI a dn q = some ci) :
    nat? a q = some (ciKind ci) ∧
    (match ci with
     | .indInfo cv _ => decCV a (q + 1) = some cv
     | .ctorInfo cv nP nF => decCV a (q + 1) = some cv ∧ nat? a (q + 5) = some nP ∧
         nat? a (q + 6) = some nF
     | .recInfo cv mI rP rules => decCV a (q + 1) = some cv ∧ nat? a (q + 5) = some mI ∧
         nat? a (q + 6) = some rP ∧ ∃ o l, nat? a (q + 7) = some o ∧ nat? a (q + 8) = some l ∧
         decRules a o l = some rules
     | _ => True) := by
  unfold decCI at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨kd, hkd, h⟩ := h
  rcases kd with _ | _ | _ | _ | _ | _ | kd
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, -, rfl⟩ := h; exact ⟨hkd, trivial⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, -, v, -, hh, -, rfl⟩ := h; exact ⟨hkd, trivial⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, -, rfl⟩ := h; exact ⟨hkd, trivial⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, caps, -, rfl⟩ := h; exact ⟨hkd, hcv⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, nP, hnP, nF, hnF, rfl⟩ := h; exact ⟨hkd, hcv, hnP, hnF⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, mI, hmI, rP, hrP, o, ho, l, hl, rules, hrules, rfl⟩ := h
    exact ⟨hkd, hcv, hmI, hrP, o, l, ho, hl, hrules⟩
  · simp at h

/-- The block's head, below the tops. -/
theorem partsBlk_cons {dn : NIdx → Option ConLeche.Name} {m : Mem} {off L : Nat}
    {blk : List IConstantInfo} (h : DecB (fun m => decEBlk dn m off (L + 1)) m blk) :
    ∃ q x rest, blk = x :: rest ∧ nat? (erA (truncM m)) off = some q ∧
      decCI (erA (truncM m)) dn q = some x ∧ DecB (fun m => decEBlk dn m (off + 1) L) m rest := by
  have h' : decEBlk dn (truncM m) off (L + 1) = some blk := h
  rw [decEBlk_succ] at h'
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h'
  obtain ⟨q, hq, x, hx, rest, hr, rfl⟩ := h'
  exact ⟨q, x, rest, rfl, hq, hx, hr⟩

theorem partsBlk_nil {dn : NIdx → Option ConLeche.Name} {m : Mem} {off : Nat}
    {blk : List IConstantInfo} (h : DecB (fun m => decEBlk dn m off 0) m blk) : blk = [] := by
  have h' : decEBlk dn (truncM m) off 0 = some blk := h
  simp only [decEBlk, List.range_zero, List.mapM_nil, pure, Option.some.injEq] at h'
  exact h'.symm

/-- **A word of the record pool read below the top**, in any memory the pools grew into. -/
theorem partsErRd {m m' : Mem} (hg : IWGrow m m') {i v : Nat} (h : nat? (erA (truncM m)) i = some v)
    {w : Word} (hw : w.toNat = i) :
    rdW (m'.arr64 EREC) w = UInt64.ofNat v ∧ v < 2 ^ 64 ∧ i < erTop m := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨hi, hx'⟩ := truncM_er_get hx
  simp only [erA] at hx'
  refine ⟨?_, x.toNat_lt, hi⟩
  rw [rdW_of_get? hw.symm (by rw [hg.2.2.2 i hi]; exact hx')]
  simp

/-- **A fresh record, read back below the new top.** -/
theorem partsFresh {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m'))
    (hS : StageR dn vis fe m a) (hl : ws.length < 2 ^ 64) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ q.toNat = iwTop m ∧ q.toNat + ws.length = iwTop m' ∧
      ∀ j (hj : j < ws.length), iwN (truncM m') (q.toNat + j) = some (ws[j]).toNat := by
  obtain ⟨hS', hg, hq, htop, hget⟩ := posRecW_stage h hS hl
  refine ⟨hS', hg, hq, by omega, fun j hj => ?_⟩
  rw [iwN_truncM (by omega)]
  simp only [iwN, nat?, iwA, hget j hj, List.getElem?_eq_getElem hj, Option.map_some]

/-- **`sl_cons` of a pointer onto a pointer slice decoded below the tops.** -/
theorem partsConsPL {α : Type} {f : Mem → Nat → Option α} (hf : ∀ q, OMono (fun m => f m q))
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List α} {y : α}
    (h : consW n m x o l = some (r, m')) (hS : StageR dn vis fe m a)
    (hb : o.toNat + l.toNat ≤ iwTop m)
    (hxs : DecB (fun m => decPL m (f m) o.toNat l.toNat) m xs) (hy : DecB (fun m => f m x.toNat) m y) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      DecB (fun m => decPL m (f m) (r.headD 0).toNat (r.tail.headD 0).toNat) m' (y :: xs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  have hxs' : decPL (truncM m) (f (truncM m)) o.toNat l.toNat = some xs := hxs
  rw [decPL_eq_bind] at hxs'
  simp only [Option.bind_eq_some_iff] at hxs'
  obtain ⟨ps, hps, hmap⟩ := hxs'
  have hps' : decNL m o.toNat l.toNat = some ps :=
    (OMono.decNL _ _).mono _ _ _ (IWGrow.refl m).truncExt hps
  obtain ⟨hS', hg, hdn, htop⟩ := consW_stageN h hS hb hps'
  refine ⟨hS', hg, ?_, htop⟩
  show decPL (truncM m') (f (truncM m')) _ _ = some (y :: xs)
  have hdn' : decNL (truncM m') (r.headD 0).toNat (r.tail.headD 0).toNat = some (x.toNat :: ps) :=
    decNL_decB hdn (Nat.le_of_eq htop)
  rw [decPL_eq_bind, hdn']
  have hy' : f (truncM m') x.toNat = some y := hy.grow (hf _) hg
  have hm' : ps.mapM (f (truncM m')) = some xs :=
    (show DecB (fun m => ps.mapM (f m)) m xs from hmap).grow (OMono.mapM hf ps) hg
  simp [hy', hm']

/-- A word `w + k` of the record pool, read below the top in any memory the pools grew into. -/
theorem partsErW {m m1 : Mem} (hg : IWGrow m m1) {w k : Word} {v : Nat}
    (h : nat? (erA (truncM m)) (w.toNat + k.toNat) = some v) :
    (rdW (m1.arr64 EREC) (w + k)).toNat = v ∧ w.toNat + k.toNat < erTop m := by
  have hlt : w.toNat + k.toNat < erTop m := by
    simp only [nat?, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, -⟩ := h; exact (truncM_er_get hx).1
  have hE : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt
  have hw : (w + k).toNat = w.toNat + k.toNat := by rw [UInt64.toNat_add]; omega
  obtain ⟨h1, h2, -⟩ := partsErRd hg h hw
  rw [h1]; exact ⟨UInt64.toNat_ofNat_of_lt' h2, hlt⟩

/-- A constant decoded below the top lies below the top. -/
theorem partsDecCV_lt {m : Mem} {i : Nat} {cv : IConstantVal} (h : decCV (erA (truncM m)) i = some cv) :
    i < erTop m := by
  simp only [decCV, bind, Option.bind_eq_some_iff] at h
  obtain ⟨nm, hnm, -⟩ := h
  simp only [hd?, bind, Option.bind_eq_some_iff] at hnm
  obtain ⟨x, hx, -⟩ := hnm
  exact (truncM_er_get hx).1

/-- A slice result decoded below the tops (`(off, len)`, the slice below the top). -/
def PSlR {α : Type} (f : Mem → Nat → Option α) (xs : List α) (o l : Word) (m : Mem) : Prop :=
  DecB (fun m => decPL m (f m) o.toNat l.toNat) m xs ∧ o.toNat + l.toNat ≤ iwTop m

theorem PSlR.grow {α : Type} {f : Mem → Nat → Option α} (hf : ∀ q, OMono (fun m => f m q))
    {xs : List α} {o l : Word} {m m' : Mem} (h : PSlR f xs o l m) (hg : IWGrow m m') : PSlR f xs o l m' :=
  ⟨h.1.grow (OMono.decPL hf _ _) hg, Nat.le_trans h.2 hg.1⟩

theorem PSlR.nil {α : Type} (f : Mem → Nat → Option α) (m : Mem) : PSlR f [] 0 0 m :=
  ⟨by show decPL _ _ _ _ = _; simp [decPL], by simp⟩

/-- `block_split_recs`' result `(ok, off, len)` against the twin's `Option`. -/
def RecsR (x : Option (List (IConstantVal × Nat × Nat × List IRecRule))) (r : List Word) (m : Mem) :
    Prop :=
  match x with
  | none => r.headD 0 = 0
  | some rs => r.headD 0 = 1 ∧ PSlR decSR rs (r.tail.headD 0) (r.tail.tail.headD 0) m

theorem partsPred_of {l : Word} {L : Nat} (h : l.toNat = L + 1) : (l - 1).toNat = L := by
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega

theorem partsSucc_of_lt {o : Word} {E : Nat} (h : o.toNat < E) (hE : E < 2 ^ 64) :
    (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega

/-- **The block's head as the splits read it**: the record pointer at `off`, its kind word, the
decoded record, the rest of the block at `off + 1`. -/
theorem ipBlkHead {dn : NIdx → Option ConLeche.Name} {m : Mem} {off l : Word}
    {blk : List IConstantInfo} (hl : l ≠ 0) (hblk : DecB (fun m => decEBlk dn m off.toNat l.toNat) m blk) :
    ∃ q x rest, blk = x :: rest ∧ rdW (m.arr64 EREC) off = UInt64.ofNat q ∧ q < 2 ^ 64 ∧
      rdW (m.arr64 EREC) (UInt64.ofNat q) = UInt64.ofNat (ciKind x) ∧
      decCI (erA (truncM m)) dn q = some x ∧
      DecB (fun m => decEBlk dn m (off + 1).toNat (l - 1).toNat) m rest := by
  obtain ⟨L, hL⟩ : ∃ L, l.toNat = L + 1 :=
    ⟨l.toNat - 1, by have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  rw [hL] at hblk
  obtain ⟨q, x, rest, rfl, hq, hx, hrest⟩ := partsBlk_cons hblk
  obtain ⟨hoff, hqb, hofft⟩ := partsErRd (IWGrow.refl m) hq rfl
  obtain ⟨hkw, -, -⟩ := partsErRd (IWGrow.refl m) (partsCI_fields hx).1 (w := UInt64.ofNat q)
    (UInt64.toNat_ofNat_of_lt' hqb)
  have hE : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt
  refine ⟨q, x, rest, rfl, hoff, hqb, hkw, hx, ?_⟩
  rw [partsSucc_of_lt hofft hE, partsPred_of hL]; exact hrest

/-- **`block_split_recs`' model refines `blockSplitRecs`.** -/
theorem bsrW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (off l : Word) (blk : List IConstantInfo) (r : List Word),
    bsrW n m off l = some (r, m') → StageR dn vis fe m a →
    DecB (fun m => decEBlk dn m off.toNat l.toNat) m blk →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ RecsR (ConRon.Arena.blockSplitRecs blk) r m' := by
  induction n with
  | zero => intro m m' a off l blk r h; simp [bsrW] at h
  | succ n ih =>
    intro m m' a off l blk r h hS hblk
    by_cases hl : l = 0
    · rw [bsrW_nil n m off l hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hl] at hblk
      rw [partsBlk_nil hblk]
      exact ⟨hS, IWGrow.refl _, rfl, PSlR.nil _ _⟩
    obtain ⟨q, x, rest, rfl, hoff, hqb, hkw, hx, hrest'⟩ := ipBlkHead hl hblk
    have hE : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt
    by_cases h5 : ciKind x ≠ 5
    · rw [bsrW_no n m off l hl (by rw [hoff, hkw]; exact fun e => h5 ((ciKind_w x 5 (by omega)).1 e))] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨hS, IWGrow.refl _, ?_⟩
      cases x <;> first | exact absurd rfl h5 | simp [RecsR, ConRon.Arena.blockSplitRecs]
    cases x with
    | recInfo cv mI rP rules =>
      obtain ⟨hcv, hmI, hrP, ro, rl, hro, hrl, hrules⟩ := (partsCI_fields hx).2
      rw [bsrW_rec n m off l hl (by rw [hoff, hkw]; rfl), hoff] at h
      obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (by simp [bsrK1])
      obtain ⟨hS1, hg1, hR1⟩ := ih m m1 a (off + 1) (l - 1) rest r1 h1 hS hrest'
      cases hrs : ConRon.Arena.blockSplitRecs rest with
      | none =>
        rw [hrs] at hR1
        rw [bsrK1_fail n m1 _ r1 hR1] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨hS1, hg1, by simp [RecsR, ConRon.Arena.blockSplitRecs, hrs]⟩
      | some rs =>
      rw [hrs] at hR1
      obtain ⟨hok1, hsl1⟩ := hR1
      rw [bsrK1_ok n m1 _ r1 (by rw [hok1]; decide)] at h
      have hqw : (UInt64.ofNat q).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
      obtain ⟨w5, -⟩ := partsErW hg1 (w := UInt64.ofNat q) (k := 5) (by rw [hqw]; exact hmI)
      obtain ⟨w6, -⟩ := partsErW hg1 (w := UInt64.ofNat q) (k := 6) (by rw [hqw]; exact hrP)
      obtain ⟨w7, -⟩ := partsErW hg1 (w := UInt64.ofNat q) (k := 7) (by rw [hqw]; exact hro)
      obtain ⟨w8, -⟩ := partsErW hg1 (w := UInt64.ofNat q) (k := 8) (by rw [hqw]; exact hrl)
      have hq1 : (UInt64.ofNat q + 1).toNat = q + 1 := by
        have := partsDecCV_lt hcv; rw [UInt64.toNat_add, hqw]; simp; omega
      cases h2 : posRecW m1 [UInt64.ofNat q + 1, rdW (m1.arr64 EREC) (UInt64.ofNat q + 5),
          rdW (m1.arr64 EREC) (UInt64.ofNat q + 6), rdW (m1.arr64 EREC) (UInt64.ofNat q + 7),
          rdW (m1.arr64 EREC) (UInt64.ofNat q + 8)] with
      | none => rw [h2] at h; simp [bsrK2] at h
      | some x2 =>
      obtain ⟨rc, m2⟩ := x2
      rw [h2, bsrK2_some] at h
      obtain ⟨hS2, hg2, -, -, hget⟩ := partsFresh h2 hS1 (by simp)
      have hg02 := hg1.trans hg2
      have hdec : DecB (fun m => decSR m rc.toNat) m2 (cv, mI, rP, rules) := by
        have hcv2 : decCVp (truncM m2) (q + 1) = some cv :=
          (show DecB (fun m => decCVp m (q + 1)) m cv from hcv).grow (OMono.decCVp _) hg02
        have hru2 : decRules (erA (truncM m2)) ro rl = some rules :=
          (show DecB (fun m => decRules (erA m) ro rl) m rules from hrules).grow
            (partsDecRules_mono _ _) hg02
        have g0 := hget 0 (by simp); have g1 := hget 1 (by simp); have g2 := hget 2 (by simp)
        have g3 := hget 3 (by simp); have g4 := hget 4 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero, hq1, w5, w6, w7,
          w8] at g0 g1 g2 g3 g4
        show decSR (truncM m2) rc.toNat = _
        simp only [decSR, g0, g1, g2, g3, g4, hcv2, hru2, bind, Option.bind_some,
          pure]
      obtain ⟨r3, m3, h3, h⟩ := ipK_inv h (by simp [bsK3])
      rw [bsK3_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hsl2 := hsl1.grow decSR_mono hg2
      obtain ⟨hS3, hg3, hd3, ht3⟩ := partsConsPL decSR_mono h3 hS2 hsl2.2 hsl2.1 hdec
      refine ⟨hS3, hg02.trans hg3, ?_⟩
      simp only [RecsR, ConRon.Arena.blockSplitRecs, hrs, List.headD_cons, List.tail_cons, true_and]
      exact ⟨hd3, Nat.le_of_eq ht3⟩
    | _ => simp [ciKind] at h5

/-! ## The twins' equations at a head of another kind -/

theorem partsTwinCtors_no {x : IConstantInfo} (rest : List IConstantInfo) (h : ciKind x ≠ 4) :
    ConRon.Arena.blockSplitCtors (x :: rest) =
      (ConRon.Arena.blockSplitRecs (x :: rest)).map (fun rs => ([], rs)) := by
  cases x <;> first
    | exact absurd rfl h
    | (simp only [ConRon.Arena.blockSplitCtors]; split <;> simp_all)

theorem partsTwinSplit_no {x : IConstantInfo} (rest : List IConstantInfo) (h : ciKind x ≠ 3) :
    ConRon.Arena.blockSplit (x :: rest) =
      (ConRon.Arena.blockSplitCtors (x :: rest)).map (fun q => ([], q.1, q.2)) := by
  cases x <;> first
    | exact absurd rfl h
    | (simp only [ConRon.Arena.blockSplit]; split <;> simp_all)

/-- `block_split_ctors`' result `(ok, cs.off, cs.len, rs.off, rs.len)` against the twin. -/
def CtorsR (x : Option (List (IConstantVal × Nat × Nat) × List (IConstantVal × Nat × Nat × List IRecRule)))
    (r : List Word) (m : Mem) : Prop :=
  match x with
  | none => r.headD 0 = 0
  | some (cs, rs) => r.headD 0 = 1 ∧ PSlR decSC cs (r.tail.headD 0) (r.tail.tail.headD 0) m ∧
      PSlR decSR rs (r.tail.tail.tail.headD 0) (r.tail.tail.tail.tail.headD 0) m

/-- **`block_split_ctors`' model refines `blockSplitCtors`.** -/
theorem bscW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (off l : Word) (blk : List IConstantInfo) (r : List Word),
    bscW n m off l = some (r, m') → StageR dn vis fe m a →
    DecB (fun m => decEBlk dn m off.toNat l.toNat) m blk →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ CtorsR (ConRon.Arena.blockSplitCtors blk) r m' := by
  induction n with
  | zero => intro m m' a off l blk r h; simp [bscW] at h
  | succ n ih =>
    intro m m' a off l blk r h hS hblk
    by_cases hl : l = 0
    · rw [bscW_nil n m off l hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hl] at hblk
      rw [partsBlk_nil hblk]
      exact ⟨hS, IWGrow.refl _, rfl, PSlR.nil _ _, PSlR.nil _ _⟩
    obtain ⟨q, x, rest, rfl, hoff, hqb, hkw, hx, hrest'⟩ := ipBlkHead hl hblk
    have hE : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt
    by_cases h4 : ciKind x ≠ 4
    · rw [bscW_no n m off l hl (by rw [hoff, hkw]; exact fun e => h4 ((ciKind_w x 4 (by omega)).1 e))] at h
      obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (by simp [bscKR])
      obtain ⟨hS1, hg1, hR1⟩ := bsrW_ok n m m1 a off l _ r1 h1 hS hblk
      rw [partsTwinCtors_no rest h4]
      cases hrs : ConRon.Arena.blockSplitRecs (x :: rest) with
      | none =>
        rw [hrs] at hR1
        rw [bscKR_fail m1 r1 hR1] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨hS1, hg1, by simp [CtorsR]⟩
      | some rs =>
        rw [hrs] at hR1
        rw [bscKR_ok m1 r1 (by rw [hR1.1]; decide)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨hS1, hg1, by simp only [Option.map_some, CtorsR]; exact ⟨rfl, PSlR.nil _ _, hR1.2⟩⟩
    cases x with
    | ctorInfo cv nP nF =>
      obtain ⟨hcv, hnP, hnF⟩ := (partsCI_fields hx).2
      rw [bscW_ctor n m off l hl (by rw [hoff, hkw]; rfl), hoff] at h
      obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (by simp [bscK1])
      obtain ⟨hS1, hg1, hR1⟩ := ih m m1 a (off + 1) (l - 1) rest r1 h1 hS hrest'
      cases hcs : ConRon.Arena.blockSplitCtors rest with
      | none =>
        rw [hcs] at hR1
        rw [bscK1_fail n m1 _ r1 hR1] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨hS1, hg1, by simp [CtorsR, ConRon.Arena.blockSplitCtors, hcs]⟩
      | some cr =>
      obtain ⟨cs, rs⟩ := cr
      rw [hcs] at hR1
      obtain ⟨hok1, hsl1, hsr1⟩ := hR1
      rw [bscK1_ok n m1 _ r1 (by rw [hok1]; decide)] at h
      have hqw : (UInt64.ofNat q).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
      obtain ⟨w5, -⟩ := partsErW hg1 (w := UInt64.ofNat q) (k := 5) (by rw [hqw]; exact hnP)
      obtain ⟨w6, -⟩ := partsErW hg1 (w := UInt64.ofNat q) (k := 6) (by rw [hqw]; exact hnF)
      have hq1 : (UInt64.ofNat q + 1).toNat = q + 1 := by
        have := partsDecCV_lt hcv; rw [UInt64.toNat_add, hqw]; simp; omega
      obtain ⟨c, m2, h2, h⟩ := ipK_inv h (by simp [bscK2])
      rw [bscK2_some] at h
      obtain ⟨hS2, hg2, -, -, hget⟩ := partsFresh h2 hS1 (by simp)
      have hg02 := hg1.trans hg2
      have hdec : DecB (fun m => decSC m c.toNat) m2 (cv, nP, nF) := by
        have hcv2 : decCVp (truncM m2) (q + 1) = some cv :=
          (show DecB (fun m => decCVp m (q + 1)) m cv from hcv).grow (OMono.decCVp _) hg02
        have g0 := hget 0 (by simp); have g1 := hget 1 (by simp); have g2 := hget 2 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero, hq1, w5, w6]
          at g0 g1 g2
        show decSC (truncM m2) c.toNat = _
        simp only [decSC, g0, g1, g2, hcv2, bind, Option.bind_some, pure]
      rcases h3 : consW n m2 c (r1.tail.headD 0) (r1.tail.tail.headD 0) with _ | ⟨r3, m3⟩ <;> rw [h3] at h
      · simp at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hsl2 := hsl1.grow decSC_mono hg2
      obtain ⟨hS3, hg3, hd3, ht3⟩ := partsConsPL decSC_mono h3 hS2 hsl2.2 hsl2.1 hdec
      refine ⟨hS3, hg02.trans hg3, ?_⟩
      simp only [CtorsR, ConRon.Arena.blockSplitCtors, hcs, List.headD_cons, List.tail_cons, true_and]
      exact ⟨⟨hd3, Nat.le_of_eq ht3⟩, hsr1.grow decSR_mono (hg2.trans hg3)⟩
    | _ => simp [ciKind] at h4

/-- **`blockSplit`'s record at `q`**: its three slices, decoded below the tops. -/
def SplitRec (x : List IConstantVal × List (IConstantVal × Nat × Nat) ×
    List (IConstantVal × Nat × Nat × List IRecRule)) (q : Word) (m : Mem) : Prop :=
  q.toNat + 6 ≤ iwTop m ∧
  PSlR decCVp x.1 (rdW (m.arr64 IW) q) (rdW (m.arr64 IW) (q + 1)) m ∧
  PSlR decSC x.2.1 (rdW (m.arr64 IW) (q + 2)) (rdW (m.arr64 IW) (q + 3)) m ∧
  PSlR decSR x.2.2 (rdW (m.arr64 IW) (q + 4)) (rdW (m.arr64 IW) (q + 5)) m

/-- `block_split`'s result `(ok, q)` against the twin. -/
def SplitR (x : Option (List IConstantVal × List (IConstantVal × Nat × Nat) ×
    List (IConstantVal × Nat × Nat × List IRecRule))) (r : List Word) (m : Mem) : Prop :=
  match x with
  | none => r.headD 0 = 0
  | some t => r.headD 0 = 1 ∧ SplitRec t (r.tail.headD 0) m

/-- A word of the pool below the top reads the same after growth. -/
theorem partsRdIW_grow {m m' : Mem} (hg : IWGrow m m') {w : Word} (hw : w.toNat < iwTop m) :
    rdW (m'.arr64 IW) w = rdW (m.arr64 IW) w := by
  simp only [rdW]; rw [hg.2.2.1 _ hw]

theorem partsWadd {q : Word} {i : Nat} (h : q.toNat + i < 2 ^ 64) :
    (q + UInt64.ofNat i).toNat = q.toNat + i := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]
  exact Nat.mod_eq_of_lt h

/-- The 6-word record written by `rec6`. -/
theorem partsRec6 {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {q b0 b1 b2 b3 b4 b5 : Word} {ts : List IConstantVal}
    {cs : List (IConstantVal × Nat × Nat)} {rs : List (IConstantVal × Nat × Nat × List IRecRule)}
    (h : posRecW m [b0, b1, b2, b3, b4, b5] = some (q, m')) (hS : StageR dn vis fe m a)
    (h1 : PSlR decCVp ts b0 b1 m) (h2 : PSlR decSC cs b2 b3 m) (h3 : PSlR decSR rs b4 b5 m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ SplitRec (ts, cs, rs) q m' := by
  obtain ⟨hS', hg, hq, htop, hget⟩ := posRecW_stage h hS (by simp)
  have hlt : iwTop m' < 2 ^ 64 := (rdW (m'.arr64 CTL) 200).toNat_lt
  simp only [List.length_cons, List.length_nil] at htop
  have rd : ∀ (i : Nat) (hi : i < 6), rdW (m'.arr64 IW) (q + UInt64.ofNat i) =
      [b0, b1, b2, b3, b4, b5][i]'(by simpa using hi) := by
    intro i hi
    exact rdW_of_get? (partsWadd (by omega)).symm
      (by rw [hget i (by simpa using hi), List.getElem?_eq_getElem])
  have r0 : rdW (m'.arr64 IW) q = b0 := by simpa using rd 0 (by omega)
  have r1 : rdW (m'.arr64 IW) (q + 1) = b1 := by simpa using rd 1 (by omega)
  have r2 : rdW (m'.arr64 IW) (q + 2) = b2 := by simpa using rd 2 (by omega)
  have r3 : rdW (m'.arr64 IW) (q + 3) = b3 := by simpa using rd 3 (by omega)
  have r4 : rdW (m'.arr64 IW) (q + 4) = b4 := by simpa using rd 4 (by omega)
  have r5 : rdW (m'.arr64 IW) (q + 5) = b5 := by simpa using rd 5 (by omega)
  refine ⟨hS', hg, by omega, ?_, ?_, ?_⟩
  · rw [r0, r1]; exact h1.grow (fun _ => OMono.decCVp _) hg
  · rw [r2, r3]; exact h2.grow decSC_mono hg
  · rw [r4, r5]
    exact h3.grow decSR_mono hg

/-- **`block_split`'s model refines `blockSplit`.** -/
theorem bsW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (off l : Word) (blk : List IConstantInfo) (r : List Word),
    bsW n m off l = some (r, m') → StageR dn vis fe m a →
    DecB (fun m => decEBlk dn m off.toNat l.toNat) m blk →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ SplitR (ConRon.Arena.blockSplit blk) r m' := by
  induction n with
  | zero => intro m m' a off l blk r h; simp [bsW] at h
  | succ n ih =>
    intro m m' a off l blk r h hS hblk
    by_cases hl : l = 0
    · rw [bsW_nil n m off l hl] at h
      rw [hl] at hblk
      rw [partsBlk_nil hblk]
      rcases h1 : posRecW m [0, 0, 0, 0, 0, 0] with _ | ⟨q, m1⟩ <;> rw [h1] at h
      · cases h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS1, hg1, hR⟩ := partsRec6 h1 hS (PSlR.nil _ _) (PSlR.nil _ _) (PSlR.nil _ _)
      exact ⟨hS1, hg1, by simp [SplitR, ConRon.Arena.blockSplit, ConRon.Arena.blockSplitCtors,
        ConRon.Arena.blockSplitRecs]; exact hR⟩
    obtain ⟨q, x, rest, rfl, hoff, hqb, hkw, hx, hrest'⟩ := ipBlkHead hl hblk
    have hE : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt
    by_cases h3 : ciKind x ≠ 3
    · rw [bsW_no n m off l hl (by rw [hoff, hkw]; exact fun e => h3 ((ciKind_w x 3 (by omega)).1 e))] at h
      obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (by simp [bsKC])
      obtain ⟨hS1, hg1, hR1⟩ := bscW_ok n m m1 a off l _ r1 h1 hS hblk
      rw [partsTwinSplit_no rest h3]
      cases hcs : ConRon.Arena.blockSplitCtors (x :: rest) with
      | none =>
        rw [hcs] at hR1
        rw [bsKC_fail m1 r1 hR1] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨hS1, hg1, by simp [SplitR]⟩
      | some cr =>
        obtain ⟨cs, rs⟩ := cr
        rw [hcs] at hR1
        obtain ⟨hok1, hc1, hr1⟩ := hR1
        rw [bsKC_ok m1 r1 (by rw [hok1]; decide)] at h
        rcases h2 : posRecW m1 [0, 0, r1.tail.headD 0, r1.tail.tail.headD 0, r1.tail.tail.tail.headD 0,
            r1.tail.tail.tail.tail.headD 0] with _ | ⟨q2, m2⟩ <;> rw [h2] at h
        · cases h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨hS2, hg2, hR⟩ := partsRec6 h2 hS1 (PSlR.nil _ _) hc1 hr1
        exact ⟨hS2, hg1.trans hg2, by simp only [Option.map_some, SplitR]; exact ⟨rfl, hR⟩⟩
    cases x with
    | indInfo cv caps =>
      have hcv := (partsCI_fields hx).2
      rw [bsW_ind n m off l hl (by rw [hoff, hkw]; rfl), hoff] at h
      obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (by simp [bsK1])
      obtain ⟨hS1, hg1, hR1⟩ := ih m m1 a (off + 1) (l - 1) rest r1 h1 hS hrest'
      cases hsp : ConRon.Arena.blockSplit rest with
      | none =>
        rw [hsp] at hR1
        rw [bsK1_fail n m1 _ r1 hR1] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨hS1, hg1, by simp [SplitR, ConRon.Arena.blockSplit, hsp]⟩
      | some t =>
      obtain ⟨ts, cs, rs⟩ := t
      rw [hsp] at hR1
      obtain ⟨hok1, htop1, hts1, hcs1, hrs1⟩ := hR1
      rw [bsK1_ok n m1 _ r1 (by rw [hok1]; decide)] at h
      generalize hq1 : r1.tail.headD 0 = q1 at h htop1 hts1 hcs1 hrs1
      have hqw : (UInt64.ofNat q).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
      have hq1' : (UInt64.ofNat q + 1).toNat = q + 1 := by
        have := partsDecCV_lt hcv; rw [UInt64.toNat_add, hqw]; simp; omega
      have hy : DecB (fun m => decCVp m (UInt64.ofNat q + 1).toNat) m1 cv := by
        rw [hq1']; exact (show DecB (fun m => decCVp m (q + 1)) m cv from hcv).grow (OMono.decCVp _) hg1
      obtain ⟨r2, m2, h2, h⟩ := ipK_inv h (by simp [bsK2])
      rw [bsK2_some] at h
      obtain ⟨hS2, hg2, hd2, ht2⟩ := partsConsPL (fun _ => OMono.decCVp _) h2 hS1 hts1.2 hts1.1 hy
      have hlt1 : iwTop m1 < 2 ^ 64 := (rdW (m1.arr64 CTL) 200).toNat_lt
      have e : ∀ i, i < 6 → rdW (m2.arr64 IW) (q1 + UInt64.ofNat i) = rdW (m1.arr64 IW) (q1 + UInt64.ofNat i) :=
        fun i hi => partsRdIW_grow hg2 (by rw [partsWadd (by omega)]; omega)
      have e2 : rdW (m2.arr64 IW) (q1 + 2) = rdW (m1.arr64 IW) (q1 + 2) := e 2 (by omega)
      have e3 : rdW (m2.arr64 IW) (q1 + 3) = rdW (m1.arr64 IW) (q1 + 3) := e 3 (by omega)
      have e4 : rdW (m2.arr64 IW) (q1 + 4) = rdW (m1.arr64 IW) (q1 + 4) := e 4 (by omega)
      have e5 : rdW (m2.arr64 IW) (q1 + 5) = rdW (m1.arr64 IW) (q1 + 5) := e 5 (by omega)
      rw [e2, e3, e4, e5] at h
      rcases h3 : posRecW m2 [r2.headD 0, r2.tail.headD 0, rdW (m1.arr64 IW) (q1 + 2),
          rdW (m1.arr64 IW) (q1 + 3), rdW (m1.arr64 IW) (q1 + 4), rdW (m1.arr64 IW) (q1 + 5)] with _ | ⟨q3, m3⟩ <;> rw [h3] at h
      · cases h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS3, hg3, hR⟩ := partsRec6 h3 hS2 ⟨hd2, Nat.le_of_eq ht2⟩ (hcs1.grow decSC_mono hg2)
        (hrs1.grow decSR_mono hg2)
      refine ⟨hS3, (hg1.trans hg2).trans hg3, ?_⟩
      simp only [SplitR, ConRon.Arena.blockSplit, hsp, List.headD_cons, List.tail_cons, true_and]
      exact hR
    | _ => simp [ciKind] at h3

/-! ## The census theorems -/

/-- **The program bundle of the split** (one field per lookup). -/
structure IndPartsProg (p : Prog) : Prop where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  nr : NrF p
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  rec3 : p.lookup "rec3" = some rec3
  rec5 : p.lookup "rec5" = some rec5
  rec6 : p.lookup "rec6" = some rec6
  recs : p.lookup "block_split_recs" = some blockSplitRecs
  ctors : p.lookup "block_split_ctors" = some blockSplitCtors
  split : p.lookup "block_split" = some blockSplit
  strip : StripProg p
  ad : AdF p

/-- **`block_split_recs` refines `blockSplitRecs`**: the block an `EREC` slice of constant records
decoded below the tops; the result `(ok, off, len)` is the twin's `Option`, the slice of fresh
`[cv, mI, rP, rules.off, rules.len]` records decoded below the tops. -/
@[refines ConRon.Arena.blockSplitRecs]
theorem blockSplitRecs_refines (p : Prog) (hP : IndPartsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (off l : Word)
    (blk : List IConstantInfo) (hS : StageR dn vis fe s₀.mem a₀)
    (hblk : DecB (fun m => decEBlk dn m off.toNat l.toNat) s₀.mem blk) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_split_recs" [off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      RecsR (ConRon.Arena.blockSplitRecs blk) r s'.mem; ⊤⦄ :=
  triple_post (bsr_spec p hP.alloc hP.copy hP.cons hP.rec5 hP.recs n s₀ off l) fun r _ ⟨hl, hm⟩ =>
    ⟨hl, bsrW_ok n _ _ a₀ off l blk r hm hS hblk⟩

/-- **`block_split_ctors` refines `blockSplitCtors`.** -/
@[refines ConRon.Arena.blockSplitCtors]
theorem blockSplitCtors_refines (p : Prog) (hP : IndPartsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (off l : Word)
    (blk : List IConstantInfo) (hS : StageR dn vis fe s₀.mem a₀)
    (hblk : DecB (fun m => decEBlk dn m off.toNat l.toNat) s₀.mem blk) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_split_ctors" [off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      CtorsR (ConRon.Arena.blockSplitCtors blk) r s'.mem; ⊤⦄ :=
  triple_post (bsc_spec p hP.alloc hP.copy hP.cons hP.rec5 hP.rec3 hP.recs hP.ctors n s₀ off l)
    fun r _ ⟨hl, hm⟩ => ⟨hl, bscW_ok n _ _ a₀ off l blk r hm hS hblk⟩

/-- **`block_split` refines `blockSplit`**: the result `(ok, q)`, `q` the 6-word record of the
formers', constructors' and recursors' slices (`SplitRec`). -/
@[refines ConRon.Arena.blockSplit]
theorem blockSplit_refines (p : Prog) (hP : IndPartsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (off l : Word)
    (blk : List IConstantInfo) (hS : StageR dn vis fe s₀.mem a₀)
    (hblk : DecB (fun m => decEBlk dn m off.toNat l.toNat) s₀.mem blk) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_split" [off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      SplitR (ConRon.Arena.blockSplit blk) r s'.mem; ⊤⦄ :=
  triple_post (bs_spec p hP.alloc hP.copy hP.cons hP.rec5 hP.rec3 hP.rec6 hP.recs hP.ctors hP.split
    n s₀ off l) fun r _ ⟨hl, hm⟩ => ⟨hl, bsW_ok n _ _ a₀ off l blk r hm hS hblk⟩

end L.Ind
