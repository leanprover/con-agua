import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndPartsSpec.RecTW
import ConAgua.Arena.IndPartsSpec.SetEqW
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# BlockRecNameSetOk: `ConRon.Arena.blockGroups`, `ConRon.Arena.blockRecNameSetOk`, `ConRon.Arena.ctorMember`

The refinement theorems `ctorMember_refines`, `blockGroups_refines`, `blockRecNameSetOk_refines` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem partsDrop3 (r : List Word) : (r.drop 3).headD 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

/-- `memberIdxAt?`'s index lies in the names. -/
theorem partsMemberIdx_lt {names : List NIdx} {lvls : LsIdx} {e : EIdx} {a a' : AState} {i : Nat}
    (h : (ConRon.Arena.memberIdxAt? names lvls e).run a = .ok (some i, a')) : i < names.length := by
  unfold ConRon.Arena.memberIdxAt? at h
  split at h
  · simp only [StateT.run_bind] at h
    cases hv : (viewConst e).run a with
    | error x => rw [hv] at h; cases h
    | ok p =>
      obtain ⟨x, a1⟩ := p
      rw [hv] at h
      rcases x with _ | ⟨nn, us⟩
      · revert h; simp [StateT.run, failDanglingE, bind, Except.bind]
        intro h; revert h; unfold fail
        simp [throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind]
      · revert h; simp only [except_ok_bind]
        split
        · simp [StateT.run, pure, StateT.pure, Except.pure]
          intro h _; rw [List.findIdx?_eq_some_iff_getElem] at h; exact h.1
        · simp [StateT.run, pure, StateT.pure, Except.pure]
  · revert h; simp [StateT.run, pure, StateT.pure, Except.pure]

/-- **`ctor_member`'s model refines `ctorMember?`**: the constructor `[cv, nF]` decoded below the
tops at `c`, the member names a handle slice below the top. -/
theorem ctmW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) {m : Mem}
    {a : AState} {no nl lvls nP c : Word} {cv : IConstantVal} {nF : Nat} {names : List NIdx}
    (hS : StageR dn vis fe m a) (hc : DecB (fun m => decCN m c.toNat) m (cv, nF))
    (hnm : DecB (fun m => decHL m no.toNat nl.toNat) m names) (hnb : no.toNat + nl.toNat ≤ iwTop m)
    (hlv : H lvls) :
    Sim (ctmW (n + 1) m no nl lvls nP c) (ConRon.Arena.ctorMember? names (decI lvls) nP.toNat (cv, nF)) a
      (fun r o m' a' => MemIdxOut r o ∧ (∀ i, o = some i → i < names.length) ∧
        StageR dn vis fe m' a' ∧ IWGrow m m') := by
  obtain ⟨⟨cvp, hcvp, hcv⟩, hnF⟩ := decCN_some (show decCN (truncM m) c.toNat = some (cv, nF) from hc)
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hcw, -, -⟩ := partsIwRd hcvp rfl
  have hc1lt := partsIwLt hnF
  have hc1 : (c + 1).toNat = c.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨hnFw, hnFb, -⟩ := partsIwRd hnF hc1
  have hcvp64 : (UInt64.ofNat cvp).toNat = cvp := by
    have := (partsIwRd hcvp rfl).2.1; exact UInt64.toNat_ofNat_of_lt' this
  obtain ⟨htyl, htye⟩ := partsCVType hcv hcvp64
  intro r m' hmo
  rw [ctmW.eq_2] at hmo
  rw [hcw, hnFw] at hmo
  split at hmo
  · cases hmo
  rename_i hov
  have hk : (nP + UInt64.ofNat nF).toNat = nP.toNat + nF := by
    rw [partsAddNoOv hov, UInt64.toNat_ofNat_of_lt' hnFb]
  revert r m'
  show Sim _ _ a _
  have h1 := partsSimW (stripF_pis_ok dn vis fe (nP + UInt64.ofNat nF)
    (rdW (m.arr64 EREC) (UInt64.ofNat cvp + 3)) htyl) hS
  rw [hk, htye] at h1
  refine Sim.bindK (body := fun r m1 => if r.headD 0 = 0 then some ([0, 0], m1)
      else ctmW.k_get_app_fn_f n no nl lvls (gafF m1 [CWF, r.tail.tail.tail.headD 0]))
    rfl (fun _ _ => rfl) h1 ?_
  rintro r1 x1 m1 a1 ⟨hS1, hg1, hd1⟩
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hd1
    simp only [h0, ite_true]
    exact Sim.ret ⟨rfl, by simp, hS1, hg1⟩
  | some q =>
    obtain ⟨l1, e1⟩ := q
    obtain ⟨h1', -, hbl, hbe⟩ := hd1
    rw [partsDrop3] at hbl hbe
    simp only [h1', show (1 : Word) ≠ 0 by decide, ite_false]
    have h2 := partsSimW (gafF_ok dn vis fe CWF _ hbl) hS1
    rw [CWF_eq, hbe] at h2
    show Sim (ctmW.k_get_app_fn_f n no nl lvls _) (getAppFn coreWalkFuel e1 >>= fun hd =>
      ConRon.Arena.memberIdxAt? names (decI lvls) hd) a1 _
    refine Sim.bindK (K := ctmW.k_get_app_fn_f n no nl lvls) (g := fun hd =>
      ConRon.Arena.memberIdxAt? names (decI lvls) hd)
      (body := fun r m2 => ctmW.k_member_idx_at (memWk n m2 no nl lvls (r.headD 0))) rfl (fun _ _ => rfl) h2 ?_
    rintro r2 x2 m2 a2 ⟨hS2, hg2, hl2, he2⟩
    have hnames2 : decHL m2 no.toNat nl.toNat = some names :=
      hnm.stab (OMono.decHL _ _) m2 (hg1.trans hg2)
    have hb : no.toNat + nl.toNat < 2 ^ 64 := by omega
    obtain ⟨ws, hws, hnm', hwlt⟩ := slR_of_decHL m2 nl.toNat no.toNat names hnames2 hb
    rw [ofNat_toNat_word, ofNat_toNat_word] at hws
    have hlen : ws.length < 2 ^ 64 := by
      have := decHL_length m2 hnames2; rw [hnm'] at this; simp at this; omega
    refine Sim.congr (op := ConRon.Arena.memberIdxAt? names (decI lvls) x2 >>= pure) ?_ (bind_pure _)
    refine Sim.bindK (body := fun r m3 => some ([r.headD 0, r.tail.headD 0], m3)) rfl (fun _ _ => rfl)
      (Q := fun r o m3 a3 => m3 = m2 ∧ a3 = a2 ∧ MemIdxOut r o ∧ (∀ i, o = some i → i < names.length))
      ?_ ?_
    · intro r3 m3 e3
      cases n with
      | zero => cases e3
      | succ n =>
      obtain ⟨hm3, o, hrun, hout⟩ := memW_ok n m2 m3 a2 no nl lvls (r2.headD 0) r3 ws hS2.1.arena.1 hl2
        hlv hws hwlt hlen e3
      have hrun' : (ConRon.Arena.memberIdxAt? names (decI lvls) x2).run a2 = .ok (o, a2) := by
        rw [hnm', ← he2]; exact hrun
      refine ⟨o, a2, hrun', hm3, rfl, hout, fun i hi => ?_⟩
      subst hi; exact partsMemberIdx_lt hrun'
    · rintro r3 o m3 a3 ⟨rfl, rfl, hout, hlt⟩
      refine Sim.ret ⟨?_, hlt, hS2, hg1.trans hg2⟩
      cases o <;> simp only [MemIdxOut] at hout ⊢ <;> subst hout <;> rfl

/-! ## `block_groups_one`: the `filterM` -/

theorem partsFilterAuxM {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} (p : α → m Bool) :
    ∀ (l acc : List α), List.filterAuxM p l acc = (fun r => r ++ acc) <$> List.filterAuxM p l []
  | [], acc => by simp [List.filterAuxM]
  | x :: l, acc => by
    simp only [List.filterAuxM, map_bind]
    congr 1; funext b
    rw [partsFilterAuxM p l, partsFilterAuxM p l (cond b [x] []), Functor.map_map]
    cases b <;> simp

theorem partsFilterM_cons {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} (p : α → m Bool)
    (a : α) (l : List α) :
    List.filterM p (a :: l) = (do
      let b ← p a
      let r ← List.filterM p l
      pure (if b then a :: r else r)) := by
  simp only [List.filterM, List.filterAuxM, bind_assoc]
  congr 1; funext b
  rw [partsFilterAuxM p l, bind_map_left]
  congr 1; funext r
  cases b <;> simp

theorem bgoK3_some (m2 : Mem) (r2 : List Word) : bgoK3 (some (r2, m2)) =
    some ([r2.headD 0, r2.tail.headD 0], m2) := rfl
attribute [ind_grind] bgoK3_some

/-- **`block_groups_one` is its model `bgoW`** (generated). -/
l_model bgo_spec (p : Prog) (hP : IndPartsProg p) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hm : p.lookup "member_idx_at" = some memberIdxAt)
    (hc : p.lookup "ctor_member" = some ctorMember)
    (hp : p.lookup "block_groups_one" = some blockGroupsOne)
  fns [hp ↦ bgoW]
  specs [ctorMember_specK p hv hf hm hc hP.strip hP.ad n, slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [ind_grind] finish [rdW_eq] gen 20

/-- `blockGroups`' filter predicate for member `mm`. -/
def bgPred (names : List NIdx) (lvls : LsIdx) (nP mm : Nat) (c : IConstantVal × Nat) : AM Bool := do
  match ← ConRon.Arena.ctorMember? names lvls nP c with
  | some t => pure (t == mm)
  | none => pure false

/-- `ctorMember?`'s answer compared with member `mm`. -/
def optEq (o : Option Nat) (mm : Nat) : Bool := match o with
  | some t => t == mm
  | none => false

theorem partsFilter_step (names : List NIdx) (lvls : LsIdx) (nP mm : Nat) (c0 : IConstantVal × Nat)
    (cs : List (IConstantVal × Nat)) :
    (c0 :: cs).filterM (bgPred names lvls nP mm) =
      ConRon.Arena.ctorMember? names lvls nP c0 >>= fun x =>
        cs.filterM (bgPred names lvls nP mm) >>= fun r =>
          pure (if optEq x mm then c0 :: r else r) := by
  rw [partsFilterM_cons]; simp only [bgPred, bind_assoc]
  congr 1; funext x; cases x <;> simp [optEq]

/-- **`block_groups_one`'s model refines the twin's `filterM`** (one member's group). -/
theorem bgoW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {no nl lvls nP mm : Word}
    {names : List NIdx} (hlv : H lvls) (n : Nat) :
    ∀ (m : Mem) (a : AState) (co cl : Word) (cs : List (IConstantVal × Nat)),
    StageR dn vis fe m a → PSlR decCN cs co cl m →
    DecB (fun m => decHL m no.toNat nl.toNat) m names → no.toNat + nl.toNat ≤ iwTop m →
    Sim (bgoW n m no nl lvls nP co cl mm) (cs.filterM (bgPred names (decI lvls) nP.toNat mm.toNat)) a
      (fun r gs m' a' => PSlR decCN gs (r.headD 0) (r.tail.headD 0) m' ∧ StageR dn vis fe m' a' ∧
        IWGrow m m') := by
  induction n with
  | zero => intro m a co cl cs _ _ _ _ r m' e; rw [bgoW.eq_1] at e; cases e
  | succ n ih =>
    intro m a co cl cs hS hcs hnm hnb
    by_cases hl : cl = 0
    · rw [bgoW.arm1 n m no nl lvls nP co cl mm hl]
      have : cs = [] := by
        have := decPL_length _ hcs.1; rw [hl] at this; simpa using this
      subst this
      exact Sim.ret ⟨PSlR.nil _ _, hS, IWGrow.refl _⟩
    obtain ⟨L, hL⟩ : ∃ L, cl.toNat = L + 1 :=
      ⟨cl.toNat - 1, by have : cl.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
    have hd : decPL (truncM m) (decCN (truncM m)) co.toNat (L + 1) = some cs := by
      have := hcs.1; rw [hL] at this; exact this
    obtain ⟨pc, c0, cs', rfl, hpc, hc0, hcs'⟩ := decPL_cons hd
    obtain ⟨hcw, hpcb, hcolt⟩ := partsIwRd hpc rfl
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    have hco1 : (co + 1).toNat = co.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hcl1 : (cl - 1).toNat = L := partsPred_of hL
    have hpcw : (UInt64.ofNat pc).toNat = pc := UInt64.toNat_ofNat_of_lt' hpcb
    have hc0B : DecB (fun m => decCN m (UInt64.ofNat pc).toNat) m c0 := by rw [hpcw]; exact hc0
    have hrest : PSlR decCN cs' (co + 1) (cl - 1) m :=
      ⟨by show decPL _ _ _ _ = _; rw [hco1, hcl1]; exact hcs', by rw [hco1, hcl1]; have := hcs.2; omega⟩
    rw [bgoW.arm2 n m no nl lvls nP co cl mm hl, hcw, partsFilter_step]
    have hnlen : names.length < 2 ^ 64 := by
      have := decHL_length _ (show decHL (truncM m) no.toNat nl.toNat = some names from hnm); omega
    refine Sim.bindK (bgoW.k_ctor_member.none ..) (fun _ _ => bgoW.k_ctor_member.arm1 ..) (Q := fun r o m' a' => MemIdxOut r o ∧ (∀ i, o = some i → i < names.length) ∧
        StageR dn vis fe m' a' ∧ IWGrow m m') ?_ ?_
    · cases n with
      | zero => exact Sim.of_none
      | succ n => exact ctmW_sim n hS hc0B hnm hnb hlv
    rintro r1 o m1 a1 ⟨hout, hlt, hS1, hg1⟩
    refine Sim.bindK (bgoW.k_block_groups_one.none ..) (fun _ _ => rfl)
      (ih m1 a1 (co + 1) (cl - 1) cs' hS1 (hrest.grow decCN_mono hg1) (hnm.grow (OMono.decHL _ _) hg1)
        (Nat.le_trans hnb hg1.1)) ?_
    rintro r2 gs m2 a2 ⟨hgs, hS2, hg2⟩
    have hcond : (r1.headD 0 ≠ 0 ∧ r1.tail.headD 0 = mm) ↔
        (optEq o mm.toNat = true) := by
      cases o with
      | none => simp only [MemIdxOut] at hout; subst hout; simp [optEq]
      | some i =>
        simp only [MemIdxOut] at hout; subst hout
        have hi := hlt i rfl
        have hi' : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
        simp only [List.headD_cons, List.tail_cons, beq_iff_eq, optEq]
        constructor
        · rintro ⟨-, rfl⟩; exact hi'.symm
        · intro e; exact ⟨by decide, by rw [e, ofNat_toNat_word]⟩
    by_cases hc : r1.headD 0 ≠ 0 ∧ r1.tail.headD 0 = mm
    · rw [bgoW.k_block_groups_one.arm1 (hc1 := hc), ite_eq_left (hcond.mp hc)]
      intro r m' e
      rcases h3 : consW n m2 (UInt64.ofNat pc) (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩ <;> rw [h3] at e
      · cases e
      rw [bgoW.k_sl_cons.arm1, bgoW.j1.arm1] at e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
      obtain ⟨hS3, hg3, hd3, ht3⟩ := partsConsPL decCN_mono h3 hS2 hgs.2 hgs.1
        (hc0B.grow (decCN_mono _) (hg1.trans hg2))
      exact ⟨c0 :: gs, a2, rfl, ⟨hd3, Nat.le_of_eq ht3⟩, hS3, (hg1.trans hg2).trans hg3⟩
    · have hb : optEq o mm.toNat = false := by simpa using (mt hcond.mpr hc)
      rw [bgoW.k_block_groups_one.arm2 (hc1 := hc), bgoW.j1.arm1, ite_eq_right (by rw [hb]; decide)]
      exact Sim.ret ⟨hgs, hS2, hg1.trans hg2⟩

/-! ## `block_groups_go`, `block_groups` -/

/-- A group header `[off, len]` of a constructor slice. -/
def decGH (m : Mem) (p : Nat) : Option (List (IConstantVal × Nat)) := decAt m (decPL m (decCN m)) p

theorem decGH_mono (p : Nat) : OMono (fun m => decGH m p) :=
  OMono.decAt (fun o l => OMono.decPL decCN_mono o l) p

/-- A cons onto a slice, then the slice (the shared tail of the hand `IndParts` models). -/
def bggK3 (n : Nat) (h0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => bgoK3 (consW n m3 h0 (r3.headD 0) (r3.tail.headD 0))

theorem bggK3_some (n : Nat) (m2 : Mem) (h0 : Word) (r1 : List Word) : bggK3 n h0 (some (r1, m2)) =
    bgoK3 (consW n m2 h0 (r1.headD 0) (r1.tail.headD 0)) := by simp [bggK3]
attribute [ind_grind] bggK3_some

/-- **`block_groups_go` is its model `bggW`** (generated). -/
l_model bgg_spec (p : Prog) (hP : IndPartsProg p) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hm : p.lookup "member_idx_at" = some memberIdxAt)
    (hc : p.lookup "ctor_member" = some ctorMember)
    (ho : p.lookup "block_groups_one" = some blockGroupsOne) (h2 : p.lookup "rec2" = some rec2)
    (hp : p.lookup "block_groups_go" = some blockGroupsGo)
  fns [hp ↦ bggW]
  specs [bgo_spec p hP hv hf hm hc ho n, posRec2_specW p hP.alloc h2 n,
    slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [ind_grind] finish [rdW_eq] gen 20

/-- A fresh group header over a constructor slice decoded below the tops. -/
theorem partsGH {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {g0 g1 h0 : Word} {gs : List (IConstantVal × Nat)}
    (h : posRecW m [g0, g1] = some (h0, m')) (hS : StageR dn vis fe m a) (hg : PSlR decCN gs g0 g1 m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ DecB (fun m => decGH m h0.toNat) m' gs := by
  obtain ⟨hS', hgr, -, -, hget⟩ := partsFresh h hS (by simp)
  refine ⟨hS', hgr, ?_⟩
  have e0 := hget 0 (by simp); have e1 := hget 1 (by simp)
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1
  have hd := (hg.grow decCN_mono hgr).1
  show decAt (truncM m') (decPL (truncM m') (decCN (truncM m'))) h0.toNat = some gs
  simp only [decAt, e0, e1, Option.bind_some, bind]
  exact hd

/-- **`block_groups_go`'s model refines the twin's `mapM` over members `mm, …, k - 1`.** -/
theorem bggW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {no nl lvls nP co cl k : Word}
    {names : List NIdx} {cs : List (IConstantVal × Nat)} (hlv : H lvls) (n : Nat) :
    ∀ (m : Mem) (a : AState) (mm : Word),
    StageR dn vis fe m a → PSlR decCN cs co cl m →
    DecB (fun m => decHL m no.toNat nl.toNat) m names → no.toNat + nl.toNat ≤ iwTop m →
    Sim (bggW n m no nl lvls nP co cl mm k)
      ((List.range' mm.toNat (k.toNat - mm.toNat)).mapM
        (fun j => cs.filterM (bgPred names (decI lvls) nP.toNat j))) a
      (fun r gss m' a' => PSlR decGH gss (r.headD 0) (r.tail.headD 0) m' ∧ StageR dn vis fe m' a' ∧
        IWGrow m m') := by
  induction n with
  | zero => intro m a mm _ _ _ _ r m' e; rw [bggW.eq_1] at e; cases e
  | succ n ih =>
    intro m a mm hS hcs hnm hnb
    by_cases hk : k ≤ mm
    · rw [bggW.arm1 n m no nl lvls nP co cl mm k hk]
      have : k.toNat - mm.toNat = 0 := by rw [UInt64.le_iff_toNat_le] at hk; omega
      rw [this]
      exact Sim.ret ⟨PSlR.nil _ _, hS, IWGrow.refl _⟩
    rw [bggW.arm2 n m no nl lvls nP co cl mm k hk]
    have hlt : mm.toNat < k.toNat := by rw [UInt64.le_iff_toNat_le] at hk; omega
    obtain ⟨L, hL⟩ : ∃ L, k.toNat - mm.toNat = L + 1 := ⟨k.toNat - mm.toNat - 1, by omega⟩
    have hmm1 : (mm + 1).toNat = mm.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; have := k.toNat_lt; omega
    rw [hL, List.range'_succ, List.mapM_cons]
    refine Sim.bindK (bggW.k_block_groups_one.none ..) (fun _ _ => bggW.k_block_groups_one.arm1 ..) (bgoW_sim hlv n m a co cl cs hS hcs hnm hnb) ?_
    rintro r1 gs m1 a1 ⟨hgs, hS1, hg1⟩
    intro r m' e
    rcases h2 : posRecW m1 [r1.headD 0, r1.tail.headD 0] with _ | ⟨h0, m2⟩ <;> rw [h2] at e
    · rw [bggW.k_rec2.none] at e; cases e
    rw [bggW.k_rec2.arm1] at e
    obtain ⟨hS2, hg2, hdh⟩ := partsGH h2 hS1 hgs
    have hg02 := hg1.trans hg2
    have hrec := ih m2 a1 (mm + 1) hS2 (hcs.grow decCN_mono hg02) (hnm.grow (OMono.decHL _ _) hg02)
      (Nat.le_trans hnb hg02.1)
    rw [hmm1, show k.toNat - (mm.toNat + 1) = L by omega, show mm.toNat + 1 = mm.toNat + 1 from rfl] at hrec
    revert r m' e
    refine Sim.bindK (bggW.k_block_groups_go.none ..) (fun _ _ => bggW.k_block_groups_go.arm1 ..) hrec ?_
    rintro r3 gss m3 a3 ⟨hgss, hS3, hg3⟩
    intro r m' e
    rcases h4 : consW n m3 h0 (r3.headD 0) (r3.tail.headD 0) with _ | ⟨r4, m4⟩ <;> rw [h4] at e
    · cases e
    rw [bggW.k_sl_cons.arm1] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨hS4, hg4, hd4, ht4⟩ := partsConsPL decGH_mono h4 hS3 hgss.2 hgss.1 (hdh.grow (decGH_mono _) hg3)
    exact ⟨gs :: gss, a3, rfl, ⟨hd4, Nat.le_of_eq ht4⟩, hS4, (hg02.trans hg3).trans hg4⟩

/-- **The model of `block_groups`.** -/
def bgW (n : Nat) (m : Mem) (no nl lvls nP k co cl : Word) : Option (List Word × Mem) :=
  if k = 1 then
    (match posRecW m [co, cl] with
     | none => none
     | some (h0, m1) => bgoK3 (consW n m1 h0 0 0))
  else bgoK3 (bggW n m no nl lvls nP co cl 0 k)

theorem bg_spec (p : Prog) (hP : IndPartsProg p) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hm : p.lookup "member_idx_at" = some memberIdxAt)
    (hc : p.lookup "ctor_member" = some ctorMember)
    (ho : p.lookup "block_groups_one" = some blockGroupsOne) (h2 : p.lookup "rec2" = some rec2)
    (hg : p.lookup "block_groups_go" = some blockGroupsGo)
    (hp : p.lookup "block_groups" = some blockGroups) (n : Nat) (s₀ : St) (no nl lvls nP k co cl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_groups" [no, nl, lvls, nP, k, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ bgW n s₀.mem no nl lvls nP k co cl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockGroups]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      bgg_spec p hP hv hf hm hc ho h2 hg n, posRec2_specW p hP.alloc h2 n,
      slCons_specW p hP.alloc hP.copy hP.cons n] <;>
    finish (gen := 20) [bgW]

/-- **`block_groups`' model refines `blockGroups`.** -/
theorem bgW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {no nl lvls nP k co cl : Word}
    {names : List NIdx} {cs : List (IConstantVal × Nat)} (hlv : H lvls) (n : Nat) {m : Mem} {a : AState}
    (hS : StageR dn vis fe m a) (hcs : PSlR decCN cs co cl m)
    (hnm : DecB (fun m => decHL m no.toNat nl.toNat) m names) (hnb : no.toNat + nl.toNat ≤ iwTop m) :
    Sim (bgW n m no nl lvls nP k co cl) (ConRon.Arena.blockGroups names (decI lvls) nP.toNat k.toNat cs) a
      (fun r gss m' a' => PSlR decGH gss (r.headD 0) (r.tail.headD 0) m' ∧ StageR dn vis fe m' a' ∧
        IWGrow m m') := by
  unfold bgW ConRon.Arena.blockGroups
  by_cases hk : k = 1
  · have hk' : (k.toNat == 1) = true := by subst hk; rfl
    rw [ite_eq_left hk, ite_eq_left hk']
    intro r m' e
    rcases h1 : posRecW m [co, cl] with _ | ⟨h0, m1⟩ <;> rw [h1] at e
    · cases e
    simp only at e
    obtain ⟨hS1, hg1, hdh⟩ := partsGH h1 hS hcs
    rcases h4 : consW n m1 h0 0 0 with _ | ⟨r4, m4⟩ <;> rw [h4] at e
    · cases e
    rw [bgoK3_some] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨hS4, hg4, hd4, ht4⟩ := partsConsPL decGH_mono h4 hS1 (by simp) (PSlR.nil _ _).1 hdh
    exact ⟨[cs], a, rfl, ⟨hd4, Nat.le_of_eq ht4⟩, hS4, hg1.trans hg4⟩
  · have hk' : ¬ (k.toNat == 1) = true := by
      intro e; apply hk; apply UInt64.toNat_inj.mp; simpa using e
    rw [ite_eq_right hk, ite_eq_right hk', List.range_eq_range']
    have := bggW_sim (k := k) (mm := 0) hlv n m a hS hcs hnm hnb (nP := nP)
    simp only [UInt64.toNat_zero, Nat.sub_zero] at this
    refine Sim.congr (op := _ >>= pure) ?_ (bind_pure _)
    refine Sim.bindK rfl (fun _ _ => by rw [bgoK3]) this ?_
    rintro r gss m' a' ⟨h1, h2, h3⟩
    exact Sim.ret ⟨by simpa using h1, h2, h3⟩

/-- **`ctor_member` refines `ctorMember?`** (through the stub `get_app_fn_f`; L
aborts when `nP + nF` wraps, a capacity). -/
@[refines ConRon.Arena.ctorMember?]
theorem ctorMember_refines (p : Prog) (hP : IndPartsProg2 p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (no nl lvls nP c : Word)
    (cv : IConstantVal) (nF : Nat) (names : List NIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (hc : DecB (fun m => decCN m c.toNat) s₀.mem (cv, nF))
    (hnm : DecB (fun m => decHL m no.toNat nl.toNat) s₀.mem names)
    (hnb : no.toNat + nl.toNat ≤ iwTop s₀.mem) (hlv : H lvls) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ctor_member" [no, nl, lvls, nP, c]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.ctorMember? names (decI lvls) nP.toNat (cv, nF)) a₀ ∧
      MemIdxOut r (AM.res (ConRon.Arena.ctorMember? names (decI lvls) nP.toNat (cv, nF)) a₀) ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.ctorMember? names (decI lvls) nP.toNat (cv, nF)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ :=
  triple_post (ctorMember_specK p hP.view hP.find hP.midx hP.cmem hP.strip hP.ad (n + 1) s₀ no nl lvls nP c)
    fun _ _ ⟨hl, hm⟩ =>
      let ⟨hok, hQ⟩ := Sim.run (ctmW_sim n hS hc hnm hnb hlv) hm
      ⟨hl, hok, hQ.1, hQ.2.2.1, hQ.2.2.2⟩

/-- **`block_groups` refines `blockGroups`**: the constructors `[cv, nF]` an `IW` slice decoded
below the tops, the member names a handle slice below the top; the result a slice of group headers
`[off, len]` (`decGH`). -/
@[refines ConRon.Arena.blockGroups]
theorem blockGroups_refines (p : Prog) (hP : IndPartsProg2 p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (no nl lvls nP k co cl : Word)
    (cs : List (IConstantVal × Nat)) (names : List NIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (hcs : PSlR decCN cs co cl s₀.mem)
    (hnm : DecB (fun m => decHL m no.toNat nl.toNat) s₀.mem names)
    (hnb : no.toNat + nl.toNat ≤ iwTop s₀.mem) (hlv : H lvls) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_groups" [no, nl, lvls, nP, k, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.blockGroups names (decI lvls) nP.toNat k.toNat cs) a₀ ∧
      PSlR decGH (AM.res (ConRon.Arena.blockGroups names (decI lvls) nP.toNat k.toNat cs) a₀)
        (r.headD 0) (r.tail.headD 0) s'.mem ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.blockGroups names (decI lvls) nP.toNat k.toNat cs) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ :=
  triple_post (bg_spec p hP.toIndPartsProg hP.view hP.find hP.midx hP.cmem hP.gone hP.rec2 hP.ggo
      hP.groups n s₀ no nl lvls nP k co cl)
    fun _ _ ⟨hl, hm⟩ =>
      let ⟨hok, hQ⟩ := Sim.run (bgW_sim hlv n hS hcs hnm hnb) hm
      ⟨hl, hok, hQ⟩

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

theorem slSetEq_spec (p : Prog) (hc : p.lookup "sl_contains" = some slContains)
    (ha : p.lookup "sl_all_in" = some slAllIn) (hp : p.lookup "sl_set_eq" = some slSetEq) (n : Nat)
    (s₀ : St) (o1 l1 o2 l2 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "sl_set_eq" [o1, l1, o2, l2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ setEqW n s₀.mem o1 l1 o2 l2 = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, slSetEq]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, slAllIn_spec p hc ha n] <;>
    finish (gen := 20) [setEqW]

/-! ## `block_rec_want`, `block_rec_got` -/

mutual
/-- **The model of `block_rec_want`.** -/
def brwW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, mo, ml =>
    if ml = 0 then some ([0, 0], m)
    else brwK1 n mo ml (nrF m [rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) mo))])
/-- After `name_rec`. -/
def brwK1 (n : Nat) (mo ml : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => bggK3 n (r1.headD 0) (brwW n m1 (mo + 1) (ml - 1))
end

/-- **The model of `block_rec_got`.** -/
def brgW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, ro, rl =>
    if rl = 0 then some ([0, 0], m)
    else brgK n (rdW (m.arr64 IW) ro) (brgW n m (ro + 1) (rl - 1))
where
  /-- After the recursive call. -/
  brgK (n : Nat) (rc : Word) : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (r, m1) => bgoK3 (consW n m1 (rdW (m1.arr64 EREC) (rdW (m1.arr64 IW) rc)) (r.headD 0) (r.tail.headD 0))

section arms
variable (n : Nat) (m m1 : Mem) (mo ml ro rl rc : Word) (r1 : List Word)
theorem brwW_nil (h : ml = 0) : brwW (n + 1) m mo ml = some ([0, 0], m) := by simp [brwW, h]
theorem brwW_cons (h : ml ≠ 0) : brwW (n + 1) m mo ml = brwK1 n mo ml
    (nrF m [rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) mo))]) := by
  simp [brwW, h]
theorem brwK1_some : brwK1 n mo ml (some (r1, m1)) = bggK3 n (r1.headD 0) (brwW n m1 (mo + 1) (ml - 1)) := by
  simp [brwK1]
theorem brgW_nil (h : rl = 0) : brgW (n + 1) m ro rl = some ([0, 0], m) := by simp [brgW, h]
theorem brgW_cons (h : rl ≠ 0) : brgW (n + 1) m ro rl =
    brgW.brgK n (rdW (m.arr64 IW) ro) (brgW n m (ro + 1) (rl - 1)) := by simp [brgW, h]
theorem brgK_some : brgW.brgK n rc (some (r1, m1)) =
    bgoK3 (consW n m1 (rdW (m1.arr64 EREC) (rdW (m1.arr64 IW) rc)) (r1.headD 0) (r1.tail.headD 0)) := rfl
end arms
attribute [ind_grind] brwW_nil brwW_cons brwK1_some brgW_nil brgW_cons brgK_some

section spec
variable (p : Prog) (hP : IndPartsProg p)
include hP

theorem brw_spec (hp : p.lookup "block_rec_want" = some blockRecWant) (n : Nat) :
    ∀ (s₀ : St) (mo ml : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_rec_want" [mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ brwW n s₀.mem mo ml = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ mo ml; rw [invoke_eq _ hp]; simp only [callFn, blockRecWant]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ mo ml
    rw [invoke_eq _ hp]
    simp only [callFn, blockRecWant]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, nrF_spec p hP.nr n,
        slCons_specW p hP.alloc hP.copy hP.cons n, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem brg_spec (hp : p.lookup "block_rec_got" = some blockRecGot) (n : Nat) :
    ∀ (s₀ : St) (ro rl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_rec_got" [ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ brgW n s₀.mem ro rl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ ro rl; rw [invoke_eq _ hp]; simp only [callFn, blockRecGot]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ro rl
    rw [invoke_eq _ hp]
    simp only [callFn, blockRecGot]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        slCons_specW p hP.alloc hP.copy hP.cons n, ih] <;>
      finish (gen := 20) [rdW_eq]

end spec

/-- **`block_rec_got`'s model**: the recursors' names. -/
theorem brgW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (ro rl : Word) (recs : List RecShape) (r : List Word),
    brgW n m ro rl = some (r, m') → StageR dn vis fe m a → PSlR decRS recs ro rl m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (recs.map (·.cvR.name)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  induction n with
  | zero => intro m m' a ro rl recs r h; simp [brgW] at h
  | succ n ih =>
    intro m m' a ro rl recs r h hS hrs
    by_cases hl : rl = 0
    · rw [brgW_nil n m ro rl hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl; rw [partsPSl_nil hrs]
      exact ⟨hS, IWGrow.refl _, by simp [decHL, hslice?], by simp⟩
    rw [brgW_cons n m ro rl hl] at h
    obtain ⟨pc, rs0, rs', rfl, hw, hpb, hrs0, hrs'⟩ := partsPSl_cons hrs hl
    rw [hw] at h
    obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (by simp [brgW.brgK])
    rw [brgK_some] at h
    obtain ⟨hS1, hg1, hd1, hb1⟩ := ih m m1 a (ro + 1) (rl - 1) rs' r1 h1 hS hrs'
    obtain ⟨⟨ca, hca, hcv⟩, -⟩ := decRS_some (show decRS (truncM m) pc = some rs0 from hrs0)
    obtain ⟨hcw, hcab, -⟩ := partsIwRd hca (UInt64.toNat_ofNat_of_lt' hpb)
    have hpclt : pc < iwTop m := partsIwLt hca
    rw [partsRdIW_grow hg1 (by rw [UInt64.toNat_ofNat_of_lt' hpb]; exact hpclt), hcw] at h
    obtain ⟨hnl, hne⟩ := partsCVName hg1 (show DecB (fun m => decCVp m ca) m rs0.cvR from hcv) hcab
    rcases h2 : consW n m1 (rdW (m1.arr64 EREC) (UInt64.ofNat ca)) (r1.headD 0) (r1.tail.headD 0) with _ | ⟨r2, m2⟩ <;> rw [h2] at h
    · cases h
    rw [bgoK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hS2, hg2, hd2, ht2⟩ := consW_stage h2 hS1 hb1 hnl hd1
    refine ⟨hS2, hg1.trans hg2, ?_, by simp only [List.headD_cons, List.tail_cons]; omega⟩
    simp only [List.headD_cons, List.tail_cons, List.map_cons]
    rw [← hne]; exact hd2

/-- **`block_rec_want`'s model refines the twin's `mapM` of `name_rec`.** -/
theorem brwW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m : Mem) (a : AState) (mo ml : Word) (ms : List MemberShape),
    StageR dn vis fe m a →
    DecB (fun m => decPL m (decMS m) mo.toNat ml.toNat) m ms ∧ (ml = 0 ∨ mo.toNat + ml.toNat ≤ iwTop m) →
    Sim (brwW n m mo ml) (ms.mapM fun ms => internNNode (.str ms.cvT.name "rec")) a
      (fun r xs m' a' => decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  induction n with
  | zero => intro m a mo ml ms _ _ r m' e; simp [brwW] at e
  | succ n ih =>
    intro m a mo ml ms hS hms
    by_cases hl : ml = 0
    · rw [brwW_nil n m mo ml hl]
      have : ms = [] := by
        have := decPL_length _ (show decPL _ _ _ _ = _ from hms.1); subst hl; simpa using this
      subst this
      exact Sim.ret ⟨by simp [decHL, hslice?], by simp, hS, IWGrow.refl _⟩
    rw [brwW_cons n m mo ml hl]
    obtain ⟨pc, ms0, ms', rfl, hw, hpb, hms0, hms'⟩ := partsPSl_cons ⟨hms.1, hms.2.resolve_left hl⟩ hl
    obtain ⟨⟨ca, hca, hcv⟩, -⟩ := decMS_some (show decMS (truncM m) pc = some ms0 from hms0)
    obtain ⟨hcw, hcab, -⟩ := partsIwRd hca (UInt64.toNat_ofNat_of_lt' hpb)
    rw [hw, hcw]
    obtain ⟨hnl, hne⟩ := partsCVName (IWGrow.refl m) (show DecB (fun m => decCVp m ca) m ms0.cvT from hcv) hcab
    rw [List.mapM_cons]
    have h1 := partsSimW (nrF_ok dn vis fe _ hnl) hS
    rw [hne] at h1
    refine Sim.bindK (by simp [brwK1]) (fun _ _ => by rw [brwK1]) h1 ?_
    rintro r1 x1 m1 a1 ⟨hS1, hg1, hx1l, hx1⟩
    refine Sim.bindK (by simp [bggK3]) (fun _ _ => by rw [bggK3]) (ih m1 a1 (mo + 1) (ml - 1) ms' hS1 ⟨(hms'.grow decMS_mono hg1).1, Or.inr (hms'.grow decMS_mono hg1).2⟩) ?_
    rintro r2 xs m2 a2 ⟨hd2, hb2, hS2, hg2⟩
    intro r m' e
    rcases h3 : consW n m2 (r1.headD 0) (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩ <;> rw [h3] at e
    · cases e
    rw [bgoK3_some] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage h3 hS2 hb2 hx1l hd2
    refine ⟨x1 :: xs, a2, rfl, ?_, by simp only [List.headD_cons, List.tail_cons]; omega, hS3,
      (hg1.trans hg2).trans hg3⟩
    simp only [List.headD_cons, List.tail_cons]; rw [← hx1]; exact hd3

theorem partsAll_decI (ws vs : List Word) (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hvs : ∀ w ∈ vs, w.toNat < 2 ^ 32) :
    (ws.map (decI : Word → NIdx)).all (fun n => (vs.map (decI : Word → NIdx)).contains n) =
      ws.all (fun w => vs.contains w) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.all_cons]
    rw [ih (fun w' h' => hws w' (List.mem_cons_of_mem _ h')),
      partsContains_decI vs w hvs (hws w (List.mem_cons_self ..))]

/-- **The model of `block_rec_name_set_ok`** (at exec fuel `n + 2`). -/
def brnW (n : Nat) (m : Mem) (mo ml ro rl : Word) : Option (List Word × Mem) :=
  match brwW (n + 1) m mo ml with
  | none => none
  | some (r1, m1) =>
    match brgW (n + 1) m1 ro rl with
    | none => none
    | some (r2, m2) =>
      match setEqW n m2 (r2.headD 0) (r2.tail.headD 0) (r1.headD 0) (r1.tail.headD 0) with
      | none => none
      | some b => some ([b], m2)

theorem brn_spec (p : Prog) (hP : IndPartsProg p) (hw : p.lookup "block_rec_want" = some blockRecWant)
    (hg : p.lookup "block_rec_got" = some blockRecGot) (hc : p.lookup "sl_contains" = some slContains)
    (ha : p.lookup "sl_all_in" = some slAllIn) (hs : p.lookup "sl_set_eq" = some slSetEq)
    (hp : p.lookup "block_rec_name_set_ok" = some blockRecNameSetOk) (n : Nat) (s₀ : St)
    (mo ml ro rl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "block_rec_name_set_ok" [mo, ml, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ brnW n s₀.mem mo ml ro rl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockRecNameSetOk]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, brw_spec p hP hw (n + 1),
      brg_spec p hP hg (n + 1), slSetEq_spec p hc ha hs n] <;>
    finish (gen := 20) [brnW]

/-- **`block_rec_name_set_ok` refines `blockRecNameSetOk`** (through the stub `name_rec`): the
members and recursors slices of records decoded below the tops (the members' below the top unless
empty: an empty slice's offset is whatever its record holds). -/
@[refines ConRon.Arena.blockRecNameSetOk]
theorem blockRecNameSetOk_refines (p : Prog) (hP : IndPartsProg3 p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mo ml ro rl : Word)
    (ms : List MemberShape) (recs : List RecShape) (hS : StageR dn vis fe s₀.mem a₀)
    (hms : DecB (fun m => decPL m (decMS m) mo.toNat ml.toNat) s₀.mem ms ∧
      (ml = 0 ∨ mo.toNat + ml.toNat ≤ iwTop s₀.mem))
    (hrs : PSlR decRS recs ro rl s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "block_rec_name_set_ok" [mo, ml, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.blockRecNameSetOk ms recs) a₀ ∧
      r = [if AM.res (ConRon.Arena.blockRecNameSetOk ms recs) a₀ then 1 else 0] ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.blockRecNameSetOk ms recs) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (brn_spec p hP.toIndPartsProg hP.want hP.got hP.contains hP.allIn hP.setEq hP.nameSet
    n s₀ mo ml ro rl) ?_
  rintro r s' ⟨hl, hm⟩
  have hsim : Sim (brnW n s₀.mem mo ml ro rl) (ConRon.Arena.blockRecNameSetOk ms recs) a₀
      (fun r b m' a' => r = [if b then 1 else 0] ∧ StageR dn vis fe m' a' ∧ IWGrow s₀.mem m') := by
    unfold brnW ConRon.Arena.blockRecNameSetOk
    refine Sim.bindK (K := fun x => match x with
      | none => none
      | some (r1, m1) =>
        match brgW (n + 1) m1 ro rl with
        | none => none
        | some (r2, m2) =>
          match setEqW n m2 (r2.headD 0) (r2.tail.headD 0) (r1.headD 0) (r1.tail.headD 0) with
          | none => none
          | some b => some ([b], m2))
      (body := fun r1 m1 => match brgW (n + 1) m1 ro rl with
        | none => none
        | some (r2, m2) =>
          match setEqW n m2 (r2.headD 0) (r2.tail.headD 0) (r1.headD 0) (r1.tail.headD 0) with
          | none => none
          | some b => some ([b], m2)) rfl (fun _ _ => rfl) (brwW_sim (n + 1) _ a₀ mo ml ms hS hms) ?_
    rintro r1 want m1 a1 ⟨hd1, hb1, hS1, hg1⟩
    intro r m' e
    rcases h2 : brgW (n + 1) m1 ro rl with _ | ⟨r2, m2⟩ <;> rw [h2] at e
    · cases e
    simp only at e
    obtain ⟨hS2, hg2, hd2, hb2⟩ := brgW_ok (n + 1) m1 m2 a1 ro rl recs r2 h2 hS1 (hrs.grow decRS_mono hg1)
    rcases h3 : setEqW n m2 (r2.headD 0) (r2.tail.headD 0) (r1.headD 0) (r1.tail.headD 0) with _ | b <;> rw [h3] at e
    · cases e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    have hT : iwTop m2 < 2 ^ 64 := (rdW (m2.arr64 CTL) 200).toNat_lt
    have hd1' : decHL m2 (r1.headD 0).toNat (r1.tail.headD 0).toNat = some want := by
      rw [decHL_grow3 hg2 hb1]; exact hd1
    obtain ⟨gws, hgs, hgm, hgl⟩ := slR_of_decHL m2 _ _ _ hd2 (by omega)
    obtain ⟨wws, hws, hwm, hwl⟩ := slR_of_decHL m2 _ _ _ hd1' (by have := hg2.1; omega)
    rw [ofNat_toNat_word, ofNat_toNat_word] at hgs hws
    have hb := setEqW_ok hgs hws h3
    refine ⟨_, a1, rfl, ?_, hS2, hg1.trans hg2⟩
    rw [hb, hgm, hwm, partsAll_decI wws gws hwl hgl, partsAll_decI gws wws hgl hwl]
    simp only [List.length_map]
  obtain ⟨hok, hr, hS', hg⟩ := Sim.run hsim hm
  exact ⟨hl, hok, hr, hS', hg⟩

end L.Ind

end

end
