import ConAgua.Arena.IndPartsSpec8

/-!
# Refinements of `IndParts`, part 9 (lane `indproofs2`, helper `parts`): the groups

`ctorMember?`, `blockGroups` (with `block_groups_one`, the `filterM`, and `block_groups_go`, the
`mapM` over the members, both recursive). The relational lemmas compose the callees with `Sim`
(`IndSim.lean`); a stub's `RelAM` fact is a `Sim` (`partsSimStub`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A real callee's word-model fact (`RelW`) as a `Sim`. -/
theorem partsSimW {α : Type} {W : Mem → List Word → Option (List Word × Mem)} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    (h : RelW W args pre op post) {m : Mem} {a : AState} (hpre : pre m a) :
    Sim (W m args) op a (fun r x m' a' => post m m' a' r x) :=
  fun r m' e => h m m' a r e hpre

/-! ## `ctor_member` -/

/-- `member_idx_at`'s model at every exec fuel. -/
def memWk : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, no, nl, lvls, e => memW n m no nl lvls e

theorem memberIdxAt_specK (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hp : p.lookup "member_idx_at" = some memberIdxAt)
    (n : Nat) (s₀ : St) (no nl lvls e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "member_idx_at" [no, nl, lvls, e]
    ⦃fun r s' => LocEq s' s₀ ∧ memWk n s₀.mem no nl lvls e = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => rw [invoke_eq _ hp]; simp only [callFn, memberIdxAt]; vcgen [exec] <;> grind
  | succ n => exact memberIdxAt_spec p hv hf hp n s₀ no nl lvls e

/-- **`ctor_member` is its model `ctmW`** (generated). -/
l_model ctorMember_specK (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hm : p.lookup "member_idx_at" = some memberIdxAt)
    (hp : p.lookup "ctor_member" = some ctorMember) (hst : StripProg p) (had : AdF p)
  fns [hp ↦ ctmW list]
  specs [stripPis_specF p hst n, gafF_spec p had n, memberIdxAt_specK p hv hf hm n]
  grind [ind_grind] finish [rdW_eq] gen 20

/-! ## Reading decoded records' words -/

/-- A number of the pool decoded below the top: the word L reads there, below the top. -/
theorem partsIwRd {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) {w : Word} (hw : w.toNat = i) :
    rdW (m.arr64 IW) w = UInt64.ofNat v ∧ v < 2 ^ 64 ∧ i < iwTop m := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨hi, hx'⟩ := truncM_iw_get hx
  simp only [iwA] at hx'
  refine ⟨?_, x.toNat_lt, hi⟩
  rw [rdW_of_get? hw.symm hx']; simp

theorem partsIwLt {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) : i < iwTop m := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, -⟩ := h
  exact (truncM_iw_get hx).1

/-- The type handle of a constant decoded below the top. -/
theorem partsCVType {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp (truncM m) q = some cv)
    {w : Word} (hw : w.toNat = q) :
    (rdW (m.arr64 EREC) (w + 3)).toNat < 2 ^ 32 ∧ decI (rdW (m.arr64 EREC) (w + 3)) = cv.type := by
  obtain ⟨x, hx, hxl, hxe⟩ := hd?_some (decCV_type h)
  obtain ⟨hi, hx'⟩ := truncM_er_get hx
  simp only [erA] at hx'
  have hE : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt
  have hw3 : (w + 3).toNat = q + 3 := by rw [UInt64.toNat_add]; simp; omega
  rw [rdW_of_get? hw3.symm hx']
  exact ⟨hxl, hxe.symm⟩

/-- A word sum that does not wrap. -/
theorem partsAddNoOv {a b : Word} (h : ¬ a + b < a) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
  have := b.toNat_lt; have := a.toNat_lt
  rw [UInt64.toNat_add]; omega

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

/-- After `sl_cons`: the slice (the shared tail of the hand `IndParts` models). -/
def bgoK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

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

/-! ## The census theorems -/

/-- The program bundle of the groups. -/
structure IndPartsProg2 (p : Prog) : Prop extends IndPartsProg p where
  view : p.lookup "e_view" = some eView
  find : p.lookup "sl_find" = some slFind
  midx : p.lookup "member_idx_at" = some memberIdxAt
  cmem : p.lookup "ctor_member" = some ctorMember
  rec2 : p.lookup "rec2" = some rec2
  gone : p.lookup "block_groups_one" = some blockGroupsOne
  ggo : p.lookup "block_groups_go" = some blockGroupsGo
  groups : p.lookup "block_groups" = some blockGroups

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
