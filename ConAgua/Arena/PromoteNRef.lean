import ConAgua.Arena.PromoteN
import ConAgua.Census.Attr

/-!
# `promote_n` refines `promoteN`

The relational lemma by induction on L's fuel (`pn_rel`), for `promote_n` and `pn_arm` together:
from `ArenaD`, `PMemoR` and a handle word, a run of the L function is a successful run of the
twin's (`promoteN`, its arm `pnArmT`) with the relations after, a persistent result word, the
caches and pins kept, and the frame `nArrs`/`nCtl` (the name tables, the name memo, the flag).
The twin side: `promoteN_succ` (the arm named), the scratch view of a name record
(`viewN_anon`, `viewN_str`, `viewN_num`), the bracket (`PromotePi.lean`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## The twin, with the arm named -/

/-- The twin's arm of `promoteN` after a memo miss: the view, the children, the interning. -/
def pnArmT (m : PMemo) (fuel : Nat) (h : NIdx) : AM (PMemo × NIdx) := do
  match ← viewN h with
  | .anonymous => do pure (m, ← internPersistentN .anonymous)
  | .str p s => do
    let (m, p) ← promoteN m fuel p
    pure (m, ← internPersistentN (.str p s))
  | .num p n => do
    let (m, p) ← promoteN m fuel p
    pure (m, ← internPersistentN (.num p n))

/-- The twin's `promoteN` at fuel `fuel + 1`, with the arm named. -/
def pnStepT (m : PMemo) (fuel : Nat) (h : NIdx) : AM (PMemo × NIdx) :=
  if h.isPersistent then pure (m, h)
  else match m.nM[h]? with
    | some r => pure (m, r)
    | none => do
      let (m, r) ← pnArmT m fuel h
      pure ({ m with nM := m.nM.insert h r }, r)

theorem promoteN_succ (m : PMemo) (fuel : Nat) (h : NIdx) :
    promoteN m (fuel + 1) h = pnStepT m fuel h := by
  rw [promoteN, pnStepT]
  by_cases hp : h.isPersistent
  · simp only [hp, ↓reduceIte]
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]
    cases hm : m.nM[h]? with
    | some r => rfl
    | none =>
      simp only [pnArmT, bind_assoc]
      apply bind_congr; intro v
      cases v <;> simp

/-! ## The view of a name record -/

section view
variable {m : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : h.toNat < 2 ^ 32)
  (hv : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
include hR hh hv

/-- The name store's view reads the tier the handle names. -/
theorem nview_tier :
    a.store.lss.ls.ns.view (decI h) =
      (if tierW h = 0 then a.store.lss.ls.ns.pers else a.store.lss.ls.ns.scr).get (decI h) := by
  have hfl := ConsR.flag hR.nanon
  unfold NStore.view
  rw [isPersistent_decI h hh]
  by_cases ht : tierW h = 0
  · simp only [show (h >>> 27) &&& 1 = tierW h from rfl, ht, beq_self_eq_true, ↓reduceIte]
  · have hon : a.store.lss.ls.ns.scratchOn = true := by
      rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun e => hv ⟨ht, e⟩
    simp only [show (h >>> 27) &&& 1 = tierW h from rfl, beq_iff_eq, ht, ↓reduceIte, hon]

omit hR hh hv in
theorem viewN_run {v : NNodeView} (hw : a.store.lss.ls.ns.view (decI h) = some v) :
    (viewN (decI h)).run a = .ok (v, a) := by
  simp only [viewN, EStore.ns, StateT.run_bind, StateT.run_get, pure_bind, hw]; rfl

/-- The scratch view of an `anonymous` record. -/
theorem viewN_anon (hg : h >>> 28 = 0) (hc : ¬ tcnt m NANON (tierW h) ≤ idxW h) :
    (viewN (decI h)).run a = .ok (.anonymous, a) := by
  apply viewN_run
  rw [nview_tier hR hh hv]
  have e0 : ((decI h : NIdx).tag = 0) := (decI_tag_eq h hh 0 (by decide)).mpr (by rw [hg]; rfl)
  obtain ⟨x, hx, -⟩ := ConsR.node hR.nanon (tierW h) (tierW_le h)
    (idxW h) (UInt64.not_le.mp hc)
  simp only [NTables.get, e0, NTag.anonymous, beq_self_eq_true, ↓reduceIte, Tbl.node?,
    decI_idx, apply_ite NTables.anons, hx, Option.map_some]

/-- The scratch view of a `str` record: its prefix word and a slice holding the string. -/
theorem viewN_str (hg : h >>> 28 = 1) (hc : ¬ tcnt m NSTR (tierW h) ≤ idxW h) :
    ∃ s, (viewN (decI h)).run a = .ok (.str (decI (tfld m NSTR (tierW h) (idxW h) 0)) s, a) ∧
      SliceOK m (tfld m NSTR (tierW h) (idxW h) 1) (tfld m NSTR (tierW h) (idxW h) 2) ∧
      sliceL (vpool m) (tfld m NSTR (tierW h) (idxW h) 1).toNat (tfld m NSTR (tierW h) (idxW h) 2).toNat =
        strWords s ∧ (tfld m NSTR (tierW h) (idxW h) 0).toNat < 2 ^ 32 := by
  have e1 : ((decI h : NIdx).tag = 1) := (decI_tag_eq h hh 1 (by decide)).mpr (by rw [hg]; rfl)
  obtain ⟨x, hx, hr⟩ := ConsR.node hR.nstr (tierW h) (tierW_le h)
    (idxW h) (UInt64.not_le.mp hc)
  obtain ⟨hq, hsl, hk, -⟩ := hr
  refine ⟨x.s, ?_, hsl.1, hk, by rw [hq]; exact word_lt _⟩
  apply viewN_run
  rw [nview_tier hR hh hv]
  have hne : ((1 : UInt32) == NTag.anonymous) = false := by decide
  simp only [NTables.get, e1, hne, NTag.str, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
    Tbl.node?, decI_idx, apply_ite NTables.strs, hx, Option.map_some, hq, decI_word]

/-- The scratch view of a `num` record: its prefix word and its number. -/
theorem viewN_num (hg : h >>> 28 = 2) (hc : ¬ tcnt m NNUM (tierW h) ≤ idxW h) :
    (viewN (decI h)).run a =
      .ok (.num (decI (nnQ m (tierW h) (idxW h))) (nnU m (tierW h) (idxW h)).toNat, a) ∧
      (nnQ m (tierW h) (idxW h)).toNat < 2 ^ 32 := by
  have e2 : ((decI h : NIdx).tag = 2) := (decI_tag_eq h hh 2 (by decide)).mpr (by rw [hg]; rfl)
  obtain ⟨x, hx, hr⟩ := ConsR.node hR.nnum (tierW h) (tierW_le h)
    (idxW h) (UInt64.not_le.mp hc)
  obtain ⟨hq, hu⟩ := hr
  refine ⟨?_, by rw [nnQ, hq]; exact word_lt _⟩
  apply viewN_run
  rw [nview_tier hR hh hv]
  have hne0 : ((2 : UInt32) == NTag.anonymous) = false := by decide
  have hne1 : ((2 : UInt32) == NTag.str) = false := by decide
  simp only [NTables.get, e2, hne0, hne1, NTag.num, beq_self_eq_true, Bool.false_eq_true,
    ↓reduceIte, Tbl.node?, decI_idx, apply_ite NTables.nums, hx, Option.map_some, nnQ, nnU, hq,
    hu, decI_word]

end view

/-! ## The relation -/

/-- The arrays and `CTL` words a name promotion writes. -/
abbrev nArrs : List ArrId := [POOL, PT0, NAREC, NAREC + 256, NASLOT, NASLOT + 256, NSREC, NSREC + 256, NSSLOT,
  NSSLOT + 256, NNREC, NNREC + 256, NNSLOT, NNSLOT + 256, PNM]
abbrev nCtl : List Word := [34, 35, 36, 37, 38, 39, 141]

/-- **What a successful run of a name promotion gives**: the twin's run `op` succeeds with the
memo `pm'` and the handle `decI r`, the relations hold after, `r` is a persistent handle word,
caches and pins are kept, the writes are within `nArrs`/`nCtl`, the other memos unchanged. -/
def PNOk (op : AM (PMemo × NIdx)) (m : Mem) (a : AState) (pm : PMemo) (r : Word) (m' : Mem) :
    Prop :=
  ∃ a' pm', op.run a = .ok ((pm', decI r), a') ∧ ArenaD m' a' ∧ PMemoR m' pm' ∧ PW r ∧
    cp a' = cp a ∧ MemFrame nArrs nCtl m m' ∧ pm'.eM = pm.eM ∧ pm'.lM = pm.lM ∧ pm'.lsM = pm.lsM ∧
    SlKeep m m'

theorem vp_stable (k : IdxKind) (S : MemoSch) : VStable S (VP k) := fun _ _ _ _ _ h => h

theorem pnSch_wf : pnSch.WF := ⟨by decide, by decide⟩

/-- The name memo gains an entry. -/
theorem PMemoR.setN {m m' : Mem} {pm : PMemo} (hP : PMemoR m pm) (h r : Word) (hh : h.toNat < 2 ^ 32)
    (hr : PW r) (hs : msetG pnSch m h 0 r = some m') :
    PMemoR m' { pm with nM := pm.nM.insert (decI h) (decI r) } := by
  have hf := msetG_frame pnSch pnSch_wf m m' h 0 r hs
  exact ⟨memoRV_set pnSch pnSch_wf (hKey .name) (VP .name) (vp_stable _ _) m pm.nM hP.n h 0 r
      ⟨hh, rfl⟩ (decI r) ⟨rfl, hr.1, hr.2⟩ m' hs,
    memoRV_frame plSch ⟨by decide, by decide⟩ _ _ _ _ (by decide) (by decide) m m' hf
      (fun _ _ h => h) _ hP.l,
    memoRV_frame plsSch ⟨by decide, by decide⟩ _ _ _ _ (by decide) (by decide) m m' hf
      (fun _ _ h => h) _ hP.ls,
    memoRV_frame peSch ⟨by decide, by decide⟩ _ _ _ _ (by decide) (by decide) m m' hf
      (fun _ _ h => h) _ hP.e⟩

/-- A writer of the store tier keeps the promotion memo. -/
theorem PMemoR.frameLo {A : List ArrId} {C : List Word} {m m' : Mem} {pm : PMemo}
    (hA : ∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320)) (hC : ∀ x ∈ C, x.toNat < 64) (hf : MemFrame A C m m')
    (h : PMemoR m pm) : PMemoR m' pm :=
  h.frame (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega)
    (fun x hx => .inl (Nat.lt_trans (hC x hx) (by decide))) hf

/-- A memo write keeps the arena relation. -/
theorem ArenaD.memo {m m' : Mem} {a : AState} (hD : ArenaD m a) (S : MemoSch) (hS : S.WF)
    (h1 : 64 ≤ S.arr) (h1' : S.arr < 256) (h2 : 64 ≤ (S.cs + 1).toNat) (h r : Word) (hs : msetG S m h 0 r = some m') :
    ArenaD m' a := by
  have hf := msetG_frame S hS m m' h 0 r hs
  exact ⟨ArenaR.frame_ext _ _ (by simpa using ⟨h1, h1'⟩) (by simp; exact h2) m m' hf a hD.1,
    DerR.frameM _ _ m m' hf (fun b hb => by
      rw [List.mem_singleton.mp hb]; simp only [ArrId] at h1 h1' ⊢; omega) a hD.2⟩

theorem run_bind_ok {α β : Type} {x : AM α} {f : α → AM β} {a a₁ : AState} {v : α}
    (h : x.run a = .ok (v, a₁)) : (x >>= f).run a = (f v).run a₁ := by
  simp only [StateT.run_bind, h, except_ok_bind]

theorem toNat_pred (f : Word) (hf : f ≠ 0) : f.toNat = (f - 1).toNat + 1 := by
  have : f.toNat ≠ 0 := fun h => hf (UInt64.toNat_inj.mp (by simpa using h))
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega

/-! ## `Sim` chains over the promotions -/

/-- **A promotion's existential form as a `Sim`** (the `P…Ok` predicates): the twin returns
`(pm', dec r)`, `R` relates the rest. -/
theorem Sim.ofP {α : Type} {mo : Option (List Word × Mem)} {op : AM (PMemo × α)} {dec : Word → α}
    {a : AState} {R : List Word → Mem → AState → PMemo → Prop}
    (h : ∀ r m', mo = some (r, m') → ∃ a' pm', op.run a = .ok ((pm', dec (r.headD 0)), a') ∧ R r m' a' pm') :
    Sim mo op a (fun r x m' a' => x.2 = dec (r.headD 0) ∧ R r m' a' x.1) := fun r m' e => by
  obtain ⟨a', pm', h1, h2⟩ := h r m' e; exact ⟨_, a', h1, rfl, h2⟩

/-- **The end of a chain into `PNOk`.** -/
theorem PNOk.of_sim {op : AM (PMemo × NIdx)} {m : Mem} {a : AState} {pm : PMemo}
    {mo : Option (Word × Mem)} (h : Sim mo op a fun r x m' a' => x.2 = decI r ∧ ArenaD m' a' ∧
      PMemoR m' x.1 ∧ PW r ∧ cp a' = cp a ∧ MemFrame nArrs nCtl m m' ∧ x.1.eM = pm.eM ∧
      x.1.lM = pm.lM ∧ x.1.lsM = pm.lsM ∧ SlKeep m m')
    {r : Word} {m' : Mem} (hm : mo = some (r, m')) : PNOk op m a pm r m' := by
  obtain ⟨⟨pm', y⟩, a', h1, e, h2⟩ := h r m' hm
  subst e; exact ⟨a', pm', h1, h2⟩

/-- **The model's last step `hd1` of a callee that keeps the memo**: the twin's `op` then
`pure (pm, ·)`. -/
theorem Sim.hd1 {α : Type} {mo : Option (List Word × Mem)} {op : AM α} {a : AState} {pm : PMemo}
    {Q : Word → α → Mem → AState → Prop}
    (h : Sim (L.Arena.hd1 mo) op a Q) :
    Sim (L.Arena.hd1 mo) (op >>= fun x => pure (pm, x)) a (fun r y m' a' => y.1 = pm ∧ Q r y.2 m' a') :=
  Sim.bindK (K := id) rfl (fun _ _ => rfl) h fun _ _ _ _ hQ => Sim.ret ⟨rfl, hQ⟩

/-- **A `pi_*` callee** (its spec `hs`, its relation `hrel` over `piW`) as a `Sim`. -/
theorem sim_piG {p : Prog} {α : Type} {g : FnName} {args : List Word} {n : Nat} {m : Mem}
    (W : Nat → Mem → Option (Word × Mem))
    {a : AState} {opP : AM α} {dec : Word → α} {R : Word → Mem → AState → Prop}
    (hs : ∀ n s₀, ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) g args
      ⦃fun r s' => LocEq s' s₀ ∧ W n s₀.mem = some (r.headD 0, s'.mem); ⊤⦄)
    (hrel : ∀ n r m', W n m = some (r, m') → ∃ a', opP.run a = .ok (dec r, a') ∧ R r m' a') :
    Sim (L.Arena.hd1 (callW p n g args m)) opP a (fun r x m' a' => x = dec r ∧ R r m' a') := by
  intro r m' e
  cases n with
  | zero => rw [callW_zero'] at e; cases e
  | succ n =>
  cases hc : callW p (n + 1) g args m with
  | none => rw [hc] at e; cases e
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc, hd1_some] at e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
  obtain ⟨s', hs', -, hW⟩ := callW_triple (hs n ⟨m, Locals.init []⟩) hc
  rw [hs'] at hW
  obtain ⟨a', h1, h2⟩ := hrel n _ _ hW
  exact ⟨_, a', h1, rfl, h2⟩

theorem sim_pi {p : Prog} {α : Type} {g mk : FnName} {args : List Word} {n : Nat} {m : Mem}
    {a : AState} {opP : AM α} {dec : Word → α} {R : Word → Mem → AState → Prop}
    (hs : ∀ n s₀, ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) g args
      ⦃fun r s' => LocEq s' s₀ ∧ piW p n mk args s₀.mem = some (r.headD 0, s'.mem); ⊤⦄)
    (hrel : ∀ n r m', piW p n mk args m = some (r, m') → ∃ a', opP.run a = .ok (dec r, a') ∧ R r m' a') :
    Sim (L.Arena.hd1 (callW p n g args m)) opP a (fun r x m' a' => x = dec r ∧ R r m' a') :=
  sim_piG (fun n m => piW p n mk args m) hs hrel

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`promote_n` and `pn_arm` refine `promoteN` and its arm**, at every L fuel. -/
theorem pn_rel : ∀ n : Nat,
    (∀ (m : Mem) (a : AState) (pm : PMemo) (f h : Word) (r : List Word) (m' : Mem),
      ArenaD m a → PMemoR m pm → h.toNat < 2 ^ 32 →
      callW p n "promote_n" [f, h] m = some (r, m') →
      PNOk (promoteN pm f.toNat (decI h)) m a pm (r.headD 0) m') ∧
    (∀ (m : Mem) (a : AState) (pm : PMemo) (f h : Word) (r : List Word) (m' : Mem),
      ArenaD m a → PMemoR m pm → h.toNat < 2 ^ 32 → tierW h ≠ 0 →
      callW p n "pn_arm" [f, h] m = some (r, m') →
      PNOk (pnArmT pm f.toNat (decI h)) m a pm (r.headD 0) m') := by
  intro n
  induction n with
  | zero =>
    exact ⟨fun _ _ _ _ _ _ _ _ _ _ hc => (by rw [callW_zero'] at hc; cases hc),
      fun _ _ _ _ _ _ _ _ _ _ _ hc => (by rw [callW_zero'] at hc; cases hc)⟩
  | succ n ih =>
  refine ⟨?_, ?_⟩
  · intro m a pm f h r m' hD hP hh hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (promoteN_spec p hp n ⟨m, Locals.init []⟩ f h) hc
    simp only at hW
    by_cases hf : f = 0
    · simp [pnW, hf] at hW
    rw [toNat_pred f hf, promoteN_succ]
    unfold pnStepT
    by_cases ht : tierW h = 0
    · rw [pnW_pers p n m f h hf ht] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have hpers : (decI h : NIdx).isPersistent = true := PW.pers ⟨hh, ht⟩
      rw [ite_eq_left hpers, ← hr]
      exact ⟨a, pm, rfl, hD, hP, ⟨hh, ht⟩, rfl, MemFrame.refl _ _ _, rfl, rfl, rfl, SlKeep.refl _⟩
    have hnp : (decI h : NIdx).isPersistent = false := by
      rw [isPersistent_decI h hh]; exact beq_eq_false_iff_ne.mpr ht
    rw [ite_eq_right (by simp [hnp])]
    have hk : (hKey .name).ok h 0 := ⟨hh, rfl⟩
    by_cases h0 : mfindG pnSch m h 0 = []
    · simp [pnW, hf, ht, h0] at hW
    by_cases h1 : (mfindG pnSch m h 0).headD 0 ≠ 0
    · obtain ⟨v, hv, hvr⟩ := memoRV_hit pnSch (hKey .name) (VP .name) m pm.nM hP.n h 0 h0 h1 hk
      rw [pnW_hit p n m f h hf ht h0 h1] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have hv' : pm.nM[decI h]? = some v := hv
      rw [hv']
      obtain ⟨rfl, hw1, hw2⟩ := hvr
      rw [← hr]
      exact ⟨_, pm, rfl, hD, hP, ⟨hw1, hw2⟩, rfl, MemFrame.refl _ _ _, rfl, rfl, rfl, SlKeep.refl _⟩
    have h1' : (mfindG pnSch m h 0).headD 0 = 0 := by simpa using h1
    rw [pnW_miss p n m f h hf ht h0 h1'] at hW
    have hmiss : pm.nM[decI h]? = none :=
      memoRV_miss pnSch (hKey .name) (VP .name) m pm.nM hP.n h 0 hk h0 h1'
    rw [hmiss]
    cases hca : callW p n "pn_arm" [f - 1, h] m with
    | none => rw [hca] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hca] at hW
    cases hs : msetG pnSch m₁ h 0 (r₁.headD 0) with
    | none => simp only [memoK, hs] at hW; cases hW
    | some m₂ =>
    rw [memoK_some _ _ _ _ _ hs] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨a₁, pm₁, hrun, hD₁, hP₁, hpw, hcp, hfr, he, hl, hls, hsk⟩ :=
      ih.2 m a pm (f - 1) h r₁ m₁ hD hP hh ht hca
    refine ⟨a₁, { pm₁ with nM := pm₁.nM.insert (decI h) (decI (r₁.headD 0)) }, ?_,
      hD₁.memo pnSch pnSch_wf (by decide) (by decide) (by decide) h _ hs,
      hP₁.setN h _ hh hpw hs, by rw [← hr]; exact hpw, hcp, ?_, he, hl, hls,
      hsk.trans (SlKeep.of_frame (msetG_frame pnSch pnSch_wf _ _ _ _ _ hs) (by decide) (by decide))⟩
    · rw [run_bind_ok hrun, ← hr]; rfl
    · exact hfr.trans ((msetG_frame pnSch pnSch_wf _ _ _ _ _ hs).mono (by simp) (by simp))
  · intro m a pm f h r m' hD hP hh htier hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (pnArm_spec p hp n ⟨m, Locals.init []⟩ f h) hc
    simp only at hW
    have hh' : ¬ 4294967295 < h := fun e => by
      have : (4294967295 : Nat) < h.toNat := e
      omega
    by_cases hv : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
    · simp [pnArmW, hh', hv] at hW
    cases n with
    | zero => simp [pnArmW, callW_zero', hd1, pnStrK, pnNumK] at hW
    | succ n =>
    unfold pnArmT
    by_cases g0 : h >>> 28 = 0
    · by_cases hcnt : tcnt m NANON (tierW h) ≤ idxW h
      · simp [pnArmW, hh', hv, g0, hcnt] at hW
      rw [pnArmW_anon _ _ _ _ _ hh' hv g0 hcnt] at hW
      refine PNOk.of_sim (Sim.bind_twin (viewN_anon hD.1 hh hv g0 hcnt) ((Sim.hd1 (sim_pi
        (fun n s₀ => piNAnon_spec p hp n s₀) fun n _ _ h => piNAnon_rel p hp n m a hD _ _ h)).mono ?_)) hW
      rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₁, hpw, hcp, hfr⟩
      exact ⟨rfl, hD₁, hP.frameLo (by simp [NAREC, NASLOT]) (by simp) hfr, hpw, hcp,
        hfr.mono (by simp) (by simp), rfl, rfl, rfl, SlKeep.of_frame hfr (by decide) (by decide)⟩
    by_cases g1 : h >>> 28 = 1
    · by_cases hcnt : tcnt m NSTR (tierW h) ≤ idxW h
      · simp [pnArmW, hh', hv, g1, hcnt] at hW
      rw [pnArmW_str _ _ _ _ _ hh' hv g1 hcnt] at hW
      obtain ⟨st, hview, hsl, hk, hq⟩ := viewN_str hD.1 hh hv g1 hcnt
      refine PNOk.of_sim (Sim.bind_twin hview ?_) hW
      refine Sim.bindK rfl (fun _ _ => rfl) (Sim.ofP (ih.1 m a pm f _ · · hD hP hq)) ?_
      rintro r₁ ⟨pm₁, _⟩ m₁ a₁ ⟨rfl, hD₁, hP₁, hpw₁, hcp₁, hfr₁, he₁, hl₁, hls₁, hsk₁⟩
      dsimp only [pnStrK, pnNumK]
      obtain ⟨hsl₁, hv₁⟩ := hsk₁.2.2 _ _ hsl
      refine (Sim.hd1 (sim_piG _ (fun n s₀ => piNStr_spec p hp n s₀ _ _ _) fun n _ _ h =>
        piNStr_rel p hp n m₁ a₁ hD₁ _ _ _ hpw₁ hsl₁ st
          (by rw [← hk]; exact (sliceL_eq_iff _ _ _ _ _).mpr hv₁) _ _ h)).mono ?_
      rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₂, hpw₂, hcp₂, hfr₂, hsk₂⟩
      exact ⟨rfl, hD₂, hP₁.frameLo (by simp [POOL, PT0, NSREC, NSSLOT]) (by simp) hfr₂, hpw₂,
        hcp₂.trans hcp₁, hfr₁.trans (hfr₂.mono (by simp) (by simp)), he₁, hl₁, hls₁, hsk₁.trans hsk₂⟩
    by_cases g2 : h >>> 28 = 2
    · by_cases hcnt : tcnt m NNUM (tierW h) ≤ idxW h
      · simp [pnArmW, hh', hv, g2, hcnt] at hW
      rw [pnArmW_num _ _ _ _ _ hh' hv g2 hcnt] at hW
      obtain ⟨hview, hq⟩ := viewN_num hD.1 hh hv g2 hcnt
      refine PNOk.of_sim (Sim.bind_twin hview ?_) hW
      refine Sim.bindK rfl (fun _ _ => rfl) (Sim.ofP (ih.1 m a pm f _ · · hD hP hq)) ?_
      rintro r₁ ⟨pm₁, _⟩ m₁ a₁ ⟨rfl, hD₁, hP₁, hpw₁, hcp₁, hfr₁, he₁, hl₁, hls₁, hsk₁⟩
      dsimp only [pnStrK, pnNumK]
      refine (Sim.hd1 (sim_pi (fun n s₀ => piNNum_spec p hp n s₀ _ _) fun n _ _ h =>
        piNNum_rel p hp n m₁ a₁ hD₁ _ _ hpw₁ _ _ h)).mono ?_
      rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₂, hpw₂, hcp₂, hfr₂⟩
      exact ⟨rfl, hD₂, hP₁.frameLo (by simp [NNREC, NNSLOT]) (by simp) hfr₂, hpw₂,
        hcp₂.trans hcp₁, hfr₁.trans (hfr₂.mono (by simp) (by simp)), he₁, hl₁, hls₁,
        hsk₁.trans (SlKeep.of_frame hfr₂ (by decide) (by decide))⟩
    simp [pnArmW, hh', hv, g0, g1, g2] at hW

/-- **`promote_n` refines `promoteN`**: from `ArenaD`, the promotion memo and a handle word, a
returning run is a successful run of the twin's `promoteN` at the word fuel, with the relations
after (`PNOk`). -/
@[refines ConRon.Arena.promoteN]
theorem promoteN_refines (n : Nat) (s₀ : St) (a₀ : AState) (pm : PMemo) (f h : Word)
    (hD : ArenaD s₀.mem a₀) (hP : PMemoR s₀.mem pm) (hh : h.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "promote_n" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      PNOk (promoteN pm f.toNat (decI h)) s₀.mem a₀ pm (r.headD 0) s'.mem; ⊤⦄ :=
  triple_post (callW_spec p n "promote_n" [f, h] s₀) fun _ _ ⟨hl, hc⟩ =>
    ⟨hl, (pn_rel p hp n).1 _ _ _ _ _ _ _ hD hP hh hc⟩

end rel

end L.Arena
