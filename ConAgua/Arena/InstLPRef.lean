module

public import ConAgua.Arena.InstLPSpec
public import ConAgua.Arena.LevelInternRef
import ConRon.Bridge.SpecsL
import ConAgua.Arena.CoreLevels
import ConAgua.Front.ApplyExprRefine

@[expose] public section

/-!
# The level-list functions refine the twin's: `substLevelsAt`, `substParamLevels`, `recFireLevels`

Under `ArenaD` and the twin's store invariant `StoreWF` (con-ron's `WF.lean`; `CoreS` carries only
the name store's part, `nwf`, so it is a hypothesis here: see DESIGN.md), by induction on the
handle list:

* the twin's `internLevel` keeps `StoreWF`, extends the store (`Ext`), keeps the caches, and the
  result denotes the level (con-ron's `internLevel_spec`, `Bridge/SpecsL.lean`); so the values'
  and the remaining handles' readbacks survive each element;
* the twin's readback caches (`readLC`, `readNC`) hold readbacks (`ReadLCOK`, `ReadNCOK`), so its
  `readLevelM`/`readNameM` return the denotation;
* each element's result lands on the stack above the keys (`SPN[b + i]`), the list is copied to
  the pool top and interned (`spn_ls`, `internLs_refines`).
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## Twin triples applied to runs -/

theorem AM.of_triple {α : Type} {prog : AM α} {s s' : AState} {a : α} {P : AState → Prop}
    {Q : α → AState → Prop} (hp : P s) (h : prog.run s = .ok (a, s'))
    (hwp : ⦃fun s => P s⦄ prog ⦃fun r s'' => Q r s''; ⊤⦄) : Q a s' := by
  have hs := hwp.le_wp s hp
  rw [Std.WP.StateT.wp_apply_eq, h] at hs
  exact hs

theorem StoreWF.nwf {st : EStore} (h : StoreWF st) : NStoreWF st.lss.ls.ns := by
  obtain ⟨rk, w⟩ := h
  obtain ⟨rk', w'⟩ := w.lss.ls
  exact w'.ns

/-- **What the twin's `internLevel` does to its state** (con-ron's `internLevel_spec`). -/
theorem internLevel_facts {a a' : AState} {u : Level} {h : LIdx} (hwf : StoreWF a.store)
    (hrun : (internLevel u).run a = .ok (h, a')) :
    StoreWF a'.store ∧ Ext a.store a'.store ∧ a'.caches = a.caches ∧ a'.pins = a.pins ∧
      a'.memos = a.memos ∧ denoteL a'.store.ls h = some u := by
  have := AM.of_triple (P := fun s => s = a) rfl hrun (ConRon.Bridge.internLevel_spec a u hwf)
  obtain ⟨h1, h2, -, -, -, h6, h7, h8, h9⟩ := this
  exact ⟨h1, h2, h7, h8, h6, h9⟩

/-! ## The name readback cache -/

theorem readNameM_run (a : AState) (h : NIdx) (x : Name) (hd : denoteN a.store.ns h = some x)
    (hc : ReadNCOK a) :
    ∃ c, (readNameM h).run a = .ok (x, { a with caches := c }) ∧ ReadNCOK { a with caches := c } ∧
      c.readLC = a.caches.readLC ∧ c.readLsC = a.caches.readLsC ∧
      c = { a.caches with readNC := c.readNC } := by
  simp only [readNameM]
  cases e : a.caches.readNC[h]? with
  | some x' =>
    have := hc _ _ e; rw [hd] at this; cases this
    exact ⟨a.caches, by simp [e]; rfl, hc, rfl, rfl, rfl⟩
  | none =>
    refine ⟨{ a.caches with readNC := a.caches.readNC.insert h x }, ?_, ?_, rfl, rfl, rfl⟩
    · simp [e, hd]; rfl
    · intro h' l' e'
      simp only [Std.HashMap.getElem?_insert] at e'
      split at e'
      · rename_i hb; cases e'; rw [← eq_of_beq hb]; exact hd
      · exact hc _ _ e'

/-! ## Small facts -/

theorem ArenaD.with_caches {m : Mem} {a : AState} (hA : ArenaD m a) (c : Caches) :
    ArenaD m { a with caches := c } :=
  ⟨hA.base.with_caches c, DerR.of_store _ _ _ hA.der rfl⟩

/-- A write at or past the end of a name slice keeps it. -/
theorem NmsR.set_past {N : Word → Name → Prop} {m : Mem} {A : ArrId} {d v : Word} :
    ∀ {o k : Word} {xs : List Name}, NmsR N m A o k xs → o.toNat + k.toNat ≤ d.toNat →
      NmsR N (m.set64 A d v) A o k xs := by
  intro o k xs h hb
  induction h with
  | nil => exact .nil
  | @cons o k x xs hk0 hx _ ih =>
    have hk1 : 1 ≤ k.toNat := by
      rcases Nat.eq_zero_or_pos k.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hk0
      · omega
    have ho1 : (o + 1).toNat = o.toNat + 1 := toNat_succ_lt (by have := d.toNat_lt; omega)
    have hkm : (k - 1).toNat = k.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    refine .cons hk0 ?_ (ih (by rw [ho1, hkm]; omega))
    rw [rdW_set64]
    have : ¬ ((A : TieredArray) = A ∧ d = o ∧ d.toNat < (m.arr64 A).size) := fun ⟨_, e, _⟩ => by subst e; omega
    rw [ite_eq_right this]; exact hx

theorem ReadLCOK.ext {a a' : AState} (hc : ReadLCOK a) (hx : Ext a.store a'.store)
    (hca : a'.caches.readLC = a.caches.readLC) : ReadLCOK a' := by
  intro h l e
  rw [hca] at e
  exact hx.lss.ls.lvl _ _ (hc h l e)

/-! ## `sle_go` refines `substLevelsAt` -/

/-- **The model of `sle_go` refines `substLevelsAt`** over the record-pool handle slice `(o, l)`:
the results land at `SPN[b ‥ b + l)`. -/
@[refines ConRon.Arena.substLevelsAt]
theorem sleW_ok (ks : List Name) (vs : List Level) (usIds : List LIdx) (ko kc vo vc : Word) :
    ∀ (ids : List LIdx) (n : Nat) (m m' : Mem) (a : AState) (o l b : Word),
    ArenaD m a → StoreWF a.store → ReadLCOK a →
    hslice? (erecP m) o.toNat l.toNat = some ids → o.toNat + l.toNat < 2 ^ 64 →
    (∀ u ∈ ids, ∃ L, denoteL a.store.ls u = some L) →
    NmsR (nameN a.store.lss.ls.ns) m SPN ko kc ks → ko.toNat + kc.toNat ≤ b.toNat →
    sliceL (vpool m) vo.toNat vc.toNat = lsWords usIds → vo.toNat + vc.toNat ≤ m.top.toNat →
    denoteLList a.store.ls usIds = some vs →
    b.toNat + l.toNat ≤ (m.arr64 SPN).size → (m.arr64 SPN).size < 2 ^ 63 →
    slElemW EREC n m o l b ko kc vo vc = some m' →
    ∃ hs a', (substLevelsAt ks vs ids).run a = .ok (hs, a') ∧ ArenaD m' a' ∧ StoreWF a'.store ∧
      ReadLCOK a' ∧ Ext a.store a'.store ∧ a'.pins = a.pins ∧ a'.memos = a.memos ∧
      a'.caches = { a.caches with readLC := a'.caches.readLC } ∧
      sliceL (m'.arr64 SPN) b.toNat l.toNat = lsWords hs ∧
      (∀ i : Word, i.toNat < b.toNat → rdW (m'.arr64 SPN) i = rdW (m.arr64 SPN) i) ∧
      MemFrame (LH :: SPN :: lvArrs) (192 :: lvCtl) m m' := by
  sorry

theorem ReadNCOK.ext {a a' : AState} (hc : ReadNCOK a) (hx : Ext a.store a'.store)
    (hca : a'.caches.readNC = a.caches.readNC) : ReadNCOK a' := by
  intro h l e
  rw [hca] at e
  exact hx.lss.ls.ns _ _ (hc h l e)

/-- One parameter's substitute, interned: `lookup` found a value (`lv_intern` of it) or not (the
parameter node, its name re-interned to itself). -/
theorem slpOne_ok (ks : List Name) (vs : List Level) (n : Nat) (m m₁ : Mem) (a : AState)
    (ko kc vo vc w h : Word) (nm : Name) (hA : ArenaD m a) (hwf : NStoreWF a.store.lss.ls.ns)
    (hk : NmsR (nameN a.store.lss.ls.ns) m SPN ko kc ks)
    (hv : LvsR (nameN a.store.lss.ls.ns) m vo vc vs) (hn : nameN a.store.lss.ls.ns w nm)
    (hW : slpOne n m w (lookupW (keyA SPN) POOL n m ko kc vo vc w) = some (h, m₁)) :
    ∃ a₁, (internLevel (Level.subst ks vs (.param nm))).run a = .ok (decI h, a₁) ∧ ArenaD m₁ a₁ ∧
      MemFrame lvArrs lvCtl m m₁ ∧ LKeep a a₁ := by
  rcases e : lookupW (keyA SPN) POOL n m ko kc vo vc w with _ | ⟨f, v⟩ <;> rw [e] at hW
  · simp [slpOne] at hW
  rcases lookupW_ok (nameN_rel _ hwf) n _ _ _ _ _ _ _ _ _ _ _ hk.toK hv.toAR hn e with ⟨hf, hvl⟩ | ⟨rfl, hgo⟩
  · rw [slpOne_hit n m w f v hf] at hW
    obtain ⟨a₁, hrun, hA₁, hlt, hfr, hkp, -⟩ := lvInternW_ok _ n m a v h m₁ hA hwf hvl hW
    exact ⟨a₁, by simpa [Level.subst] using hrun, hA₁, hfr, hkp⟩
  · rw [slpOne_miss] at hW
    obtain ⟨ok, hR, res, hfr⟩ := L.Front.param_A m a hA h m₁ w hn.1 hW
    have hrun := node_run ok
    rw [res] at hrun
    have hk' := internLNode_keep _ _ _ _ hrun
    refine ⟨_, ?_, hR, hfr.mono lvSch_sub.2.2.2.2.2.2.2.2.1 lvSch_sub.2.2.2.2.2.2.2.2.2, hk'⟩
    · simp only [Level.subst, hgo]
      show (internName nm >>= fun hn => internLNode (.param hn)).run a = _
      rw [StateT.run_bind, internName_nameN_run a hwf hn]; exact hrun

/-- **The model of `slp_go` refines `substParamLevels`** over the record-pool name slice `(o, l)`:
the results land at `SPN[b ‥ b + l)`. -/
@[refines ConRon.Arena.substParamLevels]
theorem slpW_ok (ks : List Name) (vs : List Level) (usIds : List LIdx) (ko kc vo vc : Word) :
    ∀ (ids : List NIdx) (n : Nat) (m m' : Mem) (a : AState) (o l b : Word),
    ArenaD m a → StoreWF a.store → ReadNCOK a →
    hslice? (erecP m) o.toNat l.toNat = some ids → o.toNat + l.toNat < 2 ^ 64 →
    (∀ u ∈ ids, ∃ nm, denoteN a.store.lss.ls.ns u = some nm) →
    NmsR (nameN a.store.lss.ls.ns) m SPN ko kc ks → ko.toNat + kc.toNat ≤ b.toNat →
    sliceL (vpool m) vo.toNat vc.toNat = lsWords usIds → vo.toNat + vc.toNat ≤ m.top.toNat →
    denoteLList a.store.ls usIds = some vs →
    b.toNat + l.toNat ≤ (m.arr64 SPN).size → (m.arr64 SPN).size < 2 ^ 63 →
    slpW n m o l b ko kc vo vc = some m' →
    ∃ hs a', (substParamLevels ks vs ids).run a = .ok (hs, a') ∧ ArenaD m' a' ∧ StoreWF a'.store ∧
      ReadNCOK a' ∧ Ext a.store a'.store ∧ a'.pins = a.pins ∧ a'.memos = a.memos ∧
      a'.caches = { a.caches with readNC := a'.caches.readNC } ∧
      sliceL (m'.arr64 SPN) b.toNat l.toNat = lsWords hs ∧
      (∀ i : Word, i.toNat < b.toNat → rdW (m'.arr64 SPN) i = rdW (m.arr64 SPN) i) ∧
      MemFrame (SPN :: lvArrs) lvCtl m m' := by
  sorry

/-! ## `spn_pool`, `spn_ls`: the list interned -/

/-- The twin's `internLsNode` changes only the store. -/
theorem internLsNode_keep (v : LsNodeView) (a a' : AState) (i : LsIdx)
    (h : (internLsNode v).run a = .ok (i, a')) :
    a'.caches = a.caches ∧ a'.pins = a.pins ∧ a'.memos = a.memos := by
  unfold internLsNode at h
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
  split at h
  · simp only [StateT.run_pure] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    exact ⟨rfl, rfl, rfl⟩
  · split at h <;> split at h <;> first
      | (simp only [StateT.bind, StateT.pure, StateT.run,
          bind, Except.bind, pure, Except.pure] at h
         injection h with h
         obtain ⟨-, rfl⟩ := Prod.mk.inj h
         exact ⟨rfl, rfl, rfl⟩)
      | simp [fail, throwThe, MonadExceptOf.throw, StateT.run, bind, StateT.lift,
          Except.bind] at h

/-- **The model of `spn_ls` refines `internLsNode hs`** at a stack slice holding the list's words:
the pool grows by the copy (its old part untouched), the list store by the node. -/
theorem spnLsW_ok (n : Nat) (m m' : Mem) (a : AState) (b l r : Word) (hs : List LIdx)
    (hA : ArenaD m a) (hmode : ModeOK m) (hsl : sliceL (m.arr64 SPN) b.toNat l.toNat = lsWords hs)
    (hb : b.toNat + l.toNat < 2 ^ 64) (hW : spnLsW n m b l = some (r, m')) :
    ∃ a', (internLsNode hs).run a = .ok (decI r, a') ∧ ArenaD m' a' ∧ r.toNat < 2 ^ 32 ∧
      MemFrame [POOL, POOL1, LSREC, LSSLOT, LSHP, tier1 LSREC, tier1 LSSLOT, tier1 LSHP] [0, 40, 41] m m' ∧
      Agree (vpool m') (vpool m) m.top.toNat ∧
      m.top.toNat ≤ m'.top.toNat ∧ pcap m' = pcap m ∧
      a'.caches = a.caches ∧ a'.pins = a.pins ∧ a'.memos = a.memos := by
  obtain ⟨m₂, hg, htop₂, htl, hsl₂, hmf, -, hI, hr⟩ := spnLsW_pool n m m' b l r hA.base.lit.1 hb hW
  have hA₂ : ArenaD m₂ a := ArenaD.grow m m₂ hg a hA
  have hq : SliceOK m₂ m.top l := SliceOK.fresh hg htop₂
  have hq0 : m₂.flag = 0 → m.top.toNat < 2 ^ 40 := fun hf => by
    exact (hmode.poolGrew (PoolGrew.of_grows hg)).slice0 hq hf
  obtain ⟨ok, hA₃, res, hf₃⟩ := L.Front.internLs_D m₂ a hA₂ r m' m.top l hq hs
    (by rw [hsl₂, hsl]) hq0 hI
  have hrun := AM.run_of_ok _ _ ok
  rw [res] at hrun
  obtain ⟨hca, hpi, hme⟩ := internLsNode_keep _ _ _ _ hrun
  have hpool₃ : m'.arr64 POOL = m₂.arr64 POOL :=
    hf₃.1 POOL (by simp [tier1, lsSch, LSREC, LSSLOT, LSHP, POOL]) (by decide)
  have hpool₃' : m'.arr64 POOL1 = m₂.arr64 POOL1 :=
    hf₃.1 POOL1 (by simp [tier1, lsSch, LSREC, LSSLOT, LSHP, POOL1]) (by decide)
  have htop₃ : m'.top = m₂.top := by simp only [top_rdW]; exact hf₃.ctl 0 (by simp [lsSch])
  refine ⟨_, hrun, hA₃, hr, ?_, ?_, ?_, ?_, hca, hpi, hme⟩
  · exact (hmf.mono (by simp) (by simp)).trans (hf₃.mono (by simp [lsSch]) (by simp [lsSch]))
  · rw [vpool_congr hpool₃ hpool₃']; exact hg.agree
  · rw [htop₃]; exact hg.le
  · rw [pcap_congr' hpool₃ hpool₃']; exact hg.pcapEq

/-! ## `keys_push`: the keys on the stack -/

/-- **`keys_push` puts an `EREC` name slice on the stack** at the old top `b`, raises the top past
it, and writes nothing else. -/
theorem keysPushW_ok {N : Word → Name → Prop} (n : Nat) (m m₁ : Mem) (po pc b : Word) (ks : List Name)
    (hk : NmsR N m EREC po pc ks) (hsz : (m.arr64 SPN).size < 2 ^ 63)
    (hctl : 136 < (m.arr64 CTL).size) (hW : keysPushW n m po pc = some (b, m₁)) :
    b = spTop m ∧ NmsR N m₁ SPN b pc ks ∧ MemFrame [SPN] [136] m m₁ ∧
      (spTop m₁).toNat = b.toNat + pc.toNat ∧ b.toNat + pc.toNat ≤ (m.arr64 SPN).size ∧
      ∀ i : Word, i.toNat < b.toNat → rdW (m₁.arr64 SPN) i = rdW (m.arr64 SPN) i := by
  cases n with
  | zero => simp [keysPushW] at hW
  | succ n =>
  simp only [keysPushW] at hW
  by_cases t1 : m.len64 SPN < spTop m
  · simp [t1] at hW
  by_cases t2 : m.len64 SPN - spTop m < pc
  · simp [t1, t2] at hW
  simp only [t1, t2, ↓reduceIte] at hW
  have hlen : (m.len64 SPN).toNat = (m.arr64 SPN).size := L.Front.toNat_ofNat_size _ hsz
  have t1' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp t1)
  have t2' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp t2)
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp t1), hlen] at t2'
  rw [hlen] at t1'
  have hroom : (spTop m).toNat + pc.toNat ≤ (m.arr64 SPN).size := by omega
  rcases hc : ekCopyW n m po (spTop m) pc with _ | mc <;> rw [hc] at hW
  · simp [kpK] at hW
  rw [kpK_some] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨hk₁, hf₁, hb₁⟩ := ekCopyW_ok ks n m mc po (spTop m) pc hk hroom hsz hc
  have hspn : (mc.set64 CTL 136 (spTop m + pc)).arr64 SPN = mc.arr64 SPN :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hctl' : (136 : Word).toNat < (mc.arr64 CTL).size := by rw [hf₁.size CTL]; simpa using hctl
  refine ⟨rfl, hk₁.of_arr hspn, (hf₁.mono (by simp) (by simp)).trans
    ((MemFrame.setCtl _ _ _).mono (by simp) (by simp)), ?_, hroom, fun i hi => by rw [hspn]; exact hb₁ i hi⟩
  simp only [spTop]; rw [rdW_set64]; simp only [hctl', and_self, ↓reduceIte]
  rw [UInt64.toNat_add]; simp only [spTop] at hroom ⊢; omega

/-! ## The twin's readbacks of the substitution -/

theorem readNamesM_run (a : AState) (hc : ReadNCOK a) : ∀ (lps : List NIdx) (ks : List Name),
    lps.mapM (denoteN a.store.lss.ls.ns) = some ks →
    ∃ c, (readNamesM lps).run a = .ok (ks, { a with caches := c }) ∧ ReadNCOK { a with caches := c } ∧
      c.readLC = a.caches.readLC ∧ c.readLsC = a.caches.readLsC ∧
      c = { a.caches with readNC := c.readNC } := by
  intro lps
  induction lps generalizing a with
  | nil =>
    intro ks h; simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h
    exact ⟨a.caches, rfl, hc, rfl, rfl, rfl⟩
  | cons p ps ih =>
    intro ks h
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h
    cases d1 : denoteN a.store.lss.ls.ns p with
    | none => simp [d1] at h
    | some nm =>
    cases d2 : ps.mapM (denoteN a.store.lss.ls.ns) with
    | none => simp [d1, d2] at h
    | some nms =>
    simp only [d1, d2, Option.bind_some, Option.some.injEq] at h
    subst h
    obtain ⟨c₁, hr₁, hc₁, e₁, f₁, g₁⟩ := readNameM_run a p nm d1 hc
    obtain ⟨c₂, hr₂, hc₂, e₂, f₂, g₂⟩ := ih { a with caches := c₁ } hc₁ nms d2
    refine ⟨c₂, ?_, hc₂, e₂.trans e₁, f₂.trans f₁, g₂.trans (by rw [g₁])⟩
    simp only [readNamesM, StateT.run_bind, hr₁, except_ok_bind, hr₂]; rfl

theorem lp_readLevelsM_run (a : AState) (h : LsIdx) (ls : List Level)
    (hd : denoteLs a.store.lss h = some ls) (hc : ReadLsCOK a) :
    ∃ c, (readLevelsM h).run a = .ok (ls, { a with caches := c }) ∧
      ReadLsCOK { a with caches := c } ∧ c.readLC = a.caches.readLC ∧ c.readNC = a.caches.readNC ∧
      c = { a.caches with readLsC := c.readLsC } := by
  simp only [readLevelsM]
  cases e : a.caches.readLsC[h]? with
  | some l' =>
    have := hc _ _ e; rw [hd] at this; cases this
    exact ⟨a.caches, by simp [e]; rfl, hc, rfl, rfl, rfl⟩
  | none =>
    refine ⟨{ a.caches with readLsC := a.caches.readLsC.insert h ls }, ?_, ?_, rfl, rfl, rfl⟩
    · simp [e, hd]; rfl
    · intro h' l' e'
      simp only [Std.HashMap.getElem?_insert] at e'
      split at e'
      · rename_i hb; cases e'; rw [← eq_of_beq hb]; exact hd
      · exact hc _ _ e'

end L.Arena
