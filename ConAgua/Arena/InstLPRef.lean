import ConAgua.Arena.InstLPSpec
import ConAgua.Arena.LevelInternRef
import ConRon.Bridge.SpecsL
import ConAgua.Arena.CoreLevels
import ConAgua.Census.Attr

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

set_option linter.unusedSimpArgs false

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

/-- The name readback cache holds readbacks. -/
def ReadNCOK (a : AState) : Prop :=
  ∀ (h : NIdx) (x : Name), a.caches.readNC[h]? = some x → denoteN a.store.ns h = some x

theorem readNameM_run (a : AState) (h : NIdx) (x : Name) (hd : denoteN a.store.ns h = some x)
    (hc : ReadNCOK a) :
    ∃ c, (readNameM h).run a = .ok (x, { a with caches := c }) ∧ ReadNCOK { a with caches := c } ∧
      c.readLC = a.caches.readLC ∧ c.readLsC = a.caches.readLsC := by
  simp only [readNameM]
  cases e : a.caches.readNC[h]? with
  | some x' =>
    have := hc _ _ e; rw [hd] at this; cases this
    exact ⟨a.caches, by simp [e]; rfl, hc, rfl, rfl⟩
  | none =>
    refine ⟨{ a.caches with readNC := a.caches.readNC.insert h x }, ?_, ?_, rfl, rfl⟩
    · simp [e, hd]; rfl
    · intro h' l' e'
      simp only [Std.HashMap.getElem?_insert] at e'
      split at e'
      · rename_i hb; cases e'; rw [← eq_of_beq hb]; exact hd
      · exact hc _ _ e'

/-! ## Small facts -/

theorem ArenaD.with_caches {m : Mem} {a : AState} (hA : ArenaD m a) (c : Caches) :
    ArenaD m { a with caches := c } :=
  ⟨hA.1.with_caches c, DerR.of_store _ _ _ hA.2 rfl⟩

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
    have : ¬ (A = A ∧ d = o ∧ d.toNat < (m.arr64 A).size) := fun ⟨_, e, _⟩ => by subst e; omega
    rw [if_neg this]; exact hx

theorem ReadLCOK.ext {a a' : AState} (hc : ReadLCOK a) (hx : Ext a.store a'.store)
    (hca : a'.caches.readLC = a.caches.readLC) : ReadLCOK a' := by
  intro h l e
  rw [hca] at e
  exact hx.lss.ls.lvl _ _ (hc h l e)

/-! ## `sle_go` refines `substLevelsAt` -/

/-- **The model of `sle_go` refines `substLevelsAt`** over the record-pool handle slice `(o, l)`:
the results land at `SPN[b ‥ b + l)`. -/
theorem sleW_ok (ks : List Name) (vs : List Level) (usIds : List LIdx) (ko kc vo vc : Word) :
    ∀ (ids : List LIdx) (n : Nat) (m m' : Mem) (a : AState) (o l b : Word),
    ArenaD m a → StoreWF a.store → ReadLCOK a →
    hslice? (m.arr64 EREC) o.toNat l.toNat = some ids → o.toNat + l.toNat < 2 ^ 64 →
    (∀ u ∈ ids, ∃ L, denoteL a.store.ls u = some L) →
    NmsR (nameN a.store.lss.ls.ns) m SPN ko kc ks → ko.toNat + kc.toNat ≤ b.toNat →
    sliceL (m.arr64 POOL) vo.toNat vc.toNat = lsWords usIds → vo.toNat + vc.toNat ≤ m.top.toNat →
    denoteLList a.store.ls usIds = some vs →
    b.toNat + l.toNat ≤ (m.arr64 SPN).size → (m.arr64 SPN).size < 2 ^ 63 →
    slElemW EREC n m o l b ko kc vo vc = some m' →
    ∃ hs a', (substLevelsAt ks vs ids).run a = .ok (hs, a') ∧ ArenaD m' a' ∧ StoreWF a'.store ∧
      ReadLCOK a' ∧ Ext a.store a'.store ∧ a'.pins = a.pins ∧ a'.memos = a.memos ∧
      sliceL (m'.arr64 SPN) b.toNat l.toNat = lsWords hs ∧
      (∀ i : Word, i.toNat < b.toNat → rdW (m'.arr64 SPN) i = rdW (m.arr64 SPN) i) ∧
      MemFrame (LH :: SPN :: lvArrs) (192 :: lvCtl) m m' := by
  intro ids
  induction ids with
  | nil =>
    intro n m m' a o l b hA hwf hrc hs hb hd hk hkb hvs hvb hdv hbs hsz hW
    have hl : l.toNat = 0 := by
      rcases hk' : l.toNat with _ | j
      · rfl
      · rw [hk', lp_hslice_succ] at hs
        simp only [Option.bind_eq_bind] at hs
        cases e : (hd? (m.arr64 EREC) o.toNat : Option LIdx) with
        | none => simp [e] at hs
        | some x =>
          cases e' : (hslice? (m.arr64 EREC) (o.toNat + 1) j : Option (List LIdx)) with
          | none => simp [e, e'] at hs
          | some xs => simp [e, e'] at hs
    have hl0 : l = 0 := UInt64.toNat_inj.mp (by simpa using hl)
    subst hl0
    cases n with
    | zero => simp [slElemW] at hW
    | succ n =>
    rw [slElemW_nil _ n m o 0 b ko kc vo vc rfl] at hW; cases hW
    exact ⟨[], a, rfl, hA, hwf, hrc, Ext.refl _, rfl, rfl, by simp [sliceL, lsWords], fun _ _ => rfl,
      MemFrame.refl _ _ _⟩
  | cons u us ih =>
    intro n m m' a o l b hA hwf hrc hs hb hd hk hkb hvs hvb hdv hbs hsz hW
    rcases hk' : l.toNat with _ | j
    · rw [hk'] at hs; simp [hslice?] at hs
    rw [hk', lp_hslice_succ] at hs
    simp only [Option.bind_eq_bind] at hs
    cases e : (hd? (m.arr64 EREC) o.toNat : Option LIdx) with
    | none => simp [e] at hs
    | some x' =>
    cases e' : (hslice? (m.arr64 EREC) (o.toNat + 1) j : Option (List LIdx)) with
    | none => simp [e, e'] at hs
    | some xs' =>
    simp only [e, e', Option.bind_some, Option.pure_def, Option.some.injEq, List.cons.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    -- the word at `o`
    simp only [hd?] at e
    cases ew : (m.arr64 EREC)[o.toNat]? with
    | none => simp [ew] at e
    | some w =>
    simp only [ew] at e
    have hw : w.toNat < 2 ^ 32 := Classical.byContradiction fun hw => by simp [hw] at e
    simp [hw] at e
    subst e
    have hrd : rdW (m.arr64 EREC) o = w := by simp [rdW, ew]
    have hl0 : l ≠ 0 := fun h0 => by subst h0; simp at hk'
    obtain ⟨L, hdu⟩ := hd _ (List.mem_cons_self ..)
    cases n with
    | zero => simp [slElemW] at hW
    | succ n =>
    rw [slElemW_cons _ n m o l b ko kc vo vc hl0, hrd] at hW
    cases hS : lvSubIntW n m w ko kc vo vc with
    | none => rw [hS] at hW; simp [slElemK] at hW
    | some r =>
    obtain ⟨h, m₁⟩ := r
    rw [hS, slElemK_some] at hW
    by_cases hh : 4294967296 ≤ h
    · simp [hh] at hW
    simp only [hh, ↓reduceIte] at hW
    -- the twin's readback
    obtain ⟨X, hrl, hrc'⟩ := readLevelM_run' a (decI w) L hdu hrc
    generalize hac : ({ a with caches := { a.caches with readLC := X } } : AState) = ac at hrl hrc'
    have hAc : ArenaD m ac := by rw [← hac]; exact hA.with_caches _
    have hstc : ac.store = a.store := by rw [← hac]
    -- the element
    have hA₀ := arenaD_reset hAc
    have hpool₀ : (m.set64 CTL 192 0).arr64 POOL = m.arr64 POOL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have htop := m.top.toNat_lt
    have hv₀ := lvsR_of_slice hA₀.1 usIds vs _ _ (by rw [hpool₀]; exact hvs) (by omega)
      (by rw [hstc]; exact hdv)
    have hk₀ : NmsR (nameN ac.store.lss.ls.ns) (m.set64 CTL 192 0) SPN ko kc ks := by
      rw [hstc]; exact hk.of_arr (Mem.arr64_set64_ne _ _ _ _ _ (by decide))
    obtain ⟨a₁, hrun₁, hA₁, hlt₁, hf₁, hkp₁⟩ := lvSubIntW_ok n m m₁ ac w ko kc vo vc h L ks vs hAc
      (by rw [hstc]; exact StoreWF.nwf hwf) hw (by rw [hstc]; exact hdu) hk₀ hv₀ hS
    obtain ⟨hwf₁, hx₁, hca₁, hpi₁, hme₁, -⟩ := internLevel_facts (by rw [hstc]; exact hwf) hrun₁
    rw [hstc] at hx₁
    -- the store on the stack
    have hf₂ : MemFrame [SPN] [] m₁ (m₁.set64 SPN b h) := MemFrame.set64 _ _ (by decide) _ _
    have hA₂ : ArenaD (m₁.set64 SPN b h) a₁ := arenaD_frame_hi hA₁ hf₂ (by simp [SPN]) (by simp)
    have hspn₁ : m₁.arr64 SPN = m.arr64 SPN := hf₁.1 SPN (by simp [lvArrs, LH, SPN, ZREC, ZSLOT, SREC, SSLOT,
      MREC, MSLOT, IREC, ISLOT, PREC, PSLOT]) (by decide)
    have herec₂ : (m₁.set64 SPN b h).arr64 EREC = m.arr64 EREC := by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
      exact hf₁.1 EREC (by simp [lvArrs, LH, EREC, ZREC, ZSLOT, SREC, SSLOT, MREC, MSLOT, IREC, ISLOT,
        PREC, PSLOT]) (by decide)
    have hpool₂ : (m₁.set64 SPN b h).arr64 POOL = m.arr64 POOL := by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
      exact hf₁.1 POOL (by simp [lvArrs, LH, POOL, ZREC, ZSLOT, SREC, SSLOT, MREC, MSLOT, IREC, ISLOT,
        PREC, PSLOT]) (by decide)
    have htop₂ : (m₁.set64 SPN b h).top = m.top := by
      simp only [Mem.top]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
      have := hf₁.2.1 0 (by simp [lvCtl])
      simpa [rdW] using this
    have hsz₂ : ((m₁.set64 SPN b h).arr64 SPN).size = (m.arr64 SPN).size := by
      rw [Mem.size_arr64_set64, hspn₁]
    have hb1 : (b + 1).toNat = b.toNat + 1 := toNat_succ_lt (by omega)
    have ho1 : (o + 1).toNat = o.toNat + 1 := toNat_succ_lt (by omega)
    have hl1 : (l - 1).toNat = j := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    have hns₁ : a₁.store.lss.ls.ns = a.store.lss.ls.ns := by rw [hkp₁.2, hstc]
    obtain ⟨hs', a', hrun', hA', hwf', hrc'', hx', hpi', hme', hsl', hbl', hf'⟩ :=
      ih n (m₁.set64 SPN b h) m' a₁ (o + 1) (l - 1) (b + 1) hA₂ hwf₁
        (hrc'.ext (by rw [hstc]; exact hx₁) (by rw [hca₁]))
        (by rw [herec₂, ho1, hl1]; exact e')
        (by rw [ho1, hl1]; omega)
        (fun u hu => by
          obtain ⟨L', hL'⟩ := hd u (List.mem_cons_of_mem _ hu)
          exact ⟨L', hx₁.lss.ls.lvl _ _ hL'⟩)
        (by rw [hns₁]; exact NmsR.set_past (NmsR.of_arr (m := m) (m' := m₁) hspn₁ hk) (by omega))
        (by rw [hb1]; omega)
        (by rw [hpool₂]; exact hvs) (by rw [htop₂]; exact hvb)
        (hx₁.lss.ls.lvl |> fun hl => denoteLList_mono_of_lext hx₁.lss.ls _ _ hdv)
        (by rw [hsz₂, hb1, hl1]; omega) (by rw [hsz₂]; exact hsz) hW
    refine ⟨decI h :: hs', a', ?_, hA', hwf', hrc'', hx₁.trans hx', ?_, ?_, ?_, ?_, ?_⟩
    · simp only [substLevelsAt, StateT.run_bind, hrl, except_ok_bind, hrun₁, hrun']; rfl
    · rw [hpi', hpi₁, ← hac]
    · rw [hme', hme₁, ← hac]
    · rw [sliceL_succ]
      have hbb : rdW (m'.arr64 SPN) b = h := by
        rw [hbl' b (by rw [hb1]; omega), rdW_set64]
        simp [show b.toNat < (m₁.arr64 SPN).size by rw [hspn₁]; omega]
      simp only [lsWords, List.map_cons, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · have : (m'.arr64 SPN)[b.toNat]?.getD 0 = rdW (m'.arr64 SPN) b := rfl
        rw [this, hbb]
        exact ((word_decI _ h (by omega)).mpr rfl).symm
      · rw [hb1, hl1] at hsl'; simpa [lsWords] using hsl'
    · intro i hi
      rw [hbl' i (by rw [hb1]; omega), rdW_set64, hspn₁]
      have : ¬ b = i := fun e => by subst e; omega
      simp [this]
    · exact (hf₁.mono (by simp) (by simp)).trans ((hf₂.mono (by simp) (by simp)).trans hf')

end L.Arena
