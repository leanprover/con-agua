import ConAgua.Arena.PropReadW
import ConAgua.Arena.InferFieldSort
import ConAgua.Arena.CoreDen
import ConAgua.Arena.LevelInternRef

/-!
# The prop-ness readers: the relations, `residual_pw`, `subst_pw_at` (helper `defeq2-prop`)

**After a reader** (`RdAfter`): the core relation at the same maps, the stack kept, only the spine
stack, the level heap and their tops written (`MemFrame [SPN, LH] [136, 192]`), the twin's store
unchanged (the readers read; the twin's readbacks write only its readback caches).

**The datum** (`PWD`): `(k, o, c)` denotes an `Option PropWhen`, the names `LH[o .. o + c)` read
by the store's name decoder `nameN` (`LevelArena.lean`), below the heap top.

**Readbacks.** `residualPW` reads a `sort` node's level back (`StoreDen.sort`); `substPWAt` reads
the constant's level-parameter names (`readNamesM`: the name cache `StoreDen.readN` and the
names' readbacks, an argument here) and the use's level list (`readLevelsM`: `StoreDen.constLs`,
an argument here).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

open ConLeche (Name Level PropWhen)

/-! ## The relations -/

/-- **After a reader.** -/
def RdAfter (dn : NIdx → Option ConLeche.Name) (m m' : Mem) (a a' : AState) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb : Word) : Prop :=
  CoreS dn m' a' vis fe M eb ∧ StackKept m m' ∧ MemFrame [SPN, LH] [136, 192] m m' ∧
    a'.store = a.store

section rd
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}

theorem RdAfter.refl {m : Mem} {a : AState} (hS : CoreS dn m a vis fe M eb) :
    RdAfter dn m m a a vis fe M eb :=
  ⟨hS, StackKept.refl _, MemFrame.refl _ _ _, rfl⟩

theorem RdAfter.trans {m₁ m₂ m₃ : Mem} {a₁ a₂ a₃ : AState}
    (h₁ : RdAfter dn m₁ m₂ a₁ a₂ vis fe M eb) (h₂ : RdAfter dn m₂ m₃ a₂ a₃ vis fe M eb) :
    RdAfter dn m₁ m₃ a₁ a₃ vis fe M eb :=
  ⟨h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem RdAfter.rel {m m' : Mem} {a a' : AState} (h : RdAfter dn m m' a a' vis fe M eb) :
    CoreS dn m' a' vis fe M eb := h.1

theorem RdAfter.erec {m m' : Mem} {a a' : AState} (h : RdAfter dn m m' a a' vis fe M eb) :
    m'.arr64 EREC = m.arr64 EREC :=
  h.2.2.1.1 EREC (by simp [EREC, SPN, LH]) (by decide)

/-- A heap computation keeps the relation. -/
theorem RdAfter.heap {m m' : Mem} {a : AState} (hS : CoreS dn m a vis fe M eb) (he : HeapExt m m') :
    RdAfter dn m m' a a vis fe M eb := by
  obtain ⟨hS', hK⟩ := hS.frame he.memFrame (fun b hb => by simp at hb; subst hb; decide)
    (fun x hx => by simp at hx; subst hx; decide)
  exact ⟨hS', hK, he.memFrame.mono (by simp) (by simp), rfl⟩

/-- A reader that does not write. -/
theorem RdAfter.same {m : Mem} {a : AState} (hS : CoreS dn m a vis fe M eb) :
    RdAfter dn m m a a vis fe M eb := RdAfter.refl hS

/-- **After a reader, as a core run**: `CoreAfter` at the same maps. -/
theorem RdAfter.core {m m' : Mem} {a a' : AState} (h : RdAfter dn m m' a a' vis fe M eb) :
    CoreAfter dn m m' a' vis fe M eb :=
  ⟨M, h.1, KeptAll.refl _ _, h.2.1⟩

end rd

/-- **The datum** `(k, o, c)`. -/
def PWD (N : Word → Name → Prop) (m : Mem) (k o c : Word) : Option PropWhen → Prop
  | none => k = 0
  | some .never => k = 1
  | some (.ifAllZero ps) => k = 2 ∧ NmsR N m LH o c ps ∧ o.toNat + c.toNat ≤ (htop m).toNat

theorem PWD.none_iff {N : Word → Name → Prop} {m : Mem} {k o c : Word} {r : Option PropWhen}
    (h : PWD N m k o c r) : k = 0 ↔ r = none := by
  rcases r with _ | _ | ps
  · exact ⟨fun _ => rfl, fun _ => h⟩
  · simp only [PWD] at h; subst h; simp
  · obtain ⟨rfl, -⟩ := h; simp

theorem NmsR.nil_iff {N : Word → Name → Prop} {m : Mem} {A : ArrId} {o c : Word} {ps : List Name}
    (h : NmsR N m A o c ps) : c = 0 ↔ ps = [] := by
  cases h with
  | nil => simp
  | cons hk _ _ => simp [hk]

/-! ## The twin's readbacks -/

theorem pr_readLevel_run (a : AState) (u : LIdx) (l : Level) (hd : denoteL a.store.ls u = some l) :
    (readLevel u).run a = .ok (l, a) := by
  simp [readLevel, hd, StateT.run_bind, StateT.run_get]; rfl

/-- `readNameM` at a defined handle: its readback, and only `readNC` changes. -/
theorem pr_readNameM_run (a : AState) (h : NIdx) (x : Name) (hd : denoteN a.store.ns h = some x)
    (hc : ReadNCOK a) :
    ∃ X, (readNameM h).run a = .ok (x, { a with caches := { a.caches with readNC := X } }) ∧
      ReadNCOK { a with caches := { a.caches with readNC := X } } := by
  simp only [readNameM]
  cases e : a.caches.readNC[h]? with
  | some x' =>
    have := hc _ _ e; rw [hd] at this; cases this
    exact ⟨a.caches.readNC, by simp [e]; rfl, by simpa using hc⟩
  | none =>
    refine ⟨a.caches.readNC.insert h x, ?_, ?_⟩
    · simp [e, hd]; rfl
    · intro h' x' e'
      simp only [Std.HashMap.getElem?_insert] at e'
      split at e'
      · rename_i hb; cases e'; rw [← eq_of_beq hb]; exact hd
      · exact hc _ _ e'

/-- `readNamesM` at names that read back. -/
theorem pr_readNamesM_run : ∀ (lps : List NIdx) (a : AState) (ks : List Name),
    lps.mapM (denoteN a.store.ns) = some ks → ReadNCOK a →
    ∃ X, (readNamesM lps).run a = .ok (ks, { a with caches := { a.caches with readNC := X } }) ∧
      ReadNCOK { a with caches := { a.caches with readNC := X } }
  | [], a, ks, h, hc => by
    simp at h; subst h
    exact ⟨a.caches.readNC, by simp [readNamesM]; rfl, by simpa using hc⟩
  | x :: xs, a, ks, h, hc => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    obtain ⟨X₁, h₁, hc₁⟩ := pr_readNameM_run a x y hy hc
    obtain ⟨X₂, h₂, hc₂⟩ := pr_readNamesM_run xs { a with caches := { a.caches with readNC := X₁ } }
      ys hys hc₁
    refine ⟨X₂, ?_, hc₂⟩
    simp only [readNamesM, StateT.run_bind, h₁, except_ok_bind, h₂]
    rfl

/-- **The relation across the readback caches' writes.** -/
theorem CoreS.readCaches {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    (X : Std.HashMap NIdx Name) (Y : Std.HashMap LsIdx (List Level))
    (hY : ReadLsCOK { a with caches := { a.caches with readNC := X, readLsC := Y } })
    (hX : ReadNCOK { a with caches := { a.caches with readNC := X } }) :
    CoreS dn m { a with caches := { a.caches with readNC := X, readLsC := Y } } vis fe M eb :=
  ⟨hS.arena.caches_irrel _, (hS.core.readNC X).readLsC Y, hS.pins, hS.env, hS.readL, hY, hS.nwf,
    hS.erec, hS.spn, hS.memos, hS.bstk,
    hS.den.mono (LsExt.refl _) rfl rfl (fun k x hk => .inr (hX k x hk)) (fun _ _ hv => hv)
      (fun _ _ _ hv => .inl hv) (hS.den.lvlAll.congr rfl)
      (hS.den.lsAll.congr rfl), hS.mode⟩

/-! ## `residual_pw` -/

theorem pr_viewSort_ok (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h SORT) (hg : h >>> 28 = 2) :
    a.store.viewSort (decE h) = some (decI (tfld m SORT (tierW h) (idxW h) 0)) := by
  have hvs := (L.Ind.view_sort_f m a hR h hh hv hg).1
  unfold EStore.view at hvs; unfold EStore.viewSort EStore.persGetSort
  have ht : (decE h).tag = ETag.sort := by
    rw [decE_tag h hh, hg]; rfl
  have get_sort : ∀ (t : ETables) (u : LIdx), t.get (decE h) = some (.sort u) →
      t.getSort (decE h) = some u := by
    intro t u hg'
    unfold ETables.get at hg'
    rw [ht] at hg'
    simp only [show (ETag.sort == ETag.bvar) = false by decide,
      show (ETag.sort == ETag.fvar) = false by decide, show (ETag.sort == ETag.sort) = true by decide,
      ite_true, ite_false, Bool.false_eq_true] at hg'
    unfold ETables.getSort
    cases e : t.sorts.node? (decE h).idxNat with
    | none => rw [e] at hg'; cases hg'
    | some r => rw [e] at hg'; simp at hg'; simp [hg']
  split at hvs
  · rw [ite_eq_left (by assumption)]; exact get_sort _ _ hvs
  · rw [ite_eq_right (by assumption)]
    split at hvs
    · rw [ite_eq_left (by assumption)]; exact get_sort _ _ hvs
    · cases hvs

section rpw
variable {p : Prog} (hp : PropReadProg p) (hden : CoreDen)
include hp hden

/-- **`residual_pw` refines `residualPW`.** -/
theorem rpw_ok {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {fl h k o c : Word}
    (hh : fl ≠ 0 → HW h) (hW : rpwW p n m fl h = some (k, o, c, m')) :
    ∃ res, (residualPW (decOpt fl h)).run a = .ok (res, a) ∧ RdAfter dn m m' a a vis fe M eb ∧
      PWD (nameN a.store.lss.ls.ns) m' k o c res := by
  unfold rpwW at hW
  by_cases hf : fl = 0
  · simp only [hf, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    exact ⟨none, by simp [decOpt, hf, ConRon.Arena.residualPW]; rfl, RdAfter.refl hS, rfl⟩
  simp only [hf, ↓reduceIte] at hW
  have hh := hh hf
  have hR := hS.arena.1
  by_cases hg : h >>> 28 = 2
  rotate_left
  · simp only [hg, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    refine ⟨none, ?_, RdAfter.refl hS, rfl⟩
    have ht : ((decE h).tag == ETag.sort) = false := by
      rw [tag_beq_w h hh 2 (by decide) ETag.sort rfl 2 rfl]; simp [hg]
    simp [decOpt, hf, residualPW, ht]; rfl
  simp only [hg, ne_eq, not_true_eq_false, ↓reduceIte] at hW
  by_cases hv1 : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hv1] at hW
  by_cases hv2 : tcnt m SORT (tierW h) ≤ idxW h
  · simp [hv1, hv2] at hW
  simp only [hv1, hv2, ↓reduceIte] at hW
  have hvo : viewOK m h SORT := ⟨hv1, UInt64.not_le.mp hv2⟩
  obtain ⟨hview, hu⟩ := L.Ind.view_sort_f m a hR h hh hvo hg
  have hvs := pr_viewSort_ok m a hR h hh hvo hg
  generalize hw : tfld m SORT (tierW h) (idxW h) 0 = u at hW hview hu hvs
  obtain ⟨l, hl⟩ := (hden dn m a vis fe M eb hS).sort _ _ hview
  have hlv : LvR (nameN a.store.lss.ls.ns) m u l := by
    have := denoteL_lvR hR (decI u) l hl
    rwa [decI_word_self u hu] at this
  rcases hc : callW p n "lv_zero" [u] m with _ | ⟨r, m₁⟩ <;> rw [hc] at hW
  · cases hW
  obtain ⟨t, ht, -, hz⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lvZero_spec p (hp.get "lv_node") (hp.get "lh_push") (hp.get "lv_zero") n ⟨m, Locals.init []⟩ u) hc
  rw [ht] at hz
  obtain ⟨he, hZ⟩ := zeroW_ok n _ _ _ _ _ hlv hz
  have hrun : (residualPW (decOpt fl h)).run a = .ok (some (Level.zeronessOf l), a) := by
    have ht : ((decE h).tag == ETag.sort) = true := by
      rw [tag_beq_w h hh 2 (by decide) ETag.sort rfl 2 rfl]; simp [hg]
    simp only [decOpt, hf, ↓reduceIte, residualPW, ht, StateT.run_bind,
      show ∀ x, (viewSort x).run a = .ok (a.store.viewSort x, a) from fun _ => rfl, hvs,
      except_ok_bind, pr_readLevel_run a _ l hl]
    rfl
  simp only [pushedK] at hW
  rcases hZ with ⟨hx, hpw⟩ | ⟨hx, ps, hpw, hnm⟩
  · simp only [hx, ne_eq, show (1 : Word) ≠ 0 by decide, not_false_eq_true, ↓reduceIte,
      Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, -, -, rfl⟩ := hW
    refine ⟨_, hrun, RdAfter.heap hS he, ?_⟩
    rw [hpw]; rfl
  · simp only [hx, ne_eq, not_true_eq_false, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    refine ⟨_, hrun, RdAfter.heap hS he, ?_⟩
    rw [hpw]
    refine ⟨rfl, hnm, ?_⟩
    have := he.top
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
    omega

end rpw

/-! ## `subst_pw_at`: `lv_spw` over a datum on the heap -/

section spw
variable {N : Word → Name → Prop}

/-- **`lv_spw` is `bindZ.go`** with the datum's names on the heap itself (below its top; lane
`levels`' `spwW_ok` wants them elsewhere): a slice below the top survives the pushes. -/
theorem spwW_ok_lh (hN : NameRel N) {KA VA : ArrId} (hKA : KA ≠ LH ∧ KA ≠ CTL)
    (hVA : VA ≠ LH ∧ VA ≠ CTL ∧ VA < 256) (ks : List Name) (vs : List Level)
    (n : Nat) : ∀ (m m' : Mem) (po pc ko kc vo vc x : Word) (ps : List Name),
      NmsR N m LH po pc ps → po.toNat + pc.toNat ≤ (htop m).toNat →
      NmsR N m KA ko kc ks → LvsAR N m VA vo vc vs →
      spwW KA VA LH n m po pc ko kc vo vc = some (x, m') →
      HeapExt m m' ∧ ZR N m' (htop m) (htop m') x (PropWhen.bindZ.go (spwF ks vs) ps) := by
  induction n with
  | zero => intro m m' po pc ko kc vo vc x ps _ _ _ _ h; simp [spwW] at h
  | succ n ih =>
    intro m m' po pc ko kc vo vc x ps hp hb hk hv h
    cases hp with
    | nil =>
      rw [spwW_nil KA VA LH n m po 0 ko kc vo vc rfl] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨HeapExt.refl _, Or.inr ⟨rfl, [], by simp [PropWhen.bindZ.go], by simpa using NmsR.nil⟩⟩
    | @cons _ pk p ps' hp0 hpx hps =>
      rw [spwW_cons KA VA LH n m po _ ko kc vo vc hp0] at h
      have hpc1 : 1 ≤ pc.toNat := by
        rcases Nat.eq_zero_or_pos pc.toNat with e | e
        · exact absurd (UInt64.toNat_inj.mp (by simpa using e)) hp0
        · exact e
      have hd : ∃ x₁ m₁, lfK n m (rdW (m.arr64 LH) po)
          (lookupW KA VA n m ko kc vo vc (rdW (m.arr64 LH) po)) = some (x₁, m₁) ∧
          HeapExt m m₁ ∧ ZR N m₁ (htop m) (htop m₁) x₁ (spwF ks vs p) := by
        cases e : lookupW KA VA n m ko kc vo vc (rdW (m.arr64 LH) po) with
        | none => rw [e] at h; simp [lfK, spK] at h
        | some fv =>
          obtain ⟨f, v⟩ := fv
          rcases lookupW_ok hN n _ _ _ _ _ _ _ _ _ _ _ hk hv hpx e with ⟨hf, hvl⟩ | ⟨rfl, hgo⟩
          · rw [e, lfK_hit (hf := hf)] at h
            rw [lfK_hit (hf := hf)]
            cases e' : zeroW n m v with
            | none => rw [e'] at h; simp [spK] at h
            | some w =>
              obtain ⟨x₁, m₁⟩ := w
              obtain ⟨he, hz⟩ := zeroW_ok n _ _ _ _ _ hvl e'
              exact ⟨x₁, m₁, rfl, he, hz⟩
          · rw [e, lfK_miss] at h
            rw [lfK_miss]
            cases e' : lhPushW m (rdW (m.arr64 LH) po) with
            | none => rw [e'] at h; simp [pushK, spK] at h
            | some w =>
              obtain ⟨o, m₁⟩ := w
              obtain ⟨he, -, ht, hw⟩ := lhPushW_ext e'
              refine ⟨0, m₁, by rw [pushK_some], he, Or.inr ⟨rfl, [p], by simp [spwF, hgo,
                Level.zeronessOf], ?_⟩⟩
              have h1 : htop m₁ - htop m = 1 := by
                apply UInt64.toNat_inj.mp
                rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]; simp; omega
              rw [h1]
              exact .cons (by decide) (by rw [hw]; exact hpx) (by simpa using NmsR.nil)
      obtain ⟨x₁, m₁, e₁, he₁, hz₁⟩ := hd
      rw [e₁] at h
      have hpo : (po + 1).toNat = po.toNat + 1 := by
        have := (htop m).toNat_lt; rw [UInt64.toNat_add]; simp; omega
      have hpc : (pc - 1).toNat = pc.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
      rcases hz₁ with ⟨rfl, hn₁⟩ | ⟨rfl, qs, hq₁, hs₁⟩
      · rw [spK_ne (hx := by decide)] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨he₁, Or.inl ⟨rfl, by simp [PropWhen.bindZ.go, hn₁, PropWhen.inter]⟩⟩
      · rw [spK_zero] at h
        have := he₁.top
        obtain ⟨he₂, hz₂⟩ := ih _ _ _ _ _ _ _ _ _ _ (hps.mono_lh he₁ (by rw [hpo, hpc]; omega))
          (by rw [hpo, hpc]; omega) (hk.mono he₁ hKA) (hv.mono he₁ hVA) h
        refine ⟨he₁.trans he₂, ?_⟩
        have := ZR.inter hs₁ he₁.top rfl he₂ rfl hz₂
        simpa [PropWhen.bindZ.go, hq₁] using this

end spw

section spa
variable {p : Prog} (hp : PropReadProg p) (hden : CoreDen)
include hp hden

/-- **`subst_pw_at` refines `substPWAt`** at a datum, the constant's level parameters the
`EREC` slice `(lo, lc)` (their names read back), the use's level list `us` (read back). -/
theorem spa_ok {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    {lo lc us k o c k' o' c' : Word} {lps : List NIdx} {pw : PropWhen}
    (hl : hslice? (m.arr64 EREC) lo.toNat lc.toNat = some lps)
    (hks : ∃ ks, lps.mapM (denoteN a.store.ns) = some ks) (hus : HW us)
    (hls : ∃ ls, denoteLs a.store.lss (decI us) = some ls)
    (hd : PWD (nameN a.store.lss.ls.ns) m k o c (some pw))
    (hW : spaW p n m lo lc us k o c = some (k', o', c', m')) :
    ∃ res a', (substPWAt lps (decI us) pw).run a = .ok (res, a') ∧
      RdAfter dn m m' a a' vis fe M eb ∧ PWD (nameN a.store.lss.ls.ns) m' k' o' c' res := by
  unfold spaW at hW
  rcases pw with _ | ps
  · -- `never`: unchanged
    simp only [PWD] at hd; subst hd
    simp only [ne_eq, show (1 : Word) ≠ 2 by decide, not_false_eq_true, ↓reduceIte,
      Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    exact ⟨some .never, a, by simp [substPWAt]; rfl, RdAfter.refl hS, rfl⟩
  obtain ⟨rfl, hnm, hb⟩ := hd
  simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hW
  by_cases hc0 : c = 0
  · -- `ifAllZero []`: unchanged
    simp only [hc0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    have hps : ps = [] := hnm.nil_iff.mp hc0
    subst hps
    refine ⟨some (.ifAllZero []), a, by simp [substPWAt]; rfl, RdAfter.refl hS, ⟨rfl, ?_, ?_⟩⟩
    · rw [← hc0]; exact hnm
    · rw [← hc0]; exact hb
  simp only [hc0, ↓reduceIte] at hW
  obtain ⟨x₀, ps₀, rfl⟩ : ∃ x xs, ps = x :: xs := by
    cases ps with
    | nil => exact absurd (hnm.nil_iff.mpr rfl) hc0
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hR := hS.arena.1
  have hN := nameN_rel _ hS.nwf
  have hSD := hden dn m a vis fe M eb hS
  obtain ⟨ks, hk⟩ := hks
  obtain ⟨vs, hv⟩ := hls
  -- the arguments' slice
  obtain ⟨ids, hvw, hdl⟩ := denoteLs_view a (decI us) vs hv
  obtain ⟨e₁, t₁, s₁⟩ := lsNodeW_store hR hus hvw
  rw [e₁] at hW
  simp only [List.cons_ne_nil, ↓reduceIte, List.headD_cons, List.tail_cons] at hW
  have htop := m.top.toNat_lt
  have h41 := hR.lit.1.top41
  have hvs := (lvsR_of_slice hR ids vs _ _ s₁ (by omega) hdl).toAR
  -- the keys
  have hbound : lo.toNat + lc.toNat < 2 ^ 64 := by
    have := hS.erec
    rcases hslice?_bound_fsz _ _ _ _ hl with h0 | h0
    · have := lo.toNat_lt; omega
    · omega
  have hkr : NmsR (nameN a.store.lss.ls.ns) m EREC lo lc ks :=
    nmsR_of_hslice _ _ lc.toNat lps ks lo lc rfl hl hbound hk
  -- the run
  rcases hc : callW p n "lv_spw" [o, c, lo, lc, tfld m LVLS (tierW us) (idxW us) 0,
      tfld m LVLS (tierW us) (idxW us) 1] m with _ | ⟨r, m₁⟩
  · rw [hc] at hW; cases hW
  rw [hc] at hW
  obtain ⟨t, ht, -, hz⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lvSpw_spec EREC POOL LH p (hp.get "lv_lookup") (hp.get "lv_node") (hp.get "lh_push") (hp.get "lv_zero") (hp.get "lv_spw") n ⟨m, Locals.init []⟩ _ _ _ _ _ _)
    hc
  rw [ht] at hz
  obtain ⟨he, hZ⟩ := spwW_ok_lh hN (by decide) (by decide) ks vs n _ _ _ _ _ _ _ _ _ _ hnm hb hkr
    hvs hz
  -- the twin
  obtain ⟨X, hX, hcX⟩ := pr_readNamesM_run lps a ks hk hSD.readN
  obtain ⟨Y, hY, hcY⟩ := readLevelsM_run' { a with caches := { a.caches with readNC := X } }
    (decI us) vs hv (by exact hS.readLs)
  have hrun : (substPWAt lps (decI us) (.ifAllZero (x₀ :: ps₀))).run a =
      .ok (some (Level.substPW ks vs (.ifAllZero (x₀ :: ps₀))),
        { a with caches := { a.caches with readNC := X, readLsC := Y } }) := by
    simp only [substPWAt, StateT.run_bind, hX, except_ok_bind, hY]
    rfl
  have hS' : CoreS dn m₁ { a with caches := { a.caches with readNC := X, readLsC := Y } } vis fe
      M eb := (CoreS.readCaches ((RdAfter.heap hS he).1) X Y (by exact hcY) hcX)
  have hRd : RdAfter dn m m₁ a { a with caches := { a.caches with readNC := X, readLsC := Y } }
      vis fe M eb := ⟨hS', (RdAfter.heap hS he).2.1, (RdAfter.heap hS he).2.2.1, rfl⟩
  simp only [pushedK] at hW
  rcases hZ with ⟨hx, hpw⟩ | ⟨hx, qs, hpw, hq⟩
  · simp only [hx, ne_eq, show (1 : Word) ≠ 0 by decide, not_false_eq_true, ↓reduceIte,
      Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, -, -, rfl⟩ := hW
    refine ⟨_, _, hrun, hRd, ?_⟩
    show PWD _ _ _ _ _ (some (Level.substPW ks vs (.ifAllZero (x₀ :: ps₀))))
    rw [show Level.substPW ks vs (.ifAllZero (x₀ :: ps₀)) =
      PropWhen.bindZ.go (spwF ks vs) (x₀ :: ps₀) from rfl, hpw]
    rfl
  · simp only [hx, ne_eq, not_true_eq_false, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    refine ⟨_, _, hrun, hRd, ?_⟩
    show PWD _ _ _ _ _ (some (Level.substPW ks vs (.ifAllZero (x₀ :: ps₀))))
    rw [show Level.substPW ks vs (.ifAllZero (x₀ :: ps₀)) =
      PropWhen.bindZ.go (spwF ks vs) (x₀ :: ps₀) from rfl, hpw]
    refine ⟨rfl, hq, ?_⟩
    have := he.top
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
    omega

end spa

end L.Arena
