import ConAgua.Front.IndApplySpec
import ConRon.Arena.Frontend.ExportC
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The apply step of an `inductive` line against the twin, I: the leaves

The models of `IndApplySpec.lean` against con-ron's `validateIndD` helpers: the telescope walks
(`piResW_ok`, `teleW_ok`, `sortTeleW_ok`: `piResultD`, `indPiTeleLen`, `piSortTeleLen?` at the
fuel word's value, every step a `view`, `eViewW_ok`), `name_rec_pre` (`nrpW_ok`: `viewN`), the
store's fuel (`storeFuelW_eq`: `nodeCount + 1`), the table lookups (`lkW_name`, `lkW_expr`).
Every twin run is read-only: it ends in the state it starts from.
-/

open L.Arena
open L.Ind (eViewW eViewW_ok ViewR)
open ConRon.Arena
open ConRon.Arena.Frontend


namespace L.Front.Ind

/-! ## Runs -/

theorem run_pure {α : Type} (x : α) (a : AState) : (pure x : AM α).run a = .ok (x, a) := rfl

theorem run_bind {α β : Type} (x : AM α) (f : α → AM β) (a : AState) (y : α)
    (h : x.run a = .ok (y, a)) : (x >>= f).run a = (f y).run a := by
  simp only [StateT.run_bind, h]; rfl

/-- A read-only `mapM`: every element's run returns its image and keeps the state. -/
theorem mapM_run {α β : Type} (f : α → AM β) (g : α → β) (a : AState) :
    ∀ (xs : List α), (∀ x ∈ xs, (f x).run a = .ok (g x, a)) →
      (xs.mapM f).run a = .ok (xs.map g, a)
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons, List.map_cons]
    rw [run_bind _ _ a _ (h x (by simp)), run_bind _ _ a _ (mapM_run f g a xs fun y hy => h y (by simp [hy]))]
    rfl

/-- A read-only `forIn` that yields at every element: the states `S i`. -/
theorem forIn_yield {α β : Type} (f : α → β → AM (ForInStep β)) (a : AState) (xs : List α)
    (S : Nat → β) (h : ∀ i (hi : i < xs.length), (f xs[i] (S i)).run a = .ok (.yield (S (i + 1)), a)) :
    (forIn xs (S 0) f).run a = .ok (S xs.length, a) := by
  induction xs generalizing S with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons]
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [run_bind _ _ a _ h0]
    have := ih (fun i => S (i + 1)) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa using this)
    simpa using this

/-! ## Views -/

theorem getD2 (l : List Word) : l.getD 2 0 = l.tail.tail.headD 0 := by
  rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

theorem getD1 (l : List Word) : l.getD 1 0 = l.tail.headD 0 := by
  rcases l with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl

/-- The view of a handle the L code views. -/
theorem view_ok' (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hne : eViewW m h ≠ []) :
    ∃ v, (view (decE h)).run a = .ok (v, a) ∧ ViewR (eViewW m h) v := by
  obtain ⟨v, hv, hr⟩ := eViewW_ok m a hR h hne
  exact ⟨v, view_run _ a v hv, hr⟩

/-- The tag word of a view. -/
def tagOf : ENodeView → Word
  | .bvar _ => 0 | .fvar _ _ => 1 | .sort _ => 2 | .const _ _ => 3 | .app _ _ => 4
  | .lam _ _ => 5 | .forallE _ _ => 6 | .letE _ _ _ => 7 | .lit _ => 8 | .proj _ _ _ => 9

theorem viewR_head {r : List Word} {v : ENodeView} (h : ViewR r v) : r.headD 0 = tagOf v := by
  cases v <;> simp only [ViewR] at h <;> first | exact h.1 | exact h

theorem viewR_forall {r : List Word} {v : ENodeView} (h : ViewR r v) (h6 : r.headD 0 = 6) :
    ∃ ty, v = .forallE ty (decE (r.tail.tail.headD 0)) := by
  have ht := viewR_head h
  rw [h6] at ht
  cases v <;> simp only [tagOf] at ht <;> (try exact absurd ht (by decide))
  simp only [ViewR] at h
  exact ⟨_, by rw [← getD2, h.2.2.2.2]⟩

theorem viewR_sort {r : List Word} {v : ENodeView} (h : ViewR r v) (h2 : r.headD 0 = 2) :
    v = .sort (decI (r.tail.headD 0)) ∧ (r.tail.headD 0).toNat < 2 ^ 32 := by
  have ht := viewR_head h
  rw [h2] at ht
  cases v <;> simp only [tagOf] at ht <;> (try exact absurd ht (by decide))
  simp only [ViewR] at h
  exact ⟨by rw [← getD1, h.2.2], by rw [← getD1]; exact h.2.1⟩

theorem fuel_pred {f : Word} (hf : ¬ f = 0) : f.toNat = (f - 1).toNat + 1 := by
  have : f.toNat ≠ 0 := fun h0 => hf (UInt64.toNat_inj.mp (by simpa using h0))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

/-! ## The telescope walks -/

section tele
variable (m : Mem) (a : AState) (hR : ArenaR m a)
include hR

@[refines ConRon.Arena.Frontend.piResultD]
theorem piResW_ok : ∀ (n : Nat) (f h r : Word), piResW n m f h = some r →
    (ConRon.Arena.Frontend.piResultD f.toNat (decE h)).run a = .ok (decE r, a) := by
  intro n
  induction n with
  | zero => intro f h r hw; simp [piResW] at hw
  | succ n ih =>
    intro f h r hw
    simp only [piResW] at hw
    split at hw; cases hw; rename_i hf
    split at hw; cases hw; rename_i hne
    obtain ⟨v, hv, hr⟩ := view_ok' m a hR h hne
    rw [fuel_pred hf, ConRon.Arena.Frontend.piResultD, run_bind _ _ a _ hv]
    split at hw
    · rename_i h6
      obtain ⟨ty, rfl⟩ := viewR_forall hr h6
      exact ih _ _ _ hw
    · rename_i h6
      cases hw
      cases v <;> (try rfl)
      exact absurd (viewR_head hr) h6

@[refines ConRon.Arena.Frontend.indPiTeleLen]
theorem teleW_ok : ∀ (n : Nat) (f h r : Word), teleW n m f h = some r →
    (ConRon.Arena.Frontend.indPiTeleLen f.toNat (decE h)).run a = .ok (r.toNat, a) ∧
      r.toNat < f.toNat := by
  intro n
  induction n with
  | zero => intro f h r hw; simp [teleW] at hw
  | succ n ih =>
    intro f h r hw
    simp only [teleW] at hw
    split at hw; cases hw; rename_i hf
    split at hw; cases hw; rename_i hne
    obtain ⟨v, hv, hr⟩ := view_ok' m a hR h hne
    have hf1 := fuel_pred hf
    rw [hf1, ConRon.Arena.Frontend.indPiTeleLen, run_bind _ _ a _ hv]
    split at hw
    · rename_i h6
      obtain ⟨ty, rfl⟩ := viewR_forall hr h6
      rcases hrec : teleW n m (f - 1) ((eViewW m h).tail.tail.headD 0) with _ | r' <;> simp only [hrec, teleK, reduceCtorEq] at hw
      cases hw
      obtain ⟨h1, h2⟩ := ih _ _ _ hrec
      simp only
      rw [run_bind _ _ a _ h1]
      have hlt : (f - 1).toNat < 2 ^ 64 := UInt64.toNat_lt _
      have : (r' + 1).toNat = r'.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      exact ⟨by rw [this]; rfl, by omega⟩
    · rename_i h6
      cases hw
      refine ⟨?_, by simp only [UInt64.toNat_zero]; omega⟩
      cases v <;> (try rfl)
      exact absurd (viewR_head hr) h6

@[refines ConRon.Arena.piSortTeleLen?]
theorem sortTeleW_ok : ∀ (n : Nat) (f h ok r : Word), sortTeleW n m f h = some (ok, r) →
    (piSortTeleLen? f.toNat (decE h)).run a =
      .ok ((if ok = 0 then none else some r.toNat), a) ∧ r.toNat < f.toNat := by
  intro n
  induction n with
  | zero => intro f h ok r hw; simp [sortTeleW] at hw
  | succ n ih =>
    intro f h ok r hw
    simp only [sortTeleW] at hw
    split at hw; cases hw; rename_i hf
    split at hw; cases hw; rename_i hne
    obtain ⟨v, hv, hr⟩ := view_ok' m a hR h hne
    have hf1 := fuel_pred hf
    rw [hf1, piSortTeleLen?, run_bind _ _ a _ hv]
    split at hw
    · rename_i h6
      obtain ⟨ty, rfl⟩ := viewR_forall hr h6
      rcases hrec : sortTeleW n m (f - 1) ((eViewW m h).tail.tail.headD 0) with _ | ⟨ok', r'⟩ <;> simp only [hrec, stK, reduceCtorEq] at hw
      obtain ⟨h1, h2⟩ := ih _ _ _ _ hrec
      simp only
      rw [run_bind _ _ a _ h1]
      by_cases hok : ok' = 0
      · rw [ite_eq_left hok] at hw
        cases hw
        simp only [hok, ite_true, Option.map_none]
        exact ⟨rfl, by simp⟩
      · rw [ite_eq_right hok] at hw
        cases hw
        have : (r' + 1).toNat = r'.toNat + 1 := by
          rw [UInt64.toNat_add]; simp; have := UInt64.toNat_lt (f - 1); omega
        simp only [hok, ite_false, Option.map_some, this, show (1 : Word) ≠ 0 by decide]
        exact ⟨rfl, by omega⟩
    · rename_i h6
      split at hw
      · rename_i h2
        cases hw
        refine ⟨?_, by simp only [UInt64.toNat_zero]; omega⟩
        rw [(viewR_sort hr h2).1]
        rfl
      · rename_i h2
        cases hw
        refine ⟨?_, by simp only [UInt64.toNat_zero]; omega⟩
        cases v <;> (try rfl)
        · exact absurd (viewR_head hr) h2
        · exact absurd (viewR_head hr) h6

end tele


/-! ## The store's fuel -/

/-- The sum of `c` words of `CTL` from `k`. -/
def csum (m : Mem) (k : Word) : Nat → Word
  | 0 => 0
  | c + 1 => rdW (m.arr64 CTL) k + csum m (k + 1) c

theorem ctlSumW_eq : ∀ (n : Nat) (m : Mem) (k c s : Word), ctlSumW n m k c = some s → s = csum m k c.toNat := by
  intro n
  induction n with
  | zero => intro m k c s h; simp [ctlSumW] at h
  | succ n ih =>
    intro m k c s h
    simp only [ctlSumW] at h
    split at h
    · cases h; rename_i hc; subst hc; rfl
    · rename_i hc
      rcases hr : ctlSumW n m (k + 1) (c - 1) with _ | r <;> simp only [hr, addK, reduceCtorEq] at h
      cases h
      rw [ih _ _ _ _ hr, fuel_pred hc]
      rfl

/-- **`store_fuel` is the twin's `storeFuel`**: the store's node count `+ 1`. -/
@[refines ConRon.Arena.Frontend.storeFuel]
theorem storeFuelW_ok {m : Mem} {a : AState} (hR : ArenaR m a) {n : Nat} {f : Word}
    (h : storeFuelW n m = some f) : f.toNat = a.store.nodeCount + 1 := by
  cases n with
  | zero => simp [storeFuelW] at h
  | succ n =>
  simp only [storeFuelW] at h
  cases h1 : ctlSumW n m 2 4 with
  | none => rw [h1] at h; cases h
  | some x =>
  cases h2 : ctlSumW n m 16 8 with
  | none => rw [h1, h2] at h; cases h
  | some y =>
  cases h3 : ctlSumW n m 26 8 with
  | none => rw [h1, h2, h3] at h; cases h
  | some z =>
  rw [h1, h2, h3] at h
  simp only [sfK, Option.some.injEq] at h
  subst h
  rw [ctlSumW_eq _ _ _ _ _ h1, ctlSumW_eq _ _ _ _ _ h2, ctlSumW_eq _ _ _ _ _ h3]
  obtain ⟨a1, a2, a3, a4⟩ := ConsR.sizes hR.lit.2
  obtain ⟨b1, b2, b3, b4⟩ := ConsR.sizes hR.app
  obtain ⟨c1, c2, c3, c4⟩ := ConsR.sizes hR.sort
  obtain ⟨d1, d2, d3, d4⟩ := ConsR.sizes hR.const
  obtain ⟨e1, e2, e3, e4⟩ := ConsR.sizes hR.letE
  obtain ⟨f1, f2, f3, f4⟩ := ConsR.sizes hR.bvar
  obtain ⟨g1, g2, g3, g4⟩ := ConsR.sizes hR.fvar
  obtain ⟨h1', h2', h3', h4'⟩ := ConsR.sizes hR.lam
  obtain ⟨i1, i2, i3, i4⟩ := ConsR.sizes hR.forallE
  obtain ⟨j1, j2, j3, j4⟩ := ConsR.sizes hR.proj
  simp only [litCS, litCSk, appCS, sortCS, constCS, letCS, bvarCS, fvarCS, lamCS, forallCS,
    projCS] at a1 a3 b1 b3 c1 c3 d1 d3 e1 e3 f1 f3 g1 g3 h1' h3' i1 i3 j1 j3
  simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount, ETables.count, Tbl.size] at *
  simp only [csum, show (4 : Word).toNat = 4 from rfl, show (8 : Word).toNat = 8 from rfl]
  simp only [UInt64.reduceAdd] at a1 a3 b1 b3 c1 c3 d1 d3 e1 e3 f1 f3 g1 g3 h1' h3' i1 i3 j1 j3 ⊢
  simp only [UInt64.toNat_add, UInt64.toNat_zero, UInt64.toNat_one] at *
  omega


/-! ## Names: `name_rec_pre` against `viewN` -/

theorem decN_tag (h : Word) (hh : h.toNat < 2 ^ 32) :
    (decI h : NIdx).tag = (h >>> 28).toUInt32 := by
  simp only [decI, Idx.tag]
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_div, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem decN_idx (h : Word) : (decI h : NIdx).idxNat = (idxW h).toNat := by
  simp only [decI, Idx.idxNat, Idx.index, idxW]
  simp [UInt32.toNat_mod, UInt64.toNat_toUInt32, UInt64.toNat_and]
  have : (134217727 : Nat) = 2 ^ 27 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-- Under the scratch check, the name store's view reads the tier the handle's bit names. -/
theorem nview_tier {m : Mem} {a : AState} (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) :
    a.store.lss.ls.ns.view (decI h) =
      (if tierW h = 0 then a.store.lss.ls.ns.pers else a.store.lss.ls.ns.scr).get (decI h) := by
  have hfl := ConsR.flag hR.nstr
  unfold NStore.view
  rw [isPersistent_decI h hh]
  by_cases ht : tierW h = 0
  · simp [tierW] at ht; simp [ht, tierW]
  · have hon : a.store.lss.ls.ns.scratchOn = true := by
      rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hv ⟨ht, h1⟩
    simp only [tierW] at ht
    simp [ht, hon, tierW]

theorem shr28_lt (h : Word) (hh : h.toNat < 2 ^ 32) : (h >>> 28).toNat < 16 := by
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; omega

theorem viewN_run {a : AState} {h : NIdx} {v : NNodeView} (hv : a.store.ns.view h = some v) :
    (viewN h).run a = .ok (v, a) := by
  simp only [EStore.ns] at hv
  rw [show (viewN h).run a = (match a.store.lss.ls.ns.view h with
    | some v => (pure v : AM NNodeView)
    | none => fail (.internal "arena: dangling name handle")).run a from rfl, hv]
  rfl

/-- A word read at `o + k` without overflow. -/
theorem rdW_add (p : Array Word) (o k : Word) (h : o.toNat + k.toNat < 2 ^ 64) :
    rdW p (o + k) = p[o.toNat + k.toNat]?.getD 0 := by
  simp only [rdW, UInt64.toNat_add]; congr 2; omega

theorem strWords_rec : strWords "rec" = [114, 101, 99] := by decide

theorem sliceL_three (p : Array Word) (o : Nat) :
    sliceL p o 3 = [p[o]?.getD 0, p[o + 1]?.getD 0, p[o + 2]?.getD 0] := by
  simp [sliceL, List.ofFn_succ]

/-- **`name_rec_pre` refines `viewN`, matched against `.str T "rec"`.** -/
@[refines_part ConRon.Arena.viewN "matched against `.str T \"rec\"` (name_rec_pre)"]
theorem nrpW_ok {m : Mem} {a : AState} (hR : ArenaR m a) (w f T : Word) (h : nrpW m w = some (f, T)) :
    ∃ v, (viewN (decI w)).run a = .ok (v, a) ∧ (f ≠ 0 → v = .str (decI T) "rec" ∧ T.toNat < 2 ^ 32) ∧
      (f = 0 → ∀ T', v ≠ .str T' "rec") := by
  unfold nrpW at h
  split at h; cases h; rename_i hb
  have hw : w.toNat < 2 ^ 32 := by
    have : ¬ (4294967295 : Nat) < w.toNat := hb
    omega
  split at h; cases h; rename_i hs
  have hv := nview_tier hR w hw hs
  have ht1 : tierW w ≤ 1 := tierW_le w
  split at h
  · -- anonymous
    rename_i hg
    split at h; cases h; rename_i hc
    cases h
    obtain ⟨x, hx, -⟩ := ConsR.node hR.nanon (tierW w) ht1 (idxW w)
      (UInt64.not_le.mp hc)
    refine ⟨.anonymous, viewN_run ?_, by simp, by simp⟩
    rw [EStore.ns, hv, NTables.get, decN_tag w hw, hg]
    simp only [NTag.anonymous, decN_idx, Tbl.node?]
    by_cases ht : tierW w = 0
    · rw [ite_eq_left ht] at hx; simp [ht, hx]
    · rw [ite_eq_right ht] at hx; simp [ht, hx]
  split at h
  · -- num
    rename_i hg0 hg
    split at h; cases h; rename_i hc
    cases h
    obtain ⟨x, hx, -⟩ := ConsR.node hR.nnum (tierW w) ht1 (idxW w)
      (UInt64.not_le.mp hc)
    refine ⟨.num x.pre x.n, viewN_run ?_, by simp, by simp⟩
    rw [EStore.ns, hv, NTables.get, decN_tag w hw, hg]
    simp only [NTag.anonymous, NTag.str, NTag.num, decN_idx, Tbl.node?]
    by_cases ht : tierW w = 0
    · rw [ite_eq_left ht] at hx; simp [ht, hx]
    · rw [ite_eq_right ht] at hx; simp [ht, hx]
  split at h; cases h; rename_i hg0 hg2 hg1
  have hg : w >>> 28 = 1 := by simpa using hg1
  split at h; cases h; rename_i hc
  obtain ⟨x, hx, hrel⟩ := ConsR.node hR.nstr (tierW w) ht1 (idxW w)
    (UInt64.not_le.mp hc)
  have hview : (viewN (decI w)).run a = .ok (.str x.pre x.s, a) := by
    apply viewN_run
    rw [EStore.ns, hv, NTables.get, decN_tag w hw, hg]
    simp only [NTag.anonymous, NTag.str, decN_idx, Tbl.node?]
    by_cases ht : tierW w = 0
    · rw [ite_eq_left ht] at hx; simp [ht, hx]
    · rw [ite_eq_right ht] at hx; simp [ht, hx]
  obtain ⟨hq, hol, hsl, -⟩ := hrel
  have hlen := sliceL_length (vpool m) (tfld m NSTR (tierW w) (idxW w) 1).toNat
    (tfld m NSTR (tierW w) (idxW w) 2).toNat
  rw [hsl] at hlen
  have htop := UInt64.toNat_lt m.top
  unfold nrpStr at h
  generalize ho : tfld m NSTR (tierW w) (idxW w) 1 = o at hol hsl hlen h
  generalize hlw : tfld m NSTR (tierW w) (idxW w) 2 = lw at hol hsl hlen h
  have h41 := hR.lit.1.top41
  have hol' : o.toNat + lw.toNat ≤ m.top.toNat := hol.1.1
  have e1 : lw.toNat = 3 → prd m (o + 1) = (vpool m)[o.toNat + 1]?.getD 0 :=
    fun h3 => by
      have e : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      rw [← e, vpool_getD m _ (by omega)]
  have e2 : lw.toNat = 3 → prd m (o + 2) = (vpool m)[o.toNat + 2]?.getD 0 :=
    fun h3 => by
      have e : (o + 2).toNat = o.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
      rw [← e, vpool_getD m _ (by omega)]
  have e0 : prd m o = (vpool m)[o.toNat]?.getD 0 := by rw [vpool_getD m o (by omega)]
  refine ⟨_, hview, ?_, ?_⟩
  · intro hf
    split at h
    · cases h; exact absurd rfl hf
    rename_i h3
    split at h
    · rename_i hrec
      cases h
      have hl3 : lw.toNat = 3 := by
        have : lw = 3 := by simpa using h3
        rw [this]; rfl
      rw [hl3, sliceL_three] at hsl
      obtain ⟨r1, r2, r3⟩ := hrec
      rw [e0] at r1; rw [e1 hl3] at r2; rw [e2 hl3] at r3
      rw [r1, r2, r3, ← strWords_rec] at hsl
      rw [strWords_inj _ _ hsl.symm, hq, decI_word]
      exact ⟨rfl, word_lt _⟩
    · cases h; exact absurd rfl hf
  · intro hf T' heq
    simp only [NNodeView.str.injEq] at heq
    obtain ⟨-, hs'⟩ := heq
    rw [hs', strWords_rec] at hlen hsl
    simp only [List.length_cons, List.length_nil] at hlen
    split at h
    · rename_i h3
      exact h3 (UInt64.toNat_inj.mp (by simp; omega))
    split at h
    · cases h; exact absurd hf (by decide)
    rename_i h3 hrec
    apply hrec
    rw [← hlen, sliceL_three] at hsl
    simp only [List.cons.injEq] at hsl
    obtain ⟨s1, s2, s3, -⟩ := hsl
    rw [e0, e1 hlen.symm, e2 hlen.symm]
    exact ⟨s1, s2, s3⟩

end L.Front.Ind
