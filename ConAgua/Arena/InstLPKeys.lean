module

public import ConAgua.Arena.InstLP
import ConAgua.Arena.LevelInternRef
import ConAgua.Arena.TwinStep
import Std.Tactic.BVDecide.Normalize.BitVec
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConRon.Bridge.Grind
public import ConAgua.Arena.LevelApd
import all ConAgua.Arena.InstLP
import ConAgua.L.WordOff

@[expose] public section

/-!
# `keys_ok`: the substitution's keys are stored names

The twin reads the keys back (`readNamesM`), which fails on a handle that does not view. L
checks each key word on the spine stack (`keys_ok`, past the cut-off, where the twin reads them):
a name handle (tag below `3`, the scratch tier open, the index below the tier's count). Under
`ArenaR` such a handle views (`viewN_anon`/`str`/`num`), and under the name store's
well-formedness (`CoreS.nwf`) a viewing handle reads back (con-ron's `denoteN_of_view`).
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **The model of `keys_ok`**: `some ()` where every key word is a name handle. -/
def keysOkW : Nat → Mem → Word → Word → Option Unit
  | 0, _, _, _ => none
  | n + 1, m, o, l =>
    if l = 0 then some ()
    else if 4294967296 ≤ rdW (m.arr64 SPN) o then none
    else if tierW (rdW (m.arr64 SPN) o) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if (3 : Word) ≤ tagW (rdW (m.arr64 SPN) o) then none
    else if nameCnt m (tagW (rdW (m.arr64 SPN) o)) (tierW (rdW (m.arr64 SPN) o)) ≤
        idxW (rdW (m.arr64 SPN) o) then none
    else keysOkW n m (o + 1) (l - 1)

@[arena_grind =] theorem keysOkW_succ (n : Nat) (m : Mem) (o l : Word) :
    keysOkW (n + 1) m o l =
      if l = 0 then some ()
      else if 4294967296 ≤ rdW (m.arr64 SPN) o then none
      else if tierW (rdW (m.arr64 SPN) o) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
      else if (3 : Word) ≤ tagW (rdW (m.arr64 SPN) o) then none
      else if nameCnt m (tagW (rdW (m.arr64 SPN) o)) (tierW (rdW (m.arr64 SPN) o)) ≤
          idxW (rdW (m.arr64 SPN) o) then none
      else keysOkW n m (o + 1) (l - 1) := rfl

theorem keysOk_spec (p : Prog) (hk : p.lookup "keys_ok" = some keysOk) (n : Nat) :
    ∀ (s₀ : St) (o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "keys_ok" [o, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ keysOkW n s₀.mem o l = some (); ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l; rw [invoke_eq _ hk]; simp only [callFn, keysOk]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l
    rw [invoke_eq _ hk]
    simp only [callFn, keysOk]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE, ih] <;>
      finish [tierW, idxW, nameCnt]

/-! ## A name handle's view (the scratch tier open: con-ron's `viewN` reads the tier it names) -/

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
  · simp only [show (h >>> 31) &&& 1 = tierW h from rfl, ht, beq_self_eq_true, ↓reduceIte]
  · have hon : a.store.lss.ls.ns.scratchOn = true := by
      rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun e => hv ⟨ht, e⟩
    simp only [show (h >>> 31) &&& 1 = tierW h from rfl, beq_iff_eq, ht, ↓reduceIte, hon]

omit hR hh hv in
theorem viewN_run {v : NNodeView} (hw : a.store.lss.ls.ns.view (decI h) = some v) :
    (viewN (decI h)).run a = .ok (v, a) := by
  simp only [viewN, EStore.ns, StateT.run_bind, StateT.run_get, pure_bind, hw]; rfl

/-- The scratch view of an `anonymous` record. -/
theorem viewN_anon (hg : tagW h = 0) (hc : ¬ tcnt m NANON (tierW h) ≤ idxW h) :
    (viewN (decI h)).run a = .ok (.anonymous, a) := by
  apply viewN_run
  rw [nview_tier hR hh hv]
  have e0 : ((decI h : NIdx).tag = 0) := (decI_tag_eq h hh 0 (by decide)).mpr (by rw [hg]; rfl)
  obtain ⟨x, hx, -⟩ := ConsR.node hR.nanon (tierW h) (tierW_le h)
    (idxW h) (UInt64.not_le.mp hc)
  simp only [NTables.get, e0, NTag.anonymous, beq_self_eq_true, ↓reduceIte, Tbl.node?,
    decI_idx h (narrow_of_tagW h (by rw [hg]; decide)), apply_ite NTables.anons, hx, Option.map_some]

/-- The scratch view of a `str` record: its prefix word and a slice holding the string. -/
theorem viewN_str (hg : tagW h = 1) (hc : ¬ tcnt m NSTR (tierW h) ≤ idxW h) :
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
    Tbl.node?, decI_idx h (narrow_of_tagW h (by rw [hg]; decide)), apply_ite NTables.strs, hx, Option.map_some, hq, decI_word]

/-- The scratch view of a `num` record. -/
theorem viewN_num (hg : tagW h = 2) (hc : ¬ tcnt m NNUM (tierW h) ≤ idxW h) :
    ∃ v, (viewN (decI h)).run a = .ok (v, a) := by
  have e2 : ((decI h : NIdx).tag = 2) := (decI_tag_eq h hh 2 (by decide)).mpr (by rw [hg]; rfl)
  obtain ⟨x, hx, -⟩ := ConsR.node hR.nnum (tierW h) (tierW_le h)
    (idxW h) (UInt64.not_le.mp hc)
  suffices hw' : ∃ v, a.store.lss.ls.ns.view (decI h) = some v from
    hw'.elim fun v e => ⟨v, viewN_run e⟩
  rw [nview_tier hR hh hv]
  have hne0 : ((2 : UInt32) == NTag.anonymous) = false := by decide
  have hne1 : ((2 : UInt32) == NTag.str) = false := by decide
  simp only [NTables.get, e2, hne0, hne1, NTag.num, beq_self_eq_true, Bool.false_eq_true,
    ↓reduceIte, Tbl.node?, decI_idx h (narrow_of_tagW h (by rw [hg]; decide)), apply_ite NTables.nums, hx,
    Option.map_some]
  exact ⟨_, rfl⟩

end view

/-- A name handle that views reads back. -/
theorem viewN_den {a : AState} (hwf : NStoreWF a.store.lss.ls.ns) {h : NIdx} {v : NNodeView} {a' : AState}
    (hr : (viewN h).run a = .ok (v, a')) : ∃ x, denoteN a.store.lss.ls.ns h = some x := by
  obtain ⟨rk, hrk⟩ := hwf
  apply denoteN_of_viewW hrk _ _ (Nat.lt_succ_self _)
  simp only [viewN, StateT.run_bind, StateT.run_get, pure_bind, EStore.ns] at hr
  revert hr
  cases e : a.store.lss.ls.ns.view h with
  | none =>
    intro hr
    simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift, Functor.map,
      Except.map] at hr
  | some w => intro _; rfl

/-- **The checked keys read back**: their handles' names, as the twin's `readNamesM` needs them,
and the stack slice related to them (`ILWEnv.keys`). -/
theorem keysOkW_names {m : Mem} {a : AState} (hR : ArenaR m a) (hwf : NStoreWF a.store.lss.ls.ns) :
    ∀ (n : Nat) (o l : Word) (lps : List NIdx), keysOkW n m o l = some () →
      hslice? (aread (m.arr64 SPN)) o.toNat l.toNat = some lps → o.toNat + l.toNat < 2 ^ 64 →
      ∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks ∧ NmsR (nameN a.store.lss.ls.ns) m SPN o l ks := by
  intro n
  induction n with
  | zero => intro o l lps hk; simp [keysOkW] at hk
  | succ n ih =>
    intro o l lps hk hs hb
    rw [keysOkW_succ] at hk
    by_cases hl : l = 0
    · subst hl
      simp only [UInt64.toNat_zero, hslice?, List.range_zero, List.mapM_nil, Option.pure_def,
        Option.some.injEq] at hs
      subst hs
      exact ⟨[], rfl, .nil⟩
    rw [ite_eq_right hl] at hk
    generalize hw : rdW (m.arr64 SPN) o = w at hk
    obtain ⟨h1, hk⟩ := of_ite_none hk
    obtain ⟨h2, hk⟩ := of_ite_none hk
    obtain ⟨h3, hk⟩ := of_ite_none hk
    obtain ⟨h4, hk⟩ := of_ite_none hk
    have hww : w.toNat < 2 ^ 32 := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h1); simpa using this
    -- the key reads back
    have hx : ∃ x, denoteN a.store.lss.ls.ns (decI w) = some x := by
      have hg : tagW w = 0 ∨ tagW w = 1 ∨ tagW w = 2 := by
        have : (tagW w).toNat < 3 := by
          have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h3); simpa using this
        have e : ∀ k : Nat, k < 3 → (tagW w).toNat = k → tagW w = k.toUInt64 := fun k _ e =>
          UInt64.toNat_inj.mp (by rw [e]; simp; omega)
        rcases (by omega : (tagW w).toNat = 0 ∨ (tagW w).toNat = 1 ∨ (tagW w).toNat = 2) with
          e0 | e0 | e0
        · exact .inl (e 0 (by omega) e0)
        · exact .inr (.inl (e 1 (by omega) e0))
        · exact .inr (.inr (e 2 (by omega) e0))
      rcases hg with hg | hg | hg
      · rw [hg] at h4
        exact viewN_den hwf (viewN_anon hR hww h2 hg (by simpa [nameCnt] using h4))
      · rw [hg] at h4
        obtain ⟨s, hr, -⟩ := viewN_str hR hww h2 hg (by simpa [nameCnt] using h4)
        exact viewN_den hwf hr
      · rw [hg] at h4
        obtain ⟨_, hr⟩ := viewN_num hR hww h2 hg (by simpa [nameCnt] using h4)
        exact viewN_den hwf hr
    obtain ⟨x, hx⟩ := hx
    -- the rest
    have hl1 : 1 ≤ l.toNat := by
      rcases Nat.eq_zero_or_pos l.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hl
      · omega
    obtain ⟨j, hj⟩ : ∃ j, l.toNat = j + 1 := ⟨l.toNat - 1, by omega⟩
    rw [hj, lp_hslice_succ] at hs
    simp only [Option.bind_eq_bind] at hs
    cases ehd : (hd? (aread (m.arr64 SPN)) o.toNat : Option NIdx) with
    | none => simp [ehd] at hs
    | some x0 =>
    have hx0 : x0 = decI w := by
      simp only [hd?, aread_apply] at ehd
      cases ew : (m.arr64 SPN)[o.toNat]? with
      | none => simp [ew] at ehd
      | some v =>
        have hv : v = w := by rw [← hw]; simp [rdW, ew]
        subst hv
        have hvv : v.toNat < 2 ^ 32 := hww
        simp only [ew, hvv, Option.bind_eq_bind, Option.bind_some, ite_true, Option.some.injEq] at ehd
        grind
    subst hx0
    rw [ehd] at hs
    cases e' : (hslice? (aread (m.arr64 SPN)) (o.toNat + 1) j : Option (List NIdx)) with
    | none => simp [e'] at hs
    | some xs =>
    simp only [e', Option.bind_some, Option.pure_def, Option.some.injEq] at hs
    subst hs
    have ho1 : (o + 1).toNat = o.toNat + 1 := L.toNat_add_one_of_lt (by omega)
    have hl1' : (l - 1).toNat = j := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    obtain ⟨ks, hks, hn⟩ := ih (o + 1) (l - 1) xs hk (by rw [ho1, hl1']; exact e') (by omega)
    refine ⟨x :: ks, by simp [List.mapM_cons, hx, hks], .cons hl ⟨by rw [hw]; exact hww, ?_⟩ hn⟩
    rw [hw]; exact hx

end L.Arena
