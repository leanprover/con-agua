import ConAgua.Arena.Knot
import ConAgua.Arena.CoreLevels
import ConAgua.Arena.LevelInternRef
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# `field_sort_zero`: `inferProj`'s propositional-structure test (lane `defeq2`)

The twin (`Arena/Core.lean`, `inferProj`) reads back the structure's level parameters (`readNamesM`),
the subject type's universe arguments (`readLevelsM`) and the field's sort (`readLevelM`), and asks
`Level.isEquiv (Level.subst ks vs f) .zero == some true`. L runs lane `levels`' heap algorithms on
the handles themselves (no readback): `ls_node(us)` gives the arguments' `POOL` slice, the heap is
reset (as `lvl_eq` does), `lv_substl` substitutes with the keys the `EREC` name slice `(po, pl)`
and the values that `POOL` slice (`lv_lookup` at `KA = EREC`, `VA = POOL`), `lh_mk(0, 0, 0)`
allocates `zero`, and `lv_equiv` compares; the answer is `1` exactly for `some true`.

* `fszW`: the model; `fieldSortZero_spec`: the L code computes it (`vcgen` + `finish`).
* `fieldSortZero_core`: **`FieldSortZeroOK`** (`Knot.lean`) from the program's lookups. The twin's
  state changes only in its three readback caches (`readNC`, `readLsC`, `readLC`), L's only in the
  heap. Hypotheses beyond `CoreS` (in `FieldSortZeroOK`): the three readbacks succeed, and the name
  cache holds readbacks (`ReadNCOK`; `CoreS` has `readL`/`readLs` but no name counterpart).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open ConLeche

/-! ## The L code and its model -/

/-- `inferProj`'s propositional-structure test: `1` iff the field's sort `fs`, its level parameters
(the `EREC` name slice `(po, pl)`) substituted by the universe arguments `us`, is equivalent to
`zero` (`some true`). -/
-- con-ron: ConRon/Arena/Core.lean:2694-2736 ConRon.Arena.inferProj
@[l_impl ConRon.Arena.inferProj]
def fieldSortZeroL : FunDecl := lfn (po, pl, us, fs) locals (o, k, x, z, r) {
  (o, k) := call ls_node(us);
  CTL.u64[192] := 0;
  x := call lv_substl(fs, po, pl, o, k);
  z := call lh_mk(0, 0, 0);
  r := call lv_equiv(x, z);
  return u64(r == 2)
}

/-- After `lv_equiv`: `1` exactly for `some true` (`encO`'s `2`). -/
def fszK₃ : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m) => some (if r = 2 then 1 else 0, m)

/-- After `lh_mk(0, 0, 0)`: compare. -/
def fszK₂ (n : Nat) (x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (z, m) => fszK₃ (equivW n m x z)

/-- After `lv_substl`: allocate `zero`. -/
def fszK₁ (n : Nat) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m) => fszK₂ n x (lhMkW m 0 0 0)

/-- **The model of `field_sort_zero`** (callees at fuel `n`). -/
def fszW (n : Nat) (m : Mem) (po pl us fs : Word) : Option (Word × Mem) :=
  fszK₁ n (substLW EREC POOL n (m.set64 CTL 192 0) fs po pl ((lsNodeW m us).headD 0)
    ((lsNodeW m us).tail.headD 0))

theorem fszK₃_some (r : Word) (m : Mem) : fszK₃ (some (r, m)) = some (if r = 2 then 1 else 0, m) :=
  rfl
theorem fszK₂_some (n : Nat) (x z : Word) (m : Mem) :
    fszK₂ n x (some (z, m)) = fszK₃ (equivW n m x z) := rfl
theorem fszK₁_some (n : Nat) (x : Word) (m : Mem) :
    fszK₁ n (some (x, m)) = fszK₂ n x (lhMkW m 0 0 0) := rfl

/-- What `field_sort_zero` needs of a program. -/
structure FieldSortZeroProg (p : Prog) : Prop where
  lv : LevelProg p
  equiv : p.lookup "lv_equiv" = some lvEquiv
  lsn : p.lookup "ls_node" = some lsNode
  lookup : p.lookup "lv_lookup" = some (lvLookupG EREC POOL)
  substl : p.lookup "lv_substl" = some lvSubstL
  fsz : p.lookup "field_sort_zero" = some fieldSortZeroL

theorem fieldSortZero_spec (p : Prog) (hp : FieldSortZeroProg p) (n : Nat) (s₀ : St)
    (po pl us fs : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "field_sort_zero" [po, pl, us, fs]
    ⦃fun r s' => LocEq s' s₀ ∧ fszW n s₀.mem po pl us fs = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.fsz]
  simp only [callFn, fieldSortZeroL]
  sym only [lang_grind, arena_grind, level_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, lsNode_spec p hp.lsn n,
      lvSubstL_spec EREC POOL p hp.lookup hp.lv.node hp.lv.alloc hp.substl n,
      lhMk_spec p hp.lv.alloc n, lvEquiv_spec p hp.lv hp.equiv n] <;>
    finish (gen := 20) [fszW, fszK₁_some, fszK₂_some, fszK₃_some]

/-! ## The twin's readbacks -/

/-- `readNameM` at a defined handle: its readback, and only `readNC` changes. -/
theorem readNameM_run' (a : AState) (h : NIdx) (x : Name) (hd : denoteN a.store.ns h = some x)
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

/-- `readNamesM` at defined handles: their readbacks, and only `readNC` changes. -/
theorem readNamesM_run' : ∀ (lps : List NIdx) (a : AState) (ks : List Name),
    lps.mapM (denoteN a.store.ns) = some ks → ReadNCOK a →
    ∃ X, (readNamesM lps).run a = .ok (ks, { a with caches := { a.caches with readNC := X } }) ∧
      ReadNCOK { a with caches := { a.caches with readNC := X } }
  | [], a, ks, hd, hc => by
    simp at hd; subst hd
    exact ⟨a.caches.readNC, by simp [readNamesM]; rfl, by simpa using hc⟩
  | h :: hs, a, ks, hd, hc => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hd
    obtain ⟨x, hx, xs, hxs, rfl⟩ := hd
    obtain ⟨X₁, h₁, hc₁⟩ := readNameM_run' a h x hx hc
    obtain ⟨X₂, h₂, hc₂⟩ := readNamesM_run' hs { a with caches := { a.caches with readNC := X₁ } }
      xs hxs hc₁
    exact ⟨X₂, by simp only [readNamesM, StateT.run_bind, h₁, except_ok_bind, h₂]; rfl, hc₂⟩

/-- The core tier does not read the name readback cache. -/
theorem CoreRM.readNC {m : Mem} {c : Caches} {M : ModeMaps} {eb : Word} (h : CoreRM m c M eb)
    (X : Std.HashMap NIdx Name) : CoreRM m { c with readNC := X } M eb :=
  ⟨h.wc, h.wk, h.wh, h.inf, h.io, h.de, h.eb1, h.ct, h.cv, h.rr, h.lq, h.lsq⟩

/-- **The twin's test, run**: the readbacks' verdict; only the three readback caches change. -/
theorem fieldSortZeroT_run (a : AState) (lps : List NIdx) (us : LsIdx) (fs : LIdx) (ks : List Name)
    (vs : List Level) (f : Level) (hk : lps.mapM (denoteN a.store.ns) = some ks)
    (hv : denoteLs a.store.lss us = some vs) (hf : denoteL a.store.ls fs = some f)
    (hn : ReadNCOK a) (hl : ReadLCOK a) (hls : ReadLsCOK a) :
    ∃ X Y Z, (fieldSortZeroT lps us fs).run a =
      .ok (Level.isEquiv (Level.subst ks vs f) .zero == some true,
        { a with caches := { a.caches with readNC := X, readLsC := Y, readLC := Z } }) ∧
      ReadLCOK { a with caches := { a.caches with readNC := X, readLsC := Y, readLC := Z } } ∧
      ReadLsCOK { a with caches := { a.caches with readNC := X, readLsC := Y, readLC := Z } } ∧
      ReadNCOK { a with caches := { a.caches with readNC := X } } := by
  obtain ⟨X, h₁, hnX⟩ := readNamesM_run' lps a ks hk hn
  obtain ⟨Y, h₂, hls₂⟩ := readLevelsM_run' { a with caches := { a.caches with readNC := X } } us vs
    hv (fun h l e => hls h l e)
  obtain ⟨Z, h₃, hl₃⟩ := readLevelM_run'
    { a with caches := { a.caches with readNC := X, readLsC := Y } } fs f hf (fun h l e => hl h l e)
  refine ⟨X, Y, Z, ?_, hl₃, fun h l e => hls₂ h l e, hnX⟩
  simp only [fieldSortZeroT, StateT.run_bind, h₁, except_ok_bind, h₂, h₃]
  rfl

/-! ## The handles as heap pointers -/

theorem hslice?_succ {k : IdxKind} (a : Array Word) (o n : Nat) :
    (hslice? a o (n + 1) : Option (List (Idx k))) =
      (do let x ← hd? a o; let xs ← hslice? a (o + 1) n; pure (x :: xs)) := by
  simp only [hslice?, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero,
    Function.comp_def, Nat.succ_eq_add_one, ← Nat.add_assoc, Nat.add_right_comm o]

/-- A decoded slice is in bounds. -/
theorem hslice?_bound_fsz {k : IdxKind} (a : Array Word) : ∀ (n o : Nat) (l : List (Idx k)),
    hslice? a o n = some l → n = 0 ∨ o + n ≤ a.size
  | 0, _, _, _ => Or.inl rfl
  | n + 1, o, l, h => by
    rw [hslice?_succ] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, -⟩ := h
    simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
    obtain ⟨w, hw, -⟩ := hx
    have := (Array.getElem?_eq_some_iff.mp hw).1
    rcases hslice?_bound_fsz a n (o + 1) xs hxs with h0 | h0 <;> right <;> omega

/-- A decoded `EREC` name slice is related to the names' readbacks (`NmsR`). -/
theorem nmsR_of_hslice (m : Mem) (ns : NStore) : ∀ (k : Nat) (lps : List NIdx) (ks : List Name)
    (o n : Word), n.toNat = k → hslice? (m.arr64 EREC) o.toNat k = some lps →
    o.toNat + k < 2 ^ 64 → lps.mapM (denoteN ns) = some ks → NmsR (nameN ns) m EREC o n ks
  | 0, lps, ks, o, n, hn, hs, _, hd => by
    have : n = 0 := UInt64.toNat_inj.mp (by simpa using hn)
    subst this
    simp [hslice?] at hs; subst hs; simp at hd; subst hd; exact .nil
  | k + 1, lps, ks, o, n, hn, hs, hon, hd => by
    rw [hslice?_succ] at hs
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hs
    obtain ⟨x, hx, xs, hxs, rfl⟩ := hs
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hd
    obtain ⟨y, hy, ys, hys, rfl⟩ := hd
    simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
    obtain ⟨w, hw, hx⟩ := hx
    by_cases hw32 : w.toNat < 2 ^ 32
    · simp only [hw32, ↓reduceIte, Option.some.injEq] at hx
      subst hx
      have hn0 : n ≠ 0 := fun e => by subst e; simp at hn
      have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hn1 : (n - 1).toNat = k := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
      have hr : rdW (m.arr64 EREC) o = w := by simp [rdW, hw]
      exact .cons hn0 ⟨by rw [hr]; exact hw32, by rw [hr]; exact hy⟩
        (nmsR_of_hslice m ns k xs ys (o + 1) (n - 1) hn1 (by rw [ho1]; exact hxs) (by omega) hys)
    · simp [hw32] at hx

/-- `LvsR` (`POOL`) is `LvsAR` at `POOL`. -/
theorem LvsR.toAR {N : Word → Name → Prop} {m : Mem} {o k : Word} {ls : List Level}
    (h : LvsR N m o k ls) : LvsAR N m POOL o k ls := by
  induction h with
  | nil => exact .nil
  | cons hk hl _ ih => exact .cons hk hl ih

theorem decBool_fsz (o : Option Bool) :
    decBool [if encO o = 2 then 1 else 0] = (o == some true) := by
  rcases o with _ | _ | _ <;> rfl

/-! ## The refinement -/

/-- **The model of `field_sort_zero` refines `fieldSortZeroT`** under `CoreS`, at defined
readbacks. -/
theorem fszW_ok {dn : NIdx → Option Name} {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (n : Nat) (po pl us fs : Word)
    (lps : List NIdx) (hus : HW us) (hfs : HW fs)
    (hsl : hslice? (m.arr64 EREC) po.toNat pl.toNat = some lps) (hn : ReadNCOK a)
    (ks : List Name) (hk : lps.mapM (denoteN a.store.ns) = some ks)
    (vs : List Level) (hv : denoteLs a.store.lss (decI us) = some vs)
    (f : Level) (hf : denoteL a.store.ls (decI fs) = some f) (z : Word)
    (h : fszW n m po pl us fs = some (z, m')) :
    ∃ a', (fieldSortZeroT lps (decI us) (decI fs)).run a = .ok (decBool [z], a') ∧
      CoreAfter dn m m' a' vis fe M eb ∧ HW z := by
  have hR := hS.arena.1
  have hR₀ : ArenaR (m.set64 CTL 192 0) a :=
    ArenaR.frame (by decide) c192_not_arena (reset_frame m) hR
  have hN := nameN_rel _ hS.nwf
  -- the arguments' slice
  obtain ⟨ids, hvw, hdl⟩ := denoteLs_view a (decI us) vs hv
  obtain ⟨e₁, t₁, s₁⟩ := lsNodeW_store hR hus hvw
  have hpool : (m.set64 CTL 192 0).arr64 POOL = m.arr64 POOL :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hpoolv := vpool_congr hpool (Mem.arr64_set64_ne _ _ _ _ _ (by decide))
  have herec : (m.set64 CTL 192 0).arr64 EREC = m.arr64 EREC :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have htop := hR.lit.1.top41
  have hvs := (lvsR_of_slice hR₀ ids vs _ _ (by rw [hpoolv]; exact s₁) (by omega) hdl).toAR
  -- the keys
  have hbound : po.toNat + pl.toNat < 2 ^ 64 := by
    have := hS.erec
    rcases hslice?_bound_fsz _ _ _ _ hsl with h0 | h0
    · have := po.toNat_lt; omega
    · omega
  have hks : NmsR (nameN a.store.lss.ls.ns) (m.set64 CTL 192 0) EREC po pl ks :=
    nmsR_of_hslice _ _ pl.toNat lps ks po pl rfl (by rw [herec]; exact hsl) hbound hk
  -- the field's sort
  have hfl := denoteL_lvR hR₀ (decI fs) f hf
  rw [decI_word_self fs hfs] at hfl
  -- the run
  unfold fszW at h
  rw [e₁] at h
  simp only [List.headD_cons, List.tail_cons] at h
  cases e₂ : substLW EREC POOL n (m.set64 CTL 192 0) fs po pl (tfld m LVLS (tierW us) (idxW us) 0)
      (tfld m LVLS (tierW us) (idxW us) 1) with
  | none => rw [e₂] at h; simp [fszK₁] at h
  | some q₁ =>
  obtain ⟨x, m₁⟩ := q₁
  rw [e₂, fszK₁_some] at h
  obtain ⟨he₁, hx⟩ := substLW_ok hN (by decide) (by decide) ks vs n _ _ _ _ _ _ _ _ _ hfl hks hvs e₂
  cases e₃ : lhMkW m₁ 0 0 0 with
  | none => rw [e₃] at h; simp [fszK₂] at h
  | some q₂ =>
  obtain ⟨y, m₂⟩ := q₂
  rw [e₃, fszK₂_some] at h
  obtain ⟨he₂, hy, -⟩ := lhMkW_ext e₃
  cases e₄ : equivW n m₂ x y with
  | none => rw [e₄] at h; simp [fszK₃] at h
  | some q₃ =>
  obtain ⟨r, m₃⟩ := q₃
  rw [e₄, fszK₃_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨he₃, hr⟩ := equivW_ok hN n _ _ _ _ _ _ Level.zero (hx.mono he₂) (.zero hy) e₄
  -- the frame
  have hf₁ : MemFrame [LH] [192] m m₃ :=
    ((reset_frame m).mono (by simp) (by simp)).trans ((he₁.trans (he₂.trans he₃)).memFrame)
  obtain ⟨hS₁, hK₁⟩ := hS.frame hf₁ (by simp [LH]) (by simp)
  -- the twin
  obtain ⟨X, Y, Z, hrun, hl₃, hls₃, hnX⟩ := fieldSortZeroT_run a lps (decI us) (decI fs) ks vs f hk hv hf
    hn hS.readL hS.readLs
  subst hr
  refine ⟨_, by rw [hrun, decBool_fsz], ⟨M, ?_, KeptAll.refl _ _, hK₁⟩, by unfold HW; split <;> decide⟩
  exact ⟨⟨ArenaR.caches_irrel _ hS₁.arena.1, DerR.of_store _ _ _ hS₁.arena.2 rfl⟩,
    ((hS₁.core.readNC X).readLsC Y).readLC Z, hS₁.pins, hS₁.env, hl₃, hls₃, hS₁.nwf, hS₁.erec,
    hS₁.spn, hS₁.memos, hS₁.bstk,
    hS₁.den.mono (LsExt.refl _) rfl rfl (fun k x hk => .inr (hnX k x hk)) (fun _ _ hv => hv)
      (fun _ _ _ hv => .inl hv) (hS₁.den.lvlAll.congr rfl) (hS₁.den.lsAll.congr rfl), hS₁.mode⟩

/-- **`field_sort_zero` refines the twin's propositional-structure test** (`FieldSortZeroOK`). -/
@[refines_part ConRon.Arena.inferProj "the propositional-structure test (field_sort_zero)"]
theorem fieldSortZero_core (p : Prog) (hp : FieldSortZeroProg p) : FieldSortZeroOK p := by
  intro n s₀ a₀ dn vis fe M eb po pl us fs lps hS hus hfs hsl hn ⟨ks, hk⟩ ⟨vs, hv⟩ ⟨f, hf⟩
  cases n with
  | zero =>
    -- every L call at fuel `0` fails
    unfold CoreSpec
    rw [invoke_eq _ hp.fsz]
    simp only [callFn]
    vcgen [exec] <;> grind
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun
    (fieldSortZero_spec p hp n s₀ po pl us fs)
  subst hs
  obtain ⟨a', ha', hA', hz⟩ := fszW_ok hS n po pl us fs lps hus hfs hsl hn ks hk vs hv f hf _ hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', by rw [hres]; rfl, hz⟩

end L.Arena
