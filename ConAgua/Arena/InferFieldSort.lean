module

public import ConAgua.Arena.LevelSubstL
public import ConAgua.Arena.ErecRd
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.L.GrindAttr
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.WhnfBase
import ConAgua.Arena.IndLibSpec

@[expose] public section

/-!
# Readback and slice lemmas (formerly of `field_sort_zero`)

`field_sort_zero` (`inferProj`'s stored-guard test) went with con-leche's task #480: the guard is
computed at the use (`Infer.lean`'s `check_proj_guard`). What stays are its general lemmas: the
twin's name readbacks (`readNameM_run'`, `readNamesM_run'`), and decoded `EREC` slices as heap
pointers (`hslice?_succ`, `hslice?_bound_fsz`, `nmsR_of_hslice`, `LvsR.toAR`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open ConLeche

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

/-! ## The handles as heap pointers -/

/-- A decoded slice is in bounds. -/
theorem hslice?_bound_fsz {k : IdxKind} (a : Array Word) : ∀ (n o : Nat) (l : List (Idx k)),
    hslice? (aread a) o n = some l → n = 0 ∨ o + n ≤ a.size
  | 0, _, _, _ => Or.inl rfl
  | n + 1, o, l, h => by
    rw [L.Ind.hslice?_succ] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, -⟩ := h
    simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
    obtain ⟨w, hw, -⟩ := hx
    have := (Array.getElem?_eq_some_iff.mp hw).1
    rcases hslice?_bound_fsz a n (o + 1) xs hxs with h0 | h0 <;> right <;> omega

/-- A decoded `EREC` name slice is related to the names' readbacks at the tagged reads
(`NmsK` at `keyT EREC`). -/
theorem nmsAR_of_hslice (m : Mem) (ns : NStore) : ∀ (k : Nat) (lps : List NIdx) (ks : List Name)
    (o n : Word), n.toNat = k → hslice? (erecP m) o.toNat k = some lps →
    lps.mapM (denoteN ns) = some ks → NmsK (nameN ns) m (keyT EREC) o n ks
  | 0, lps, ks, o, n, hn, hs, hd => by
    have : n = 0 := UInt64.toNat_inj.mp (by simpa using hn)
    subst this
    simp [hslice?] at hs; subst hs; simp at hd; subst hd; exact .nil
  | k + 1, lps, ks, o, n, hn, hs, hd => by
    rw [L.Ind.hslice?_succ] at hs
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
      have hn1 : (n - 1).toNat = k := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
      have hr : keyT EREC m o = w := erRd_of o w hw
      have hrest : NmsK (nameN ns) m (keyT EREC) (o + 1) (n - 1) ys := by
        rcases k with _ | k
        · have e0 : n - 1 = 0 := UInt64.toNat_inj.mp (by simpa using hn1)
          rw [e0]; simp [hslice?] at hxs; subst hxs; simp at hys; subst hys; exact .nil
        · have hlt : o.toNat + 1 < 2 ^ 64 := by
            rw [L.Ind.hslice?_succ] at hxs
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hxs
            obtain ⟨_, hx', -⟩ := hxs
            simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx'
            obtain ⟨w', hw', -⟩ := hx'
            exact erecP_lt64 hw'
          have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
          exact nmsAR_of_hslice m ns (k + 1) xs ys (o + 1) (n - 1) hn1 (by rw [ho1]; exact hxs) hys
      exact .cons hn0 ⟨by rw [hr]; exact hw32, by rw [hr]; exact hy⟩ hrest
    · simp [hw32] at hx

/-- `LvsR` (`POOL`) is `LvsAR` at `POOL`. -/
theorem LvsR.toAR {N : Word → Name → Prop} {m : Mem} {o k : Word} {ls : List Level}
    (h : LvsR N m o k ls) : LvsAR N m POOL o k ls := by
  induction h with
  | nil => exact .nil
  | cons hk hl _ ih => exact .cons hk hl ih

end L.Arena
