module

public import ConAgua.Arena.DeclCanonExpr2
import ConAgua.Arena.DeclMasterStage
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclCvg
import ConAgua.Arena.IndMaster
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.DeclArmsCanon

@[expose] public section

/-!
# `canon_names_go`, `canon_names` (lane `decls3`, helper `decls3-canon`)

The numbered names `⟨0⟩ … ⟨n-1⟩`, interned. The one place the canonical comparison writes the
name tables; the expression store (and `LitInj`) is untouched.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The model of `canon_names_go(i, n)`** (`gnW`). -/
l_model canonNamesGo_spec (p : Prog) (hp : CanonProg p)
  fns [hp.get "canon_names_go" ↦ gnW list]
  specs [internNAnon_spec p (hp.get "nanon_find") (hp.get "nanon_push") (hp.get "intern_nanon") n,
    internNNum_spec p (hp.get "nnum_find") (hp.get "nnum_push") (hp.get "intern_nnum") n,
    slCons_specW p (hp.get "iw_alloc") (hp.get "iw_copy") (hp.get "sl_cons") n]
  grind [arena_grind]

theorem gnW_ok {vis : Word} {fe : IFEnv} (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (i n : Word) (r : List Word),
    gnW k m i n = some (r, m') → StageR vis fe m a → i.toNat + n.toNat < 2 ^ 64 → PoolSmall m →
    ∃ (hs : List NIdx) (a' : AState),
      (ConRon.Arena.canonNamesGo i.toNat n.toNat).run a = .ok (hs, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ decRL (fun m => decHL m) 0 m' r hs ∧ a'.store.view = a.store.view ∧ PoolSmall m' := by
  induction k with
  | zero => intro m m' a i n r h; simp [gnW] at h
  | succ k ih =>
    intro m m' a i n r h hS hin hP
    rw [gnW] at h
    by_cases hn : n = 0
    · rw [ite_eq_left hn] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hn
      refine ⟨[], a, ?_, hS, IWGrow.refl _, ⟨by simp [decHL, hslice?], by simp⟩, rfl, hP⟩
      simp [ConRon.Arena.canonNamesGo]; rfl
    rw [ite_eq_right hn] at h
    have hn1 : n.toNat = (n - 1).toNat + 1 := toNat_pred hn
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    unfold gnW.k_intern_nanon at h
    split at h
    · simp at h
    rename_i a1 m1 hna
    have ha32 : ¬ 4294967296 ≤ a1 := fun ha32 => by rw [ite_eq_left ha32] at h; simp at h
    rw [ite_eq_right ha32] at h
    have ha1 : a1.toNat < 2 ^ 32 := by
      have : ¬ (4294967296 : Word).toNat ≤ a1.toNat := fun e => ha32 (UInt64.le_iff_toNat_le.mpr e)
      simpa using this
    obtain ⟨a1', hr1, hS1, hg1, hv1, hz1⟩ := internNAnon_stage hS hna
    unfold gnW.k_intern_nnum at h
    split at h
    · simp at h
    rename_i h1 m2 hnn
    have hh32 : ¬ 4294967296 ≤ h1 := fun hh32 => by rw [ite_eq_left hh32] at h; simp at h
    rw [ite_eq_right hh32] at h
    have hh1 : h1.toNat < 2 ^ 32 := by
      have : ¬ (4294967296 : Word).toNat ≤ h1.toNat := fun e => hh32 (UInt64.le_iff_toNat_le.mpr e)
      simpa using this
    obtain ⟨a2, hr2, hS2, hg2, hv2, hz2⟩ := internNNum_stage hS1 a1 i ha1 hnn
    unfold gnW.k_canon_names_go at h
    split at h
    · simp at h
    rename_i r3 m3 hrec
    have hP2 : PoolSmall m2 := by
      unfold PoolSmall at hP ⊢; rw [pcap_congr (hz2 POOL) (hz2 POOL1), pcap_congr (hz1 POOL) (hz1 POOL1)]; exact hP
    obtain ⟨hs3, a3, hrun3, hS3, hg3, hd3, hv3, hP3⟩ := ih m2 m3 a2 (i + 1) (n - 1) r3 hrec hS2
      (by rw [hi1]; omega) hP2
    unfold gnW.k_sl_cons at h
    split at h
    · simp at h
    rename_i r4 m4 hcons
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hd3u := decRL_unpack hd3
    obtain ⟨hSc, hgc, hdc, htc⟩ := consW_stage hcons hS3 hd3u.2 hh1 hd3u.1
    obtain ⟨-, -, -, hfr, -, -⟩ := consW_dec hcons hS3.iw.iwSize hS3.iw.ctl hd3u.2 hh1 hd3u.1
    refine ⟨decI h1 :: hs3, a3, ?_, hSc, (hg1.trans hg2).trans (hg3.trans hgc), ⟨?_, ?_⟩, ?_⟩
    · rw [hn1]
      simp only [ConRon.Arena.canonNamesGo, StateT.run_bind, hr1, exc_ok_bind', hr2, StateT.run_pure]
      rw [hi1] at hrun3
      simp only [StateT.run] at hrun3 ⊢
      rw [hrun3]; rfl
    · simpa using hdc
    · show (r4.headD 0).toNat + (r4.tail.headD 0).toNat ≤ iwTop m4; omega
    · refine ⟨by rw [hv3, hv2, hv1], ?_⟩
      unfold PoolSmall at hP3 ⊢; rw [pcap_congr (hfr.size POOL) (hfr.size POOL1)]; exact hP3

/-- **The model of `canon_names(n)`** (`cnW`). -/
l_model canonNames_spec (p : Prog) (hp : CanonProg p)
  fns [hp.get "canon_names" ↦ cnW list]
  specs [canonNamesGo_spec p hp n]
  grind [arena_grind]

theorem LitInj.of_view {a a' : AState} (h : LitInj a) (hv : a'.store.view = a.store.view) :
    LitInj a' := by
  intro x y l hx hy
  rw [hv] at hx hy
  exact h x y l hx hy

/-- The post of `canon_names`: the list of numerals as an `IW` slice, the pool still addressable,
the literal hash-consing kept. -/
def NamesPost (_dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (r : List Word) (cs : List NIdx) : Prop :=
  KeepPost vis fe (fun m r (cs : List NIdx) => decRL (fun m => decHL m) 0 m r cs) m m' a r cs ∧
    PoolSmall m' ∧ LitInj a

theorem cnW_ok {vis : Word} {fe : IFEnv} {n : Nat}
    {m m' : Mem} {a : AState} {k : Word} {r : List Word} (hr : cnW n m k = some (r, m'))
    (hS : StageR vis fe m a) (hP : PoolSmall m) :
    ∃ (hs : List NIdx) (a' : AState), (ConRon.Arena.canonNames k.toNat).run a = .ok (hs, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ decRL (fun m => decHL m) 0 m' r hs ∧
      a'.store.view = a.store.view ∧ PoolSmall m' := by
  cases n with
  | zero => simp [cnW] at hr
  | succ n =>
  simp only [cnW] at hr
  rcases hg0 : gnW n m 0 k with _ | ⟨r0, m0⟩ <;> simp only [hg0, cnW.k_canon_names_go, reduceCtorEq] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
  obtain ⟨hs, a', hrun, hS', hg, hd, hv, hP'⟩ := gnW_ok n _ _ a 0 k r0 hg0 hS
    (by have := UInt64.toNat_lt k; simpa using this) hP
  refine ⟨hs, a', hrun, hS', hg, ?_, hv, hP'⟩
  simpa only [decRL, getD0, cnGetD1, List.getD_cons_zero, List.getD_cons_succ] using hd

/-- **`canon_names` refines `canonNames`.** -/
@[refines ConRon.Arena.canonNames]
theorem canonNames_refines (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (k : Word) :
    RefAM p "canon_names" [k]
      (fun m a => StageR vis fe m a ∧ PoolSmall m ∧ LitInj a)
      (ConRon.Arena.canonNames k.toNat) (NamesPost dn vis fe) := by
  intro n s₀ a₀ ⟨hS, hP, hL⟩
  refine triple_post (canonNames_spec p hp n s₀ k) ?_
  rintro r s' ⟨hl, hr⟩
  obtain ⟨hs, a', hrun, hS', hg, hd, hv, hP'⟩ := cnW_ok hr hS hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres]
  exact ⟨⟨hS', hg, hd⟩, hP', hL.of_view hv⟩

/-- **`canon_names_go` refines `canonNamesGo`.** -/
@[refines ConRon.Arena.canonNamesGo]
theorem canonNamesGo_refines (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (i k : Word) :
    RefAM p "canon_names_go" [i, k]
      (fun m a => StageR vis fe m a ∧ PoolSmall m ∧ LitInj a ∧ i.toNat + k.toNat < 2 ^ 64)
      (ConRon.Arena.canonNamesGo i.toNat k.toNat) (NamesPost dn vis fe) := by
  intro n s₀ a₀ ⟨hS, hP, hL, hik⟩
  refine triple_post (canonNamesGo_spec p hp n s₀ i k) ?_
  rintro r s' ⟨hl, hr⟩
  obtain ⟨hs, a', hrun, hS', hg, hd, hv, hP'⟩ := gnW_ok n _ _ a₀ i k r hr hS hik hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres]
  exact ⟨⟨hS', hg, hd⟩, hP', hL.of_view hv⟩

end L.Ind
