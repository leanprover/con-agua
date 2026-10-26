import ConAgua.Arena.DeclCanonExpr2

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

mutual
/-- **The model of `canon_names_go(i, n)`**. -/
def gnW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, i, n =>
    if n = 0 then some ([0, 0], m)
    else gK1 k i n (nainternW m)

/-- After `intern_nanon`. -/
def gK1 (k : Nat) (i n : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (a, m1) => if 4294967296 ≤ a then none else gK2 k i n (nninternW m1 a i)

/-- After `intern_nnum`. -/
def gK2 (k : Nat) (i n : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (h, m2) => if 4294967296 ≤ h then none else gK3 k h (gnW k m2 (i + 1) (n - 1))

/-- After the recursion. -/
def gK3 (k : Nat) (h : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => gK4 (consW k m3 h (r.headD 0) (r.tail.headD 0))

/-- After `sl_cons`. -/
def gK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m4) => some ([r.headD 0, r.tail.headD 0], m4)
end

section arms
variable (k : Nat) (m m1 m2 m3 m4 : Mem) (i n a h : Word) (r : List Word)
theorem gnW_succ : gnW (k + 1) m i n =
    (if n = 0 then some ([0, 0], m) else gK1 k i n (nainternW m)) := by rw [gnW]
theorem gK1_some : gK1 k i n (some (a, m1)) =
    (if 4294967296 ≤ a then none else gK2 k i n (nninternW m1 a i)) := by rw [gK1]
theorem gK2_some : gK2 k i n (some (h, m2)) =
    (if 4294967296 ≤ h then none else gK3 k h (gnW k m2 (i + 1) (n - 1))) := by rw [gK2]
theorem gK3_some : gK3 k h (some (r, m3)) = gK4 (consW k m3 h (r.headD 0) (r.tail.headD 0)) := by
  rw [gK3]
theorem gK4_some : gK4 (some (r, m4)) = some ([r.headD 0, r.tail.headD 0], m4) := by rw [gK4]
end arms

grind_pattern [ind_grind] gnW_succ => gnW (k + 1) m i n
grind_pattern [ind_grind] gK1_some => gK1 k i n (some (a, m1))
grind_pattern [ind_grind] gK2_some => gK2 k i n (some (h, m2))
grind_pattern [ind_grind] gK3_some => gK3 k h (some (r, m3))
grind_pattern [ind_grind] gK4_some => gK4 (some (r, m4))

section specs5
variable (p : Prog) (hp : CanonProg p)
include hp

set_option maxHeartbeats 4000000 in
theorem canonNamesGo_spec (n : Nat) : ∀ (s₀ : St) (i k : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "canon_names_go" [i, k]
    ⦃fun r s' => LocEq s' s₀ ∧ gnW n s₀.mem i k = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ i k
    rw [invoke_eq _ (hp.get "canon_names_go")]; simp only [callFn, canonNamesGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ i k
    rw [invoke_eq _ (hp.get "canon_names_go")]
    simp only [callFn, canonNamesGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        internNAnon_spec p (hp.get "nanon_find") (hp.get "nanon_push") (hp.get "intern_nanon") n,
        internNNum_spec p (hp.get "nnum_find") (hp.get "nnum_push") (hp.get "intern_nnum") n,
        slCons_specW p (hp.get "iw_alloc") (hp.get "iw_copy") (hp.get "sl_cons") n, ih] <;>
      finish (gen := 20)

end specs5


theorem gnW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (i n : Word) (r : List Word),
    gnW k m i n = some (r, m') → StageR dn vis fe m a → i.toNat + n.toNat < 2 ^ 64 → PoolSmall m →
    ∃ (hs : List NIdx) (a' : AState),
      (ConRon.Arena.canonNamesGo i.toNat n.toNat).run a = .ok (hs, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decRL (fun m => decHL m) 0 m' r hs ∧ a'.store.view = a.store.view ∧ PoolSmall m' := by
  induction k with
  | zero => intro m m' a i n r h; simp [gnW] at h
  | succ k ih =>
    intro m m' a i n r h hS hin hP
    rw [gnW_succ] at h
    by_cases hn : n = 0
    · rw [if_pos hn] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hn
      refine ⟨[], a, ?_, hS, IWGrow.refl _, ⟨by simp [decHL, hslice?], by simp⟩, rfl, hP⟩
      simp [ConRon.Arena.canonNamesGo]; rfl
    rw [if_neg hn] at h
    have hn1 : n.toNat = (n - 1).toNat + 1 := toNat_pred hn
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    unfold gK1 at h
    split at h
    · simp at h
    rename_i a1 m1 hna
    have ha32 : ¬ 4294967296 ≤ a1 := fun ha32 => by rw [if_pos ha32] at h; simp at h
    rw [if_neg ha32] at h
    have ha1 : a1.toNat < 2 ^ 32 := by
      have : ¬ (4294967296 : Word).toNat ≤ a1.toNat := fun e => ha32 (UInt64.le_iff_toNat_le.mpr e)
      simpa using this
    obtain ⟨a1', hr1, hS1, hg1, hv1, hz1⟩ := internNAnon_stage hS hna
    unfold gK2 at h
    split at h
    · simp at h
    rename_i h1 m2 hnn
    have hh32 : ¬ 4294967296 ≤ h1 := fun hh32 => by rw [if_pos hh32] at h; simp at h
    rw [if_neg hh32] at h
    have hh1 : h1.toNat < 2 ^ 32 := by
      have : ¬ (4294967296 : Word).toNat ≤ h1.toNat := fun e => hh32 (UInt64.le_iff_toNat_le.mpr e)
      simpa using this
    obtain ⟨a2, hr2, hS2, hg2, hv2, hz2⟩ := internNNum_stage hS1 a1 i ha1 hnn
    unfold gK3 at h
    split at h
    · simp at h
    rename_i r3 m3 hrec
    have hP2 : PoolSmall m2 := by
      unfold PoolSmall at hP ⊢; rw [pcap_congr (hz2 POOL) (hz2 POOL1), pcap_congr (hz1 POOL) (hz1 POOL1)]; exact hP
    obtain ⟨hs3, a3, hrun3, hS3, hg3, hd3, hv3, hP3⟩ := ih m2 m3 a2 (i + 1) (n - 1) r3 hrec hS2
      (by rw [hi1]; omega) hP2
    unfold gK4 at h
    split at h
    · simp at h
    rename_i r4 m4 hcons
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hd3u := decRL_unpack hd3
    obtain ⟨hSc, hgc, hdc, htc⟩ := consW_stage hcons hS3 hd3u.2 hh1 hd3u.1
    obtain ⟨-, -, -, hfr, -, -⟩ := consW_dec hcons hS3.2.2.2.1 hS3.2.2.2.2.2 hd3u.2 hh1 hd3u.1
    refine ⟨decI h1 :: hs3, a3, ?_, hSc, (hg1.trans hg2).trans (hg3.trans hgc), ⟨?_, ?_⟩, ?_⟩
    · rw [hn1]
      simp only [ConRon.Arena.canonNamesGo, StateT.run_bind, hr1, exc_ok_bind', hr2, StateT.run_pure]
      rw [hi1] at hrun3
      simp only [StateT.run] at hrun3 ⊢
      rw [hrun3]; rfl
    · simpa using hdc
    · show (r4.headD 0).toNat + (r4.tail.headD 0).toNat ≤ iwTop m4; omega
    · refine ⟨by rw [hv3, hv2, hv1], ?_⟩
      unfold PoolSmall at hP3 ⊢; rw [pcap_congr (hfr.2.2.1 POOL) (hfr.2.2.1 POOL1)]; exact hP3


/-- **The model of `canon_names(n)`**. -/
def cnW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | k + 1, m, n =>
    match gnW k m 0 n with
    | none => none
    | some (r, m') => some ([r.headD 0, r.tail.headD 0], m')

theorem canonNames_spec (p : Prog) (hp : CanonProg p) (n : Nat) (s₀ : St) (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "canon_names" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ cnW n s₀.mem k = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "canon_names")]
  simp only [callFn, canonNames]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        canonNamesGo_spec p hp n] <;>
      finish (gen := 20) [cnW]

theorem LitInj.of_view {a a' : AState} (h : LitInj a) (hv : a'.store.view = a.store.view) :
    LitInj a' := by
  intro x y l hx hy
  rw [hv] at hx hy
  exact h x y l hx hy

/-- The post of `canon_names`: the list of numerals as an `IW` slice, the pool still addressable,
the literal hash-consing kept. -/
def NamesPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (r : List Word) (cs : List NIdx) : Prop :=
  KeepPost dn vis fe (fun m r (cs : List NIdx) => decRL (fun m => decHL m) 0 m r cs) m m' a r cs ∧
    PoolSmall m' ∧ LitInj a

theorem cnW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {n : Nat}
    {m m' : Mem} {a : AState} {k : Word} {r : List Word} (hr : cnW n m k = some (r, m'))
    (hS : StageR dn vis fe m a) (hP : PoolSmall m) :
    ∃ (hs : List NIdx) (a' : AState), (ConRon.Arena.canonNames k.toNat).run a = .ok (hs, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decRL (fun m => decHL m) 0 m' r hs ∧
      a'.store.view = a.store.view ∧ PoolSmall m' := by
  cases n with
  | zero => simp [cnW] at hr
  | succ n =>
  simp only [cnW] at hr
  rcases hg0 : gnW n m 0 k with _ | ⟨r0, m0⟩ <;> simp only [hg0, reduceCtorEq] at hr
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
      (fun m a => StageR dn vis fe m a ∧ PoolSmall m ∧ LitInj a)
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
      (fun m a => StageR dn vis fe m a ∧ PoolSmall m ∧ LitInj a ∧ i.toNat + k.toNat < 2 ^ 64)
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
