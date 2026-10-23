import ConAgua.Arena.RecCheckSpec12
import ConAgua.Arena.IndSumSpec13


noncomputable section

/-!
# `RecCheck`: `targetMajorNfs` (lane `indproofs3`, helper `rec`)

The walk's recorded constructor normal forms of a class. L (D18): the loop became the twin's list
recursion (the tail first, so the class-match calls fire from the last entry to the first), each
kept entry `sl_cons`ed onto the kept tail (a copy, so the result is a pointer slice decoded below
the tops). Callees: `ctors_have_name` (helper `recb`'s `chnW`), `target_class_match`
(`RecCheckSpec12`), `sl_cons`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Reading records decoded below the tops -/

/-- A handle field of a record decoded in the cut pools, read at its word address. -/
theorem truncH {k : IdxKind} {m : Mem} {w : Word} {i : Nat} {x : Idx k}
    (h : iwH (truncM m) (w.toNat + i) = some x) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    H (rdW (m.arr64 IW) (w + UInt64.ofNat i)) ∧ decI (rdW (m.arr64 IW) (w + UInt64.ofNat i)) = x := by
  have hi : w.toNat + i < iwTop m := by
    simp only [iwH, hd?] at h
    cases hw : (iwA (truncM m))[w.toNat + i]? with
    | none => simp [hw] at h
    | some v => exact (truncM_iw_get hw).1
  rw [iwH_truncM hi] at h
  obtain ⟨v, e, hv, hd⟩ := iwH_rdW_at h hsz
  rw [e]; exact ⟨hv, hd⟩

/-- A slice field `(off, len)` of a record decoded in the cut pools, read at its word addresses. -/
theorem truncSl {k : IdxKind} {m : Mem} {w : Word} {i o l : Nat} {xs : List (Idx k)}
    (ho : iwN (truncM m) (w.toNat + i) = some o) (hl : iwN (truncM m) (w.toNat + i + 1) = some l)
    (hd : decHL (truncM m) o l = some xs) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    HSl0 m (rdW (m.arr64 IW) (w + UInt64.ofNat i)) (rdW (m.arr64 IW) (w + UInt64.ofNat (i + 1))) xs := by
  obtain ⟨-, hom⟩ := rec2IwN_trunc ho
  obtain ⟨-, hlm⟩ := rec2IwN_trunc hl
  obtain ⟨eo, to⟩ := rec2RdN (w := w) (k := i) hom hsz
  obtain ⟨el, tl⟩ := rec2RdN (w := w) (k := i + 1) (by simpa [Nat.add_assoc] using hlm) hsz
  rw [eo, el]
  rcases rec3IwSlice hd with hb | h0
  · refine HSl0.of ?_ (by rw [to, tl]; exact hb)
    rw [to, tl, ← decHL_truncM hb]; exact hd
  · subst h0
    have hx : xs = [] := by have := decHL_length _ hd; simpa using this
    subst hx
    exact ⟨by rw [tl]; simp [decHL, hslice?], .inl (UInt64.toNat_inj.mp (by rw [tl]; rfl))⟩

/-- The fields of a `NestCtorNf` record decoded below the tops. -/
theorem decNCN_fields {m : Mem} {e : Word} {nf : NestCtorNf} (h : DecB (fun m => decNCN m e.toNat) m nf)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    H (rdW (m.arr64 IW) e) ∧ decI (rdW (m.arr64 IW) e) = nf.ctor ∧
    H (rdW (m.arr64 IW) (e + 1)) ∧ decI (rdW (m.arr64 IW) (e + 1)) = nf.lvls ∧
    HSl0 m (rdW (m.arr64 IW) (e + 2)) (rdW (m.arr64 IW) (e + 3)) nf.ds := by
  have h' : decNCN (truncM m) e.toNat = some nf := h
  simp only [decNCN, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h'
  obtain ⟨c, hc, lv, hlv, ds, hds, x4, -, rfl⟩ := h'
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hds
  obtain ⟨hc1, hc2⟩ := truncH (i := 0) (by simpa using hc) hsz
  obtain ⟨hl1, hl2⟩ := truncH (i := 1) hlv hsz
  have hsl := truncSl (w := e) (i := 2) ho (by simpa [Nat.add_assoc] using hl) hd hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, show UInt64.ofNat 1 = (1 : Word) from rfl,
    show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat (2 + 1) = (3 : Word) from rfl,
    UInt64.add_zero] at hc1 hc2 hl1 hl2 hsl
  exact ⟨hc1, hc2, hl1, hl2, hsl⟩

/-- The head of a pointer slice decoded below the tops. -/
theorem PSlR.uncons {α : Type} {f : Mem → Nat → Option α} {xs : List α} {o l : Word} {m : Mem}
    (h : PSlR f xs o l m) (hl : l ≠ 0) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    ∃ x ys, xs = x :: ys ∧ DecB (fun m' => f m' (rdW (m.arr64 IW) o).toNat) m x ∧
      PSlR f ys (o + 1) (l - 1) m := by
  obtain ⟨hd, hb⟩ := h
  have hb64 : o.toNat + l.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt hb (Nat.lt_of_le_of_lt (by
    simp only [iwTop]; exact Nat.le_refl _) (rdW (m.arr64 CTL) 200).toNat_lt)
  obtain ⟨eo, el, hl0⟩ := slice_step hl hb64
  obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
  have hd' : decPL (truncM m) (f (truncM m)) o.toNat (l' + 1) = some xs := by rw [← hl']; exact hd
  obtain ⟨pp, x, ys, rfl, hp, hx, hys⟩ := decPL_cons hd'
  obtain ⟨-, hpm⟩ := rec2IwN_trunc hp
  have hr := (iwN_rdW hpm (by omega)).1
  rw [UInt64.ofNat_toNat] at hr
  refine ⟨x, ys, rfl, ?_, ?_, ?_⟩
  · show f (truncM m) (rdW (m.arr64 IW) o).toNat = some x
    rw [hr, UInt64.toNat_ofNat_of_lt' (iwN_rdW hpm (by omega)).2]; exact hx
  · show decPL (truncM m) (f (truncM m)) (o + 1).toNat (l - 1).toNat = some ys
    rw [eo, el, hl']; exact hys
  · rw [eo, el]; omega

/-- A pointer consed onto a pointer slice decoded below the tops (`sl_cons`). -/
theorem consW_pslr {α : Type} {f : Mem → Nat → Option α} (hf : ∀ q, OMono (fun m => f m q))
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List α} {y : α}
    (h : consW n m x o l = some (r, m')) (hS : StageR dn vis fe m a) (hxs : PSlR f xs o l m)
    (hy : DecB (fun m => f m x.toNat) m y) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ PSlR f (y :: xs) (r.headD 0) (r.tail.headD 0) m' ∧
      MFr [] [] m m' := by
  obtain ⟨ps, -, hps, hmap⟩ := sumDecNL_of_decB hxs.1
  obtain ⟨hS', hg, hd', ht'⟩ := consW_stageN h hS hxs.2 hps
  exact ⟨hS', hg, ⟨sumDecB_cons hf hmap hd' (Nat.le_of_eq ht') hg (hy.grow (hf _) hg), Nat.le_of_eq ht'⟩,
    consW_mfr h⟩

/-! ## The word model -/

def tcmF (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, q, fto, ftl, pfo, pfl, us, dso, dsl, lvls, edso, edsl =>
    tcmW cR n m vis q fto ftl pfo pfl us dso dsl lvls edso edsl

def tmnK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, m) => some ([rc.headD 0, rc.tail.headD 0], m)

def tmnK3 (cR : CallM) (n : Nat) (rr : List Word) (e : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rk, m) =>
    if rk.headD 0 = 0 then some ([rr.headD 0, rr.tail.headD 0], m)
    else tmnK4 (consW n m e (rr.headD 0) (rr.tail.headD 0))

def tmnK2 (cR : CallM) (n : Nat) (vis q fto ftl pfo pfl us dso dsl : Word) (rr : List Word) (m : Mem) (e : Word) :
    Option Word → Option (List Word × Mem)
  | none => none
  | some hv =>
    if hv = 0 then some ([rr.headD 0, rr.tail.headD 0], m)
    else tmnK3 cR n rr e (tcmF cR n m vis q fto ftl pfo pfl us dso dsl (rdW (m.arr64 IW) (e + 1))
      (rdW (m.arr64 IW) (e + 2)) (rdW (m.arr64 IW) (e + 3)))

def tmnK1 (cR : CallM) (n : Nat) (vis q fto ftl pfo pfl us dso dsl cto ctl nfo : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rr, m) => tmnK2 cR n vis q fto ftl pfo pfl us dso dsl rr m (rdW (m.arr64 IW) nfo)
      (chnW n m cto ctl (rdW (m.arr64 IW) (rdW (m.arr64 IW) nfo)))

/-- **The model of `target_major_nfs`** (exec fuel). -/
def tmnW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, q, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo, nfl =>
    if nfl = 0 then some ([0, 0], m)
    else tmnK1 cR n vis q fto ftl pfo pfl us dso dsl cto ctl nfo
      (tmnW cR n m vis q fto ftl pfo pfl us dso dsl cto ctl (nfo + 1) (nfl - 1))

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl e hv : Word) (rr rk rc : List Word)
theorem tmnK4_some : tmnK4 (some (rc, m)) = some ([rc.headD 0, rc.tail.headD 0], m) := rfl
theorem tmnK3_drop (h : rk.headD 0 = 0) : tmnK3 cR n rr e (some (rk, m)) = some ([rr.headD 0, rr.tail.headD 0], m) := by
  simp only [tmnK3]; rw [if_pos h]
theorem tmnK3_keep (h : ¬ rk.headD 0 = 0) : tmnK3 cR n rr e (some (rk, m)) =
    tmnK4 (consW n m e (rr.headD 0) (rr.tail.headD 0)) := by simp only [tmnK3]; rw [if_neg h]
theorem tmnK2_no (h : hv = 0) : tmnK2 cR n vis q fto ftl pfo pfl us dso dsl rr m e (some hv) =
    some ([rr.headD 0, rr.tail.headD 0], m) := by simp only [tmnK2]; rw [if_pos h]
theorem tmnK2_yes (h : ¬ hv = 0) : tmnK2 cR n vis q fto ftl pfo pfl us dso dsl rr m e (some hv) =
    tmnK3 cR n rr e (tcmF cR n m vis q fto ftl pfo pfl us dso dsl (rdW (m.arr64 IW) (e + 1))
      (rdW (m.arr64 IW) (e + 2)) (rdW (m.arr64 IW) (e + 3))) := by simp only [tmnK2]; rw [if_neg h]
theorem tmnK1_some : tmnK1 cR n vis q fto ftl pfo pfl us dso dsl cto ctl nfo (some (rr, m)) =
    tmnK2 cR n vis q fto ftl pfo pfl us dso dsl rr m (rdW (m.arr64 IW) nfo)
      (chnW n m cto ctl (rdW (m.arr64 IW) (rdW (m.arr64 IW) nfo))) := rfl
theorem tmnW_nil (h : nfl = 0) : tmnW cR (n + 1) m vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl = some ([0, 0], m) := by
  simp [tmnW, h]
theorem tmnW_cons (h : ¬ nfl = 0) : tmnW cR (n + 1) m vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl =
    tmnK1 cR n vis q fto ftl pfo pfl us dso dsl cto ctl nfo
      (tmnW cR n m vis q fto ftl pfo pfl us dso dsl cto ctl (nfo + 1) (nfl - 1)) := by simp [tmnW, h]
end arms
attribute [ind_grind] tmnK4_some tmnK3_drop tmnK3_keep tmnK2_no tmnK2_yes tmnK1_some tmnW_nil tmnW_cons

/-- The lookups of `target_major_nfs`. -/
structure TmnLook (p : Prog) : Prop where
  tcm : TcmLook p
  chn : p.lookup "ctors_have_name" = some ctorsHaveName
  tmn : p.lookup "target_major_nfs" = some targetMajorNfs

theorem tcmF_spec (p : Prog) (L : TcmLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St)
    (vis q fto ftl pfo pfl us dso dsl lvls edso edsl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_class_match"
      [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, lvls, edso, edsl]
    ⦃fun r s' => LocEq s' s₀ ∧
      tcmF cR n s₀.mem vis q fto ftl pfo pfl us dso dsl lvls edso edsl = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact targetClassMatch_spec p L cR hcR n s₀ vis q fto ftl pfo pfl us dso dsl lvls edso edsl

theorem tmn_spec (p : Prog) (L : TmnLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) :
    ∀ (s₀ : St) (vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_major_nfs"
      [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo, nfl]
    ⦃fun r s' => LocEq s' s₀ ∧
      tmnW cR n s₀.mem vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl
    rw [invoke_eq _ L.tmn]; simp only [callFn, targetMajorNfs]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl
    rw [invoke_eq _ L.tmn]
    simp only [callFn, targetMajorNfs]
    sym (gen := 80) (instances := 20000) only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        ctorsHaveName_spec p L.chn n, tcmF_spec p L.tcm cR hcR n,
        slCons_specW p L.tcm.ha L.tcm.ic L.tcm.sc n] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8,
        loc_init9, loc_init10, loc_init11, loc_init12]

/-! ## The relational side -/

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem tcmF_ok (n : Nat) {m m' : Mem} {a : AState} {q fto ftl pfo pfl us dso dsl lvls edso edsl : Word}
    {r : List Word} {bs : BlockShape} {formerTys pfvs ds eds : List EIdx}
    (h : tcmF stubCall n m vis q fto ftl pfo pfl us dso dsl lvls edso edsl = some (r, m'))
    (hS : StageR dn vis fe m a) (hbs : BSOK m q.toNat bs) (hus : H us) (hlv : H lvls)
    (hft : decHL m fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop m)
    (hpf : HSl0 m pfo pfl pfvs) (hds : HSl0 m dso dsl ds) (heds : HSl0 m edso edsl eds) (hP : RcMR m) :
    ∃ c a', (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds).run a =
      .ok (c, a') ∧ (r.headD 0 != 0) = c ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  cases n with
  | zero => simp [tcmF] at h
  | succ n => exact tcmW_ok dn fe vis n h hS hbs hus hlv hft hftb hpf hds heds hP

theorem tmnW_ok (n : Nat) : ∀ {m m' : Mem} {a : AState} {q fto ftl pfo pfl us dso dsl cto ctl nfo nfl : Word}
    {r : List Word} {bs : BlockShape} {formerTys pfvs ds : List EIdx} {ctors : List (IConstantVal × Nat)}
    {nfs : List NestCtorNf},
    tmnW stubCall n m vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl = some (r, m') →
    StageR dn vis fe m a → BSOK m q.toNat bs → H us →
    decHL m fto.toNat ftl.toNat = some formerTys → fto.toNat + ftl.toNat ≤ iwTop m →
    HSl0 m pfo pfl pfvs → HSl0 m dso dsl ds → PSlR decCN ctors cto ctl m → PSlR decNCN nfs nfo nfl m →
    RcMR m →
    ∃ ys a', (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs).run a = .ok (ys, a') ∧
      PSlR decNCN ys (r.headD 0) (r.tail.headD 0) m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  induction n with
  | zero => intro m m' a q fto ftl pfo pfl us dso dsl cto ctl nfo nfl r bs formerTys pfvs ds ctors nfs h
            simp [tmnW] at h
  | succ n ih =>
  intro m m' a q fto ftl pfo pfl us dso dsl cto ctl nfo nfl r bs formerTys pfvs ds ctors nfs h hS hbs hus hft hftb
    hpf hds hct hnf hP
  by_cases hl : nfl = 0
  · rw [tmnW_nil (h := hl)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hl
    have : nfs = [] := by
      have := decPL_length _ (hnf.1.get (OMono.decPL decNCN_mono _ _)); simpa using this
    subst this
    exact ⟨[], a, rfl, PSlR.nil _ _, hS, IWGrow.refl _, hP⟩
  rw [tmnW_cons (h := hl)] at h
  have hsz := hS.2.2.2.1
  obtain ⟨nf, nfs', rfl, hnf0, hnf'⟩ := hnf.uncons hl hsz
  cases h1 : tmnW stubCall n m vis q fto ftl pfo pfl us dso dsl cto ctl (nfo + 1) (nfl - 1) with
  | none => rw [h1] at h; simp [tmnK1] at h
  | some x =>
  obtain ⟨rr, m1⟩ := x
  rw [h1, tmnK1_some] at h
  obtain ⟨ys, a1, run1, hys, hS1, hg1, hP1⟩ := ih h1 hS hbs hus hft hftb hpf hds hct hnf' hP
  -- the head entry, in `m1`
  have hnfo : nfo.toNat < iwTop m := by
    have := hnf.2; have := (slice_step hl (hS.lt64 hnf.2)).2.2; omega
  have he : rdW (m1.arr64 IW) nfo = rdW (m.arr64 IW) nfo := by
    simp only [rdW]; rw [hg1.2.2.1 _ hnfo]
  rw [he] at h
  generalize hE : rdW (m.arr64 IW) nfo = e at h hnf0
  have hnf1 : DecB (fun m' => decNCN m' e.toNat) m1 nf := hnf0.grow (decNCN_mono _) hg1
  have hsz1 := hS1.2.2.2.1
  obtain ⟨hcH, hcD, hlH, hlD, hdsl⟩ := decNCN_fields hnf1 hsz1
  have hct1 := hct.grow (fun q => decCN_mono q) hg1
  cases h2 : chnW n m1 cto ctl (rdW (m1.arr64 IW) e) with
  | none => rw [h2] at h; simp [tmnK2] at h
  | some hv =>
  rw [h2] at h
  obtain ⟨hany, -⟩ := chnW_ok n m1 cto ctl _ hv ctors h2 (hct1.1.get (OMono.decPL decCN_mono _ _)) hcH
    (hS1.lt64 hct1.2)
  rw [hcD] at hany
  have hrun_tail : ∀ {α : Type} (k : List NestCtorNf → AM α),
      ((ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs') >>= k).run a = (k ys).run a1 := by
    intro α k; simp only [StateT.run_bind, run1]; rfl
  by_cases hh : hv = 0
  · rw [tmnK2_no (h := hh)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨ys, a1, ?_, hys, hS1, hg1, hP1⟩
    have hf : ctors.any (fun c => c.1.name == nf.ctor) = false := by rw [← hany, hh]; rfl
    rw [ConRon.Arena.targetMajorNfs, hrun_tail]; simp only [hf, Bool.false_eq_true, if_false]; rfl
  rw [tmnK2_yes (h := hh)] at h
  have ht : ctors.any (fun c => c.1.name == nf.ctor) = true := by rw [← hany]; simpa using hh
  cases h3 : tcmF stubCall n m1 vis q fto ftl pfo pfl us dso dsl (rdW (m1.arr64 IW) (e + 1)) (rdW (m1.arr64 IW) (e + 2))
      (rdW (m1.arr64 IW) (e + 3)) with
  | none => rw [h3] at h; simp [tmnK3] at h
  | some x =>
  obtain ⟨rk, m2⟩ := x
  rw [h3] at h
  obtain ⟨c, a2, run2, hc, hS2, hg2, hP2⟩ := tcmF_ok dn fe vis n h3 hS1 (hbs.grow hg1) hus hlH
    (by rw [decHL_grow hg1 hftb]; exact hft) (by have := hg1.1; omega) (hpf.grow hg1) (hds.grow hg1) hdsl hP1
  rw [hlD] at run2
  have hg12 := hg1.trans hg2
  by_cases hk : rk.headD 0 = 0
  · rw [tmnK3_drop (h := hk)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hc0 : c = false := by rw [← hc, hk]; rfl
    subst hc0
    refine ⟨ys, a2, ?_, hys.grow (fun q => decNCN_mono q) hg2, hS2, hg12, hP2⟩
    rw [ConRon.Arena.targetMajorNfs, hrun_tail]
    simp only [ht, if_true, StateT.run_bind, run2, except_ok_bind, Bool.false_eq_true, if_false]; rfl
  rw [tmnK3_keep (h := hk)] at h
  have hc1 : c = true := by rw [← hc]; simpa using hk
  subst hc1
  cases h4 : consW n m2 e (rr.headD 0) (rr.tail.headD 0) with
  | none => rw [h4] at h; simp [tmnK4] at h
  | some x =>
  obtain ⟨rc, m3⟩ := x
  rw [h4, tmnK4_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hS3, hg3, hps3, hf3⟩ := consW_pslr (fun q => decNCN_mono q) h4 hS2 (hys.grow (fun q => decNCN_mono q) hg2)
    (hnf1.grow (decNCN_mono _) hg2)
  refine ⟨nf :: ys, a2, ?_, by simpa using hps3, hS3, hg12.trans hg3, hP2.fr hf3⟩
  rw [ConRon.Arena.targetMajorNfs, hrun_tail]
  simp only [ht, if_true, StateT.run_bind, run2, except_ok_bind]; rfl

end rel

/-- **`target_major_nfs` refines `targetMajorNfs`** (through `target_class_match`'s contracts and
stubs): the class's shape (`BSOK`), former types, openers, parameters, constructors and the walk's
table entries decoded below the tops (the slices below the top unless empty), the walk memos well
formed; the kept entries a pointer slice decoded below the tops. Under `StageR`; the census link
is `targetMajorNfs_refinesC` (`IndT/RecCheckTmn`). -/
theorem targetMajorNfs_refines (p : Prog) (L : TmnLook p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl : Word)
    (bs : BlockShape) (formerTys pfvs ds : List EIdx) (ctors : List (IConstantVal × Nat)) (nfs : List NestCtorNf)
    (hS : StageR dn vis fe s₀.mem a₀) (hbs : BSOK s₀.mem q.toNat bs) (hus : H us)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hpf : HSl0 s₀.mem pfo pfl pfvs) (hds : HSl0 s₀.mem dso dsl ds) (hct : PSlR decCN ctors cto ctl s₀.mem)
    (hnf : PSlR decNCN nfs nfo nfl s₀.mem) (hP : RcMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_major_nfs"
      [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo, nfl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a₀ ∧
      PSlR decNCN (AM.res (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a₀)
        (r.headD 0) (r.tail.headD 0) s'.mem ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem; ⊤⦄ := by
  refine triple_post (tmn_spec p L stubCall (stubCall_spec p) n s₀ vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl) ?_
  rintro r s' ⟨hl', hm⟩
  obtain ⟨ys, a', run, hys, hS', hg, hP'⟩ := tmnW_ok dn fe vis n hm hS hbs hus hft hftb hpf hds hct hnf hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hres]; exact hys, by rw [hst]; exact hS', hg, hP'⟩

end L.Ind
