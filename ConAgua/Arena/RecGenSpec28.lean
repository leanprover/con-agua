import ConAgua.Arena.RecGenSpec27

/-!
# `classesNfs` (lane `indproofs4`, helper `cls`)

`classes_nfs(vis, p, ft.off, ft.len, tbl.off, tbl.len, ms.off, ms.len)`: every class with its
entries of `tbl` (`targetMajorNfs`). L walks `ms` with a `while` loop (the twin: a list recursion),
copying each class into a fresh 13-word record whose `nfs` slice is `target_major_nfs`'s result,
and writing the record's pointer into a result slice allocated before the loop. The loops are named
blocks here (`cnsLoop`, its copy loop `ncpLoop`; spliced back by `rfl`).

* **Writes below the top.** The result slice lies below the pool's top while the loop fills it, so
  the records' decodings are not kept by a pool growth alone. They are carried as words
  (`CnsRec`): the copied class words (decoded in the memory before the loop, `mb`), the `nfs`
  slice fresh above the result slice, its pointers those of `tbl` (decoded in `mb`). `CnsRec` is
  kept by every frame that changes no word outside the result slice below the old top (`FrX`).
* **`target_major_nfs`'s result** (`tmnW_okP`, `tmnW_ok` again with two more facts): above the
  pool's top at the call, or empty; its pointers among those of `tbl`. The class's constructors
  are taken decoded below the tops without a bound on an empty slice's offset.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The loops as named blocks -/

/-- The copy loop of `classesNfsL` (RecGen.lean), named for its spec. -/
-- con-ron: none — `classesNfsL`'s own inner loop (`rfl`), a named block for the proof
def ncpLoop : Stmt := lblk (vis, p, ftOff, ftLen, tblOff, tblLen, msOff, msLen, q, j, m, esOff,
    esLen, nm, k) {
  while k < 9 { IW.u64[nm + k] := IW.u64[m + k]; k += 1 }
}

/-- The loop of `classesNfsL` (RecGen.lean), named for its spec. -/
-- con-ron: none — `classesNfsL`'s own loop (`rfl`), a named block for the proof
def cnsLoop : Stmt := lblk (vis, p, ftOff, ftLen, tblOff, tblLen, msOff, msLen, q, j, m, esOff,
    esLen, nm, k) {
  while j < msLen {
    m := IW.u64[msOff + j];
    (esOff, esLen) := call target_major_nfs(vis, p, ftOff, ftLen, IW.u64[m + 11], IW.u64[m + 12],
      IW.u64[m + 1], IW.u64[m + 2], IW.u64[m + 3], IW.u64[m + 6], IW.u64[m + 7], tblOff, tblLen);
    nm := call iw_alloc(13);
    k := 0;
    ⟪ncpLoop⟫;
    IW.u64[nm + 9] := esOff;
    IW.u64[nm + 10] := esLen;
    IW.u64[nm + 11] := IW.u64[m + 11];
    IW.u64[nm + 12] := IW.u64[m + 12];
    IW.u64[q + j] := nm;
    j += 1
  }
}

/-- `classesNfsL`, with its loop spliced from `cnsLoop`. -/
-- con-ron: none — `classesNfsL` itself (`rfl`), its loops named blocks for the proof
def classesNfsL' : FunDecl := lfn (vis, p, ftOff, ftLen, tblOff, tblLen, msOff, msLen)
    locals (q, j, m, esOff, esLen, nm, k) {
  q := call iw_alloc(msLen);
  j := 0;
  ⟪cnsLoop⟫;
  return (q, msLen)
}

theorem classesNfsL_eq : classesNfsL = classesNfsL' := rfl

/-! ## The models -/

/-- **The model of the copy loop** at L fuel `f`: words `kk‥8` of the class `mw` copied to `nm`. -/
def ncpW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | f + 1, m, nm, mw, kk =>
    if kk < 9 then
      if (nm + kk).toNat < (m.arr64 IW).size then
        ncpW f (m.set64 IW (nm + kk) (rdW (m.arr64 IW) (mw + kk))) nm mw (kk + 1)
      else none
    else some m

section arms
variable (f : Nat) (m : Mem) (nm mw kk : Word)
theorem ncpW_exit (h : ¬ kk < 9) : ncpW (f + 1) m nm mw kk = some m := by
  simp only [ncpW]; rw [if_neg h]
theorem ncpW_step (h : kk < 9) (h1 : (nm + kk).toNat < (m.arr64 IW).size) :
    ncpW (f + 1) m nm mw kk = ncpW f (m.set64 IW (nm + kk) (rdW (m.arr64 IW) (mw + kk))) nm mw (kk + 1) := by
  simp only [ncpW]; rw [if_pos h, if_pos h1]
theorem ncpW_oob (h : kk < 9) (h1 : ¬ (nm + kk).toNat < (m.arr64 IW).size) : ncpW (f + 1) m nm mw kk = none := by
  simp only [ncpW]; rw [if_pos h, if_neg h1]
end arms

/-- The record's last four words and the result slot. -/
def wrTail (m : Mem) (nm mw eo el qr j : Word) : Mem :=
  let m1 := m.set64 IW (nm + 9) eo
  let m2 := m1.set64 IW (nm + 10) el
  let m3 := m2.set64 IW (nm + 11) (rdW (m2.arr64 IW) (mw + 11))
  let m4 := m3.set64 IW (nm + 12) (rdW (m3.arr64 IW) (mw + 12))
  m4.set64 IW (qr + j) nm

section model
variable (p : Prog)

/-- After the copy loop: the record's tail and the result slot (each store in bounds). -/
def cnsK3 (nm mw eo el qr j : Word) (rest : Mem → Option Mem) : Option Mem → Option Mem
  | none => none
  | some m =>
    if (nm + 9).toNat < (m.arr64 IW).size ∧ (nm + 10).toNat < (m.arr64 IW).size ∧
        (nm + 11).toNat < (m.arr64 IW).size ∧ (nm + 12).toNat < (m.arr64 IW).size ∧
        (qr + j).toNat < (m.arr64 IW).size then rest (wrTail m nm mw eo el qr j)
    else none

/-- After `iw_alloc(13)`: the copy loop. -/
def cnsK2 (k : Nat) (mw eo el qr j : Word) (rest : Mem → Option Mem) :
    Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m) => cnsK3 (r.headD 0) mw eo el qr j rest (ncpW (k + 1) m (r.headD 0) mw 0)

/-- After `target_major_nfs`: the fresh record. -/
def cnsK1 (k : Nat) (mw qr j : Word) (rest : Mem → Option Mem) : Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m) => cnsK2 k mw (r.headD 0) (r.tail.headD 0) qr j rest (callW p k "iw_alloc" [13] m)

/-- **The model of `classes_nfs`' loop** at L fuel `k`, from cursor `j`: the memory at the exit. -/
def cnsW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, q, fto, ftl, tblo, tbll, mo, ml, qr, j =>
    if j < ml then
      cnsK1 p k (rdW (m.arr64 IW) (mo + j)) qr j
        (fun m' => cnsW k m' vis q fto ftl tblo tbll mo ml qr (j + 1))
        (callW p k "target_major_nfs" [vis, q, fto, ftl,
          rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 11), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 12),
          rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 1), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 2),
          rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 3), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 6),
          rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 7), tblo, tbll] m)
    else some m

section arms
variable (k : Nat) (m : Mem) (vis q fto ftl tblo tbll mo ml qr j nm mw eo el : Word) (r : List Word)
  (rest : Mem → Option Mem)
theorem cnsK3_ok (h : (nm + 9).toNat < (m.arr64 IW).size ∧ (nm + 10).toNat < (m.arr64 IW).size ∧
    (nm + 11).toNat < (m.arr64 IW).size ∧ (nm + 12).toNat < (m.arr64 IW).size ∧
    (qr + j).toNat < (m.arr64 IW).size) :
    cnsK3 nm mw eo el qr j rest (some m) = rest (wrTail m nm mw eo el qr j) := by
  simp only [cnsK3]; rw [if_pos h]
theorem cnsK3_bad (h : ¬ ((nm + 9).toNat < (m.arr64 IW).size ∧ (nm + 10).toNat < (m.arr64 IW).size ∧
    (nm + 11).toNat < (m.arr64 IW).size ∧ (nm + 12).toNat < (m.arr64 IW).size ∧
    (qr + j).toNat < (m.arr64 IW).size)) :
    cnsK3 nm mw eo el qr j rest (some m) = none := by
  simp only [cnsK3]; rw [if_neg h]
theorem cnsK2_some : cnsK2 k mw eo el qr j rest (some (r, m)) =
    cnsK3 (r.headD 0) mw eo el qr j rest (ncpW (k + 1) m (r.headD 0) mw 0) := rfl
theorem cnsK1_some : cnsK1 p k mw qr j rest (some (r, m)) =
    cnsK2 k mw (r.headD 0) (r.tail.headD 0) qr j rest (callW p k "iw_alloc" [13] m) := rfl
theorem cnsW_exit (h : ¬ j < ml) : cnsW p (k + 1) m vis q fto ftl tblo tbll mo ml qr j = some m := by
  simp only [cnsW]; rw [if_neg h]
theorem cnsW_step (h : j < ml) : cnsW p (k + 1) m vis q fto ftl tblo tbll mo ml qr j =
    cnsK1 p k (rdW (m.arr64 IW) (mo + j)) qr j
      (fun m' => cnsW p k m' vis q fto ftl tblo tbll mo ml qr (j + 1))
      (callW p k "target_major_nfs" [vis, q, fto, ftl,
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 11), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 12),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 1), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 2),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 3), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 6),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 7), tblo, tbll] m) := by
  simp only [cnsW]; rw [if_pos h]
end arms

end model

/-- After the loop. -/
def cnfsK2 (qr ml : Word) : Option Mem → Option (List Word × Mem)
  | none => none
  | some m => some ([qr, ml], m)

/-- After the result slice's allocation: the loop. -/
def cnfsK1 (p : Prog) (n : Nat) (vis q fto ftl tblo tbll mo ml : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cnfsK2 (r.headD 0) ml (cnsW p (n + 1) m vis q fto ftl tblo tbll mo ml (r.headD 0) 0)

/-- **The model of `classes_nfs`** (exec fuel `n + 1`). -/
def cnfsW (p : Prog) (n : Nat) (m : Mem) (vis q fto ftl tblo tbll mo ml : Word) : Option (List Word × Mem) :=
  cnfsK1 p n vis q fto ftl tblo tbll mo ml (callW p n "iw_alloc" [ml] m)

theorem cnfsK2_some (qr ml : Word) (m : Mem) : cnfsK2 qr ml (some m) = some ([qr, ml], m) := rfl
theorem cnfsK1_some (p : Prog) (n : Nat) (vis q fto ftl tblo tbll mo ml : Word) (r : List Word) (m : Mem) :
    cnfsK1 p n vis q fto ftl tblo tbll mo ml (some (r, m)) =
      cnfsK2 (r.headD 0) ml (cnsW p (n + 1) m vis q fto ftl tblo tbll mo ml (r.headD 0) 0) := rfl

attribute [ind_grind] ncpW_exit ncpW_step ncpW_oob cnsK3_ok cnsK3_bad cnsK2_some cnsK1_some cnsW_exit
  cnsW_step cnfsK2_some cnfsK1_some

/-! ## The `vcgen` specs -/

theorem ncpLoop_spec (p : Prog) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p f ncpLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧
      s'.loc 3 = s₀.loc 3 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 6 = s₀.loc 6 ∧
      s'.loc 7 = s₀.loc 7 ∧ s'.loc 8 = s₀.loc 8 ∧ s'.loc 9 = s₀.loc 9 ∧ s'.loc 10 = s₀.loc 10 ∧
      s'.loc 11 = s₀.loc 11 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 13 = s₀.loc 13 ∧
      ncpW f s₀.mem (s₀.loc 13) (s₀.loc 10) (s₀.loc 14) = some s'.mem; ⊤⦄ := by
  induction f generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ f ih =>
    rw [exec, step_while (w := ncpLoop) rfl]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

theorem cnsLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p k cnsLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 7 = s₀.loc 7 ∧ s'.loc 8 = s₀.loc 8 ∧
      cnsW p k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)
        (s₀.loc 7) (s₀.loc 8) (s₀.loc 9) = some s'.mem; ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := cnsLoop) rfl]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih,
        callW_spec p k "target_major_nfs", callW_spec p k "iw_alloc",
        fun s => Triple.step_exec (ncpLoop_spec p (k + 1) s)] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq, wrTail]

theorem cnfsW_eq (p : Prog) (n : Nat) (m : Mem) (vis q fto ftl tblo tbll mo ml : Word) :
    cnfsW p n m vis q fto ftl tblo tbll mo ml = cnfsK1 p n vis q fto ftl tblo tbll mo ml (callW p n "iw_alloc" [ml] m) :=
  rfl

set_option maxHeartbeats 1600000 in
theorem cnfs_spec (p : Prog) (hp : p.lookup "classes_nfs" = some classesNfsL) (n : Nat) (s₀ : St)
    (vis q fto ftl tblo tbll mo ml : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "classes_nfs" [vis, q, fto, ftl, tblo, tbll, mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ cnfsW p n s₀.mem vis q fto ftl tblo tbll mo ml = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp, classesNfsL_eq]
  simp only [callFn, classesNfsL']
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "iw_alloc",
      fun s => Triple.step_exec (cnsLoop_spec p (n + 1) s)] <;>
    finish (gen := 40) (instances := 20000) [cnfsW_eq, loc_init4, loc_init5, loc_init6, loc_init7]

/-! ## `target_major_nfs`' result: fresh, its pointers those of the table -/

/-- A pointer list each of whose records decodes below the tops of `mb`. -/
abbrev PtrsB (mb : Mem) : List Nat → List NestCtorNf → Prop :=
  FA2 (fun v x => DecB (fun m => decNCN m v) mb x)

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/-- **`tmnW_ok` with the result's pointers**: those of the table (decoded in `mb`), the slice above
the pool's top at the call or empty; the constructors decoded below the tops (with no bound on an
empty slice's offset). -/
theorem tmnW_okP (mb : Mem) (n : Nat) :
    ∀ {m m' : Mem} {a : AState} {q fto ftl pfo pfl us dso dsl cto ctl nfo nfl : Word}
    {r : List Word} {bs : BlockShape} {formerTys pfvs ds : List EIdx} {ctors : List (IConstantVal × Nat)}
    {nfs : List NestCtorNf},
    tmnW stubCall n m vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl = some (r, m') →
    StageR dn vis fe m a → BSOK m q.toNat bs → H us →
    decHL m fto.toNat ftl.toNat = some formerTys → fto.toNat + ftl.toNat ≤ iwTop m →
    HSl0 m pfo pfl pfvs → HSl0 m dso dsl ds →
    DecB (fun m => decPL m (decCN m) cto.toNat ctl.toNat) m ctors → cto.toNat + ctl.toNat < 2 ^ 64 →
    PSlR decNCN nfs nfo nfl m → (∃ ps, decNL m nfo.toNat nfl.toNat = some ps ∧ PtrsB mb ps nfs) →
    RcMR m →
    ∃ ys a', (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs).run a = .ok (ys, a') ∧
      PSlR decNCN ys (r.headD 0) (r.tail.headD 0) m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' ∧
      (r.tail.headD 0 = 0 ∨ iwTop m ≤ (r.headD 0).toNat) ∧
      ∃ ps, decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some ps ∧ PtrsB mb ps ys := by
  induction n with
  | zero => intro m m' a q fto ftl pfo pfl us dso dsl cto ctl nfo nfl r bs formerTys pfvs ds ctors nfs h
            simp [tmnW] at h
  | succ n ih =>
  intro m m' a q fto ftl pfo pfl us dso dsl cto ctl nfo nfl r bs formerTys pfvs ds ctors nfs h hS hbs hus hft hftb
    hpf hds hct hctb hnf hptr hP
  by_cases hl : nfl = 0
  · rw [tmnW_nil (h := hl)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hl
    have : nfs = [] := by
      have := decPL_length _ (hnf.1.get (OMono.decPL decNCN_mono _ _)); simpa using this
    subst this
    exact ⟨[], a, rfl, PSlR.nil _ _, hS, IWGrow.refl _, hP, .inl rfl, [], by simp [decNL], FA2.nil⟩
  rw [tmnW_cons (h := hl)] at h
  have hsz := hS.2.2.2.1
  obtain ⟨nf, nfs', rfl, hnf0, hnf'⟩ := hnf.uncons hl hsz
  obtain ⟨ps, hps, hpb⟩ := hptr
  have hb64 := hS.lt64 hnf.2
  obtain ⟨e1, e2, hl0⟩ := slice_step hl hb64
  obtain ⟨L, hL⟩ : ∃ L, nfl.toNat = L + 1 := ⟨nfl.toNat - 1, by omega⟩
  rw [hL, decNL_succ] at hps
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hps
  obtain ⟨v, hv, ps', hps', rfl⟩ := hps
  cases hpb with
  | cons hpv hpb' =>
  cases h1 : tmnW stubCall n m vis q fto ftl pfo pfl us dso dsl cto ctl (nfo + 1) (nfl - 1) with
  | none => rw [h1] at h; simp [tmnK1] at h
  | some x =>
  obtain ⟨rr, m1⟩ := x
  rw [h1, tmnK1_some] at h
  obtain ⟨ys, a1, run1, hys, hS1, hg1, hP1, hfr1, pr, hpr, hprb⟩ := ih h1 hS hbs hus hft hftb hpf hds hct hctb hnf'
    ⟨ps', by rw [e1, e2, hL]; simpa using hps', hpb'⟩ hP
  have hnfo : nfo.toNat < iwTop m := by have := hnf.2; omega
  have he : rdW (m1.arr64 IW) nfo = rdW (m.arr64 IW) nfo := by
    simp only [rdW]; rw [hg1.2.2.1 _ hnfo]
  rw [he] at h
  have hev : rdW (m.arr64 IW) nfo = UInt64.ofNat v := by
    have := (iwN_rdW hv (by omega)).1; rwa [UInt64.ofNat_toNat] at this
  have hvb : v < 2 ^ 64 := (iwN_rdW hv (by omega)).2
  generalize hE : rdW (m.arr64 IW) nfo = e at h hnf0
  have heT : e.toNat = v := by rw [← hE, hev, UInt64.toNat_ofNat_of_lt' hvb]
  have hnf1 : DecB (fun m' => decNCN m' e.toNat) m1 nf := hnf0.grow (decNCN_mono _) hg1
  have hsz1 := hS1.2.2.2.1
  obtain ⟨hcH, hcD, hlH, hlD, hdsl⟩ := decNCN_fields hnf1 hsz1
  have hct1 := hct.grow (OMono.decPL decCN_mono _ _) hg1
  cases h2 : chnW n m1 cto ctl (rdW (m1.arr64 IW) e) with
  | none => rw [h2] at h; simp [tmnK2] at h
  | some hv' =>
  rw [h2] at h
  obtain ⟨hany, -⟩ := chnW_ok n m1 cto ctl _ hv' ctors h2 (hct1.get (OMono.decPL decCN_mono _ _)) hcH hctb
  rw [hcD] at hany
  have hrun_tail : ∀ {α : Type} (k : List NestCtorNf → AM α),
      ((ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs') >>= k).run a = (k ys).run a1 := by
    intro α k; simp only [StateT.run_bind, run1]; rfl
  have hprg : ∀ {m2 : Mem}, IWGrow m1 m2 → decNL m2 (rr.headD 0).toNat (rr.tail.headD 0).toNat = some pr := by
    intro m2 hg; rw [decNL_grow hg hys.2]; exact hpr
  by_cases hh : hv' = 0
  · rw [tmnK2_no (h := hh)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨ys, a1, ?_, hys, hS1, hg1, hP1, by simpa using hfr1, pr, by simpa using hpr, hprb⟩
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
    refine ⟨ys, a2, ?_, hys.grow (fun q => decNCN_mono q) hg2, hS2, hg12, hP2, by simpa using hfr1, pr,
      by simpa using hprg hg2, hprb⟩
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
  have hys2 := hys.grow (fun q => decNCN_mono q) hg2
  obtain ⟨hr, hd, -, -, -, -⟩ := consW_decN h4 hS2.2.2.2.1 hS2.2.2.2.2.2 hys2.2 (hprg hg2)
  subst hr
  refine ⟨nf :: ys, a2, ?_, by simpa using hps3, hS3, hg12.trans hg3, hP2.fr hf3, ?_, e.toNat :: pr,
    by simpa using hd, ?_⟩
  · rw [ConRon.Arena.targetMajorNfs, hrun_tail]
    simp only [ht, if_true, StateT.run_bind, run2, except_ok_bind]; rfl
  · right; simp only [List.headD_cons]; exact hg12.1
  · rw [heT]; exact FA2.cons hpv hprb

end rel

/-! ## Frames: one word changed below the top -/

theorem cnsTop_set (m : Mem) (k v : Word) : iwTop (m.set64 IW k v) = iwTop m := by
  simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]

/-- The pool grew, every word below the old top kept but the one at `x`. -/
def FrX (x : Nat) (m m' : Mem) : Prop :=
  iwTop m ≤ iwTop m' ∧ ∀ i < iwTop m, i ≠ x → (m'.arr64 IW)[i]? = (m.arr64 IW)[i]?

theorem FrX.of_grow {x : Nat} {m m' : Mem} (h : IWGrow m m') : FrX x m m' :=
  ⟨h.1, fun i hi _ => h.2.2.1 i hi⟩

theorem FrX.trans_grow {x : Nat} {m₁ m₂ m₃ : Mem} (h₁ : FrX x m₁ m₂) (h₂ : IWGrow m₂ m₃) : FrX x m₁ m₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun i hi hx => by rw [h₂.2.2.1 i (by have := h₁.1; omega)]; exact h₁.2 i hi hx⟩

theorem FrX.set {x : Nat} {m₁ m₂ : Mem} (h₁ : FrX x m₁ m₂) (k v : Word) (hk : k.toNat = x) :
    FrX x m₁ (m₂.set64 IW k v) := by
  refine ⟨by rw [cnsTop_set]; exact h₁.1, fun i hi hx => ?_⟩
  rw [set64IW_get, if_neg (fun e => hx (by omega))]; exact h₁.2 i hi hx

/-! ## The records, as words -/

/-- **A class record written by the loop**, as words: the class `p0`'s words but `nfs` (decoded
in `mb`) at a source pointer `p0` satisfying `S`, the `nfs` slice above `hi` (or empty), its pointers
those of `PtrsB`. -/
def CnsRec (mb : Mem) (S : Nat → Prop) (hi : Nat) (m : Mem) (w : Nat) (M : TargetMajor) : Prop :=
  ∃ p0 src eo el ps, DecB (fun m => decTM m p0) mb src ∧ S p0 ∧ hi ≤ w ∧ w + 13 ≤ iwTop m ∧
    (∀ k < 13, k ≠ 9 → k ≠ 10 → (m.arr64 IW)[w + k]? = (iwA (truncM mb))[p0 + k]?) ∧
    iwN m (w + 9) = some eo ∧ iwN m (w + 10) = some el ∧ decNL m eo el = some ps ∧
    eo + el ≤ iwTop m ∧ (el = 0 ∨ hi ≤ eo) ∧ PtrsB mb ps M.nfs ∧ M = { src with nfs := M.nfs }

/-- A source class of the loop: a pointer of the classes' slice `(mo, ml)` in `mb`. -/
def CnsSrc (mb : Mem) (mo ml : Word) (p0 : Nat) : Prop := ∃ c < ml.toNat, iwN mb (mo.toNat + c) = some p0

theorem decNL_frX {x : Nat} {m m' : Mem} (h : FrX x m m') {o l : Nat} (hb : o + l ≤ iwTop m)
    (hx : l = 0 ∨ x < o ∨ o + l ≤ x) : decNL m' o l = decNL m o l := by
  simp only [decNL]
  apply mapM_opt_congr
  intro j hj
  have hj' : j < l := List.mem_range.mp hj
  simp only [iwN, nat?, iwA]
  rw [h.2 (o + j) (by omega) (by omega)]

theorem CnsRec.frame {mb : Mem} {S : Nat → Prop} {hi x : Nat} {m m' : Mem} {w : Nat} {M : TargetMajor}
    (h : CnsRec mb S hi m w M) (hF : FrX x m m') (hx : x < hi) : CnsRec mb S hi m' w M := by
  obtain ⟨p0, src, eo, el, ps, hsrc, hS0, hw, htop, hwords, h9, h10, hps, hb, hfr, hpb, hM⟩ := h
  refine ⟨p0, src, eo, el, ps, hsrc, hS0, hw, Nat.le_trans htop hF.1, fun k hk h9 h10 => ?_, ?_, ?_, ?_,
    Nat.le_trans hb hF.1, hfr, hpb, hM⟩
  · rw [hF.2 _ (by omega) (by omega)]; exact hwords k hk h9 h10
  · simp only [iwN, nat?, iwA] at h9 ⊢; rw [hF.2 _ (by omega) (by omega)]; exact h9
  · simp only [iwN, nat?, iwA] at h10 ⊢; rw [hF.2 _ (by omega) (by omega)]; exact h10
  · rw [decNL_frX hF hb (by omega)]; exact hps

theorem PtrsB.mapM {mb m : Mem} (hg : IWGrow mb m) :
    ∀ {ps : List Nat} {xs : List NestCtorNf}, PtrsB mb ps xs → ps.mapM (decNCN (truncM m)) = some xs
  | [], [], .nil => rfl
  | v :: ps, x :: xs, .cons h1 h2 => by
    simp only [List.mapM_cons, show decNCN (truncM m) v = some x from h1.grow (decNCN_mono _) hg,
      PtrsB.mapM hg h2]; rfl

/-- **A record written by the loop decodes below the tops.** -/
theorem CnsRec.decB {mb : Mem} {S : Nat → Prop} {hi : Nat} {m : Mem} {w : Nat} {M : TargetMajor}
    (hg : IWGrow mb m) (h : CnsRec mb S hi m w M) : DecB (fun m => decTM m w) m M := by
  obtain ⟨p0, src, eo, el, ps, hsrc, -, hw, htop, hwords, h9, h10, hps, hb, -, hpb, hM⟩ := h
  have ew : ∀ k, k < 13 → k ≠ 9 → k ≠ 10 → (iwA (truncM m))[w + k]? = (iwA (truncM mb))[p0 + k]? :=
    fun k hk a b => by rw [truncM_iw_get?, if_pos (by omega)]; exact hwords k hk a b
  have e : ∀ k, k < 13 → k ≠ 9 → k ≠ 10 → iwN (truncM m) (w + k) = iwN (truncM mb) (p0 + k) :=
    fun k hk a b => by simp only [iwN, nat?, ew k hk a b]
  have eh : ∀ {kk : IdxKind} k, k < 13 → k ≠ 9 → k ≠ 10 →
      (iwH (truncM m) (w + k) : Option (Idx kk)) = iwH (truncM mb) (p0 + k) :=
    fun k hk a b => by simp only [iwH, hd?, ew k hk a b]
  have eh0 : ∀ {kk : IdxKind}, (iwH (truncM m) w : Option (Idx kk)) = iwH (truncM mb) p0 := by
    intro kk; have := eh (kk := kk) 0 (by omega) (by omega) (by omega); simpa using this
  have e9 : iwN (truncM m) (w + 9) = some eo := by rw [iwN_truncM (by omega)]; exact h9
  have e10 : iwN (truncM m) (w + 10) = some el := by rw [iwN_truncM (by omega)]; exact h10
  have hnfs : decPL (truncM m) (decNCN (truncM m)) eo el = some M.nfs := by
    rw [decPL_eq_bind, show decNL (truncM m) eo el = some ps from decNL_decB hps hb]
    exact PtrsB.mapM hg hpb
  have hs : decTM (truncM mb) p0 = some src := hsrc
  -- the class's other slices, grown
  have gHL : ∀ {kk : IdxKind} (o l : Nat) (xs : List (Idx kk)), decHL (truncM mb) o l = some xs →
      decHL (truncM m) o l = some xs := fun o l xs hx =>
    (show DecB (fun m => (decHL m o l : Option (List (Idx _)))) mb xs from hx).grow (OMono.decHL _ _) hg
  have gCN : ∀ (o l : Nat) (xs : List (IConstantVal × Nat)), decPL (truncM mb) (decCN (truncM mb)) o l = some xs →
      decPL (truncM m) (decCN (truncM m)) o l = some xs := fun o l xs hx =>
    (show DecB (fun m => decPL m (decCN m) o l) mb xs from hx).grow (OMono.decPL decCN_mono _ _) hg
  simp only [decTM, decAt, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hs
  obtain ⟨ind, hind, lv, hlv, ds, ⟨o2, h2, l2, h3, hds⟩, nPc, h4, nIdx, h5, ctors, ⟨o6, h6, l6, h7, hct⟩, w8, h8,
    nfs0, -, pfvs, ⟨o11, h11, l11, h12, hpf⟩, rfl⟩ := hs
  show decTM (truncM m) w = some M
  rw [hM]
  simp only [decTM, decAt, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
  refine ⟨ind, by rw [eh0]; exact hind, lv, by rw [eh 1 (by omega) (by omega) (by omega)]; exact hlv,
    ds, ⟨o2, by rw [e 2 (by omega) (by omega) (by omega)]; exact h2, l2,
      by rw [show w + 2 + 1 = w + 3 by omega, e 3 (by omega) (by omega) (by omega)]; simpa using h3, gHL _ _ _ hds⟩,
    nPc, by rw [e 4 (by omega) (by omega) (by omega)]; exact h4,
    nIdx, by rw [e 5 (by omega) (by omega) (by omega)]; exact h5,
    ctors, ⟨o6, by rw [e 6 (by omega) (by omega) (by omega)]; exact h6, l6,
      by rw [show w + 6 + 1 = w + 7 by omega, e 7 (by omega) (by omega) (by omega)]; simpa using h7, gCN _ _ _ hct⟩,
    w8, by rw [e 8 (by omega) (by omega) (by omega)]; exact h8,
    M.nfs, ⟨eo, e9, el, by simpa using e10, hnfs⟩,
    pfvs, ⟨o11, by rw [e 11 (by omega) (by omega) (by omega)]; exact h11, l11,
      by rw [show w + 11 + 1 = w + 12 by omega, e 12 (by omega) (by omega) (by omega)]; simpa using h12, gHL _ _ _ hpf⟩,
    rfl⟩

/-! ## Small pieces -/

theorem ptrsB_of_mapM {mb : Mem} : ∀ {ps : List Nat} {xs : List NestCtorNf},
    ps.mapM (decNCN (truncM mb)) = some xs → PtrsB mb ps xs
  | [], xs, h => by simp at h; subst h; exact .nil
  | v :: ps, xs, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, ys, hys, rfl⟩ := h
    exact .cons hx (ptrsB_of_mapM hys)

theorem iwN_get {m : Mem} {i v : Nat} (h : iwN m i = some v) : ∃ w, (iwA m)[i]? = some w := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, -⟩ := h; exact ⟨w, hw⟩

theorem iwH_get {kk : IdxKind} {m : Mem} {i : Nat} {x : Idx kk} (h : iwH m i = some x) :
    ∃ w, (iwA m)[i]? = some w := by
  simp only [iwH, hd?] at h
  cases hw : (iwA m)[i]? with
  | none => rw [hw] at h; cases h
  | some w => exact ⟨w, rfl⟩

/-- **Every word of a decoded class record is read.** -/
theorem decTM_get {m : Mem} {q : Nat} {M : TargetMajor} (h : decTM m q = some M) :
    ∀ k < 13, ∃ w, (iwA m)[q + k]? = some w := by
  simp only [decTM, decAt, bind, Option.bind_eq_some_iff] at h
  obtain ⟨ind, hind, lv, hlv, ds, ⟨o2, h2, l2, h3, -⟩, nPc, h4, nIdx, h5, ctors, ⟨o6, h6, l6, h7, -⟩, w8, h8,
    nfs0, ⟨o9, h9, l9, h10, -⟩, pfvs, ⟨o11, h11, l11, h12, -⟩, -⟩ := h
  intro k hk
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨
    k = 11 ∨ k = 12 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact iwH_get (by simpa using hind)
  · exact iwH_get hlv
  · exact iwN_get h2
  · exact iwN_get h3
  · exact iwN_get h4
  · exact iwN_get h5
  · exact iwN_get h6
  · exact iwN_get h7
  · exact iwN_get h8
  · exact iwN_get h9
  · exact iwN_get h10
  · exact iwN_get h11
  · exact iwN_get h12

set_option maxHeartbeats 1000000 in
/-- The class record's words that `target_major_nfs` reads, below the tops. -/
theorem cnsTM_parts {m : Mem} {w : Word} {src : TargetMajor} (h : DecB (fun m => decTM m w.toNat) m src)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    H (rdW (m.arr64 IW) (w + 1)) ∧ decI (rdW (m.arr64 IW) (w + 1)) = src.lvls ∧
    HSl0 m (rdW (m.arr64 IW) (w + 2)) (rdW (m.arr64 IW) (w + 3)) src.ds ∧
    HSl0 m (rdW (m.arr64 IW) (w + 11)) (rdW (m.arr64 IW) (w + 12)) src.pfvs ∧
    DecB (fun m' => decPL m' (decCN m') (rdW (m.arr64 IW) (w + 6)).toNat (rdW (m.arr64 IW) (w + 7)).toNat)
      m src.ctors ∧
    (rdW (m.arr64 IW) (w + 6)).toNat + (rdW (m.arr64 IW) (w + 7)).toNat < 2 ^ 64 := by
  have h' : decTM (truncM m) w.toNat = some src := h
  simp only [decTM, decAt, bind, Option.bind_eq_some_iff] at h'
  obtain ⟨ind, -, lv, hlv, ds, ⟨o2, h2, l2, h3, hds⟩, nPc, -, nIdx, -, ctors, ⟨o6, h6, l6, h7, hct⟩, w8, -,
    nfs0, -, pfvs, ⟨o11, h11, l11, h12, hpf⟩, hM⟩ := h'
  simp only [pure, Option.some.injEq] at hM
  subst hM
  obtain ⟨hl1, hl2⟩ := truncH (i := 1) hlv hsz
  have hsd := truncSl (w := w) (i := 2) h2 h3 hds hsz
  have hsp := truncSl (w := w) (i := 11) h11 h12 hpf hsz
  obtain ⟨-, h6m⟩ := rec2IwN_trunc h6
  obtain ⟨-, h7m⟩ := rec2IwN_trunc h7
  obtain ⟨e6, b6⟩ := iwN_rdW_at (w := w) (k := 6) h6m hsz
  obtain ⟨e7, b7⟩ := iwN_rdW_at (w := w) (k := 7) (by simpa [Nat.add_assoc] using h7m) hsz
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
    show UInt64.ofNat (2 + 1) = (3 : Word) from rfl, show UInt64.ofNat 11 = (11 : Word) from rfl,
    show UInt64.ofNat (11 + 1) = (12 : Word) from rfl, show UInt64.ofNat 6 = (6 : Word) from rfl,
    show UInt64.ofNat 7 = (7 : Word) from rfl] at hl1 hl2 hsd hsp e6 e7
  rw [e6, e7, UInt64.toNat_ofNat_of_lt' b6, UInt64.toNat_ofNat_of_lt' b7]
  refine ⟨hl1, hl2, hsd, hsp, hct, ?_⟩
  rcases Nat.eq_zero_or_pos l6 with hz | hpos
  · subst hz; omega
  · obtain ⟨v, hv, -⟩ := decPL_getH (truncM m) hct (l6 - 1) (by omega)
    obtain ⟨hlt, -⟩ := rec2IwN_trunc hv
    have := (rdW (m.arr64 CTL) 200).toNat_lt
    simp only [iwTop] at hlt; omega

/-- `rdW` across a store to another word. -/
theorem rdW_set_ne {m : Mem} {a x v : Word} (h : x.toNat ≠ a.toNat) :
    rdW ((m.set64 IW a v).arr64 IW) x = rdW (m.arr64 IW) x := by
  simp only [rdW, set64IW_get]; rw [if_neg (fun e => h e.1)]

/-! ## The copy loop -/

/-- **The copy loop is a run of stores at or above `nm`.** -/
theorem ncpW_ind (nm mw : Word) (hnm : nm.toNat + 9 < 2 ^ 64) (P : Mem → Prop)
    (hP : ∀ m x v, P m → nm.toNat ≤ x.toNat → P (m.set64 IW x v)) :
    ∀ (f : Nat) (m m' : Mem) (kk : Word), ncpW f m nm mw kk = some m' → kk.toNat ≤ 9 → P m → P m'
  | 0, _, _, _, h, _, _ => by simp [ncpW] at h
  | f + 1, m, m', kk, h, hk, hm => by
    by_cases hlt : kk < 9
    · by_cases h1 : (nm + kk).toNat < (m.arr64 IW).size
      · rw [ncpW_step (h := hlt) (h1 := h1)] at h
        have hk' : kk.toNat < 9 := UInt64.lt_iff_toNat_lt.mp hlt
        refine ncpW_ind nm mw hnm P hP f _ m' (kk + 1) h (by rw [UInt64.toNat_add]; simp; omega) (hP _ _ _ hm ?_)
        rw [UInt64.toNat_add]; simp; omega
      · rw [ncpW_oob (h := hlt) (h1 := h1)] at h; cases h
    · rw [ncpW_exit (h := hlt)] at h
      simp only [Option.some.injEq] at h; subst h; exact hm

/-- **The copy loop's words**: words `kk‥8` of `mw` at `nm`, every other word kept. -/
theorem ncpW_words (nm mw : Word) (hnm : nm.toNat + 9 < 2 ^ 64) (hmw : mw.toNat + 9 ≤ nm.toNat) :
    ∀ (f : Nat) (m m' : Mem) (kk : Word), ncpW f m nm mw kk = some m' → kk.toNat ≤ 9 →
    (∀ i, (i < nm.toNat + kk.toNat ∨ nm.toNat + 9 ≤ i) → (m'.arr64 IW)[i]? = (m.arr64 IW)[i]?) ∧
    (∀ t, kk.toNat ≤ t → t < 9 → (m'.arr64 IW)[nm.toNat + t]? = some (rdW (m.arr64 IW) (mw + UInt64.ofNat t)))
  | 0, _, _, _, h, _ => by simp [ncpW] at h
  | f + 1, m, m', kk, h, hk => by
    by_cases hlt : kk < 9
    · by_cases h1 : (nm + kk).toNat < (m.arr64 IW).size
      · rw [ncpW_step (h := hlt) (h1 := h1)] at h
        have hk' : kk.toNat < 9 := UInt64.lt_iff_toNat_lt.mp hlt
        have hk1 : (kk + 1).toNat = kk.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
        have hnk : (nm + kk).toNat = nm.toNat + kk.toNat := by rw [UInt64.toNat_add]; simp; omega
        obtain ⟨g1, g2⟩ := ncpW_words nm mw hnm hmw f _ m' (kk + 1) h (by omega)
        refine ⟨fun i hi => ?_, fun t ht1 ht2 => ?_⟩
        · rw [g1 i (by omega), set64IW_get, if_neg (by omega)]
        · rcases Nat.eq_or_lt_of_le ht1 with e | e
          · subst e
            rw [g1 _ (by omega), set64IW_get, if_pos ⟨by omega, by omega⟩]
            simp
          · rw [g2 t (by omega) ht2, rdW_set_ne]
            rw [UInt64.toNat_add, hnk]; simp; omega
      · rw [ncpW_oob (h := hlt) (h1 := h1)] at h; cases h
    · rw [ncpW_exit (h := hlt)] at h
      simp only [Option.some.injEq] at h; subst h
      have : kk.toNat = 9 := by
        have : ¬ kk.toNat < 9 := fun h' => hlt (UInt64.lt_iff_toNat_lt.mpr h')
        omega
      exact ⟨fun _ _ => rfl, fun t ht1 ht2 => by omega⟩

/-! ## The loop refines `classesNfs` -/

/-- The lookups of `classes_nfs`. -/
structure CnsProg (p : Prog) : Prop where
  tmn : TmnLook p
  ha : p.lookup "iw_alloc" = some iwAlloc
  cns : p.lookup "classes_nfs" = some classesNfsL

section loop
variable {p : Prog} (P : CnsProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (vis q fto ftl tblo tbll mo ml qr : Word) (bs : BlockShape) (formerTys : List EIdx)
  (tbl : List NestCtorNf) (ms : List TargetMajor) (mb : Mem)
include P

/-- **`classes_nfs`' loop refines `classesNfs`** on the classes from the cursor `j`: the records
written so far (`acc`, their pointers `ws` at the result slice `qr`) kept as words (`CnsRec`). -/
theorem cnsW_ok (hq : qr.toNat = iwTop mb) (hms : PSlR decTM ms mo ml mb) (htbl : PSlR decNCN tbl tblo tbll mb)
    (hbs : BSOK mb q.toNat bs) (hft : decHL mb fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop mb) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (j : Word) (acc : List TargetMajor) (ws : List Nat),
    cnsW p k m vis q fto ftl tblo tbll mo ml qr j = some m' →
    StageR dn vis fe m a → IWGrow mb m → qr.toNat + ml.toNat ≤ iwTop m → RcMR m → j ≤ ml →
    decNL m qr.toNat j.toNat = some ws → FA2 (CnsRec mb (CnsSrc mb mo ml) (qr.toNat + ml.toNat) m) ws acc →
    ∃ rest a', (ConRon.Arena.classesNfs V fe bs formerTys tbl (ms.drop j.toNat)).run a = .ok (rest, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow mb m' ∧ qr.toNat + ml.toNat ≤ iwTop m' ∧ RcMR m' ∧
      ∃ ws', decNL m' qr.toNat ml.toNat = some ws' ∧ FA2 (CnsRec mb (CnsSrc mb mo ml) (qr.toNat + ml.toNat) m') ws' (acc ++ rest) := by
  have hms0 : decPL (truncM mb) (decTM (truncM mb)) mo.toNat ml.toNat = some ms := hms.1
  have hlen := decPL_length _ hms0
  obtain ⟨tps, -, htps, hmap⟩ := sumDecNL_of_decB htbl.1
  have htpb : PtrsB mb tps tbl := ptrsB_of_mapM hmap
  induction k with
  | zero => intro m m' a j acc ws h; simp [cnsW] at h
  | succ k ih =>
  intro m m' a j acc ws h hS hg htop hP hje hws hacc
  have hsz := hS.2.2.2.1
  have hjm : j.toNat ≤ ml.toNat := UInt64.le_iff_toNat_le.mp hje
  have hT := (rdW (m.arr64 CTL) 200).toNat_lt
  by_cases hj : ¬ j < ml
  · rw [cnsW_exit (h := hj)] at h
    simp only [Option.some.injEq] at h; subst h
    have h1 : ml.toNat ≤ j.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hj
    have hjeq : j.toNat = ml.toNat := by omega
    have : ms.drop j.toNat = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]
    refine ⟨[], a, rfl, hS, hg, htop, hP, ws, by rw [← hjeq]; exact hws, by simpa using hacc⟩
  simp only [Decidable.not_not] at hj
  have hjl : j.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp hj
  have hml := ml.toNat_lt
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  -- the class `j`
  obtain ⟨p0, hp0, hsrc⟩ := decPL_getH (truncM mb) hms0 j.toNat hjl
  obtain ⟨hp0t, hp0m⟩ := rec2IwN_trunc hp0
  have hp0m' : iwN m (mo.toNat + j.toNat) = some p0 := by
    simp only [iwN, nat?, iwA] at hp0m ⊢; rw [hg.2.2.1 _ hp0t]; exact hp0m
  obtain ⟨hrd, hp0b⟩ := iwN_rdW_at (w := mo) (k := j.toNat) hp0m' hsz
  rw [show mo + UInt64.ofNat j.toNat = mo + j by simp] at hrd
  rw [cnsW_step (h := hj), hrd] at h
  have hp0T : (UInt64.ofNat p0 : Word).toNat = p0 := UInt64.toNat_ofNat_of_lt' hp0b
  have hsrcmb : DecB (fun m => decTM m p0) mb (ms[j.toNat]'(by omega)) := by
    show decTM (truncM mb) p0 = _; rw [hsrc]
  have hsrcB : DecB (fun m => decTM m (UInt64.ofNat p0 : Word).toNat) m (ms[j.toNat]'(by omega)) := by
    rw [hp0T]; exact hsrcmb.grow (decTM_mono _) hg
  obtain ⟨hlH, hlD, hdsS, hpfS, hctB, hctb⟩ := cnsTM_parts hsrcB hsz
  -- `target_major_nfs`
  cases c1 : callW p k "target_major_nfs" [vis, q, fto, ftl,
      rdW (m.arr64 IW) (UInt64.ofNat p0 + 11), rdW (m.arr64 IW) (UInt64.ofNat p0 + 12),
      rdW (m.arr64 IW) (UInt64.ofNat p0 + 1), rdW (m.arr64 IW) (UInt64.ofNat p0 + 2),
      rdW (m.arr64 IW) (UInt64.ofNat p0 + 3), rdW (m.arr64 IW) (UInt64.ofNat p0 + 6),
      rdW (m.arr64 IW) (UInt64.ofNat p0 + 7), tblo, tbll] m with
  | none => rw [c1] at h; simp [cnsK1] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [c1, cnsK1_some] at h
  obtain ⟨s1, hs1, -, hw1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (tmn_spec p P.tmn stubCall (stubCall_spec p) k _ vis q fto ftl
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 11)) (rdW (m.arr64 IW) (UInt64.ofNat p0 + 12))
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 1)) (rdW (m.arr64 IW) (UInt64.ofNat p0 + 2))
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 3)) (rdW (m.arr64 IW) (UInt64.ofNat p0 + 6))
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 7)) tblo tbll) c1
  simp only at hs1 hw1; subst hs1
  obtain ⟨es, a1, run1, hes, hS1, hg1, hP1, hfr, pse, hpse, hpseb⟩ := tmnW_okP dn fe vis mb k hw1 hS
    (hbs.grow hg) hlH (by rw [decHL_grow hg hftb]; exact hft) (by have := hg.1; omega) hpfS hdsS hctB hctb
    (htbl.grow (fun q => decNCN_mono q) hg) ⟨tps, by rw [decNL_grow hg htbl.2]; exact htps, htpb⟩ hP
  rw [hlD] at run1
  -- `iw_alloc(13)`
  cases c2 : callW p k "iw_alloc" [13] s1.mem with
  | none => rw [c2] at h; simp [cnsK2] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [c2, cnsK2_some] at h
  obtain ⟨s2, hs2, -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩) (iwAlloc_specW p P.ha k _ 13) c2
  simp only at hs2 hw2; subst hs2
  obtain ⟨hS2, hg2, hnm, ht2⟩ := allocW_stage hw2 hS1
  have hP2 := hP1.fr (allocW_mfr hw2)
  generalize hNM : r2.headD 0 = nm at h hnm
  have h13 : (13 : Word).toNat = 13 := rfl
  rw [h13] at ht2
  have hI2 := hS2.2.1
  have hnmb : nm.toNat + 13 < 2 ^ 64 := by have := hS2.2.2.2.1; omega
  have hp13 : p0 + 13 ≤ nm.toNat := by
    obtain ⟨_, hw12⟩ := decTM_get hsrc 12 (by omega)
    have := (truncM_iw_get hw12).1
    have := hg.1; have := hg1.1; omega
  have hmw : (UInt64.ofNat p0 : Word).toNat + 9 ≤ nm.toNat := by rw [hp0T]; omega
  -- the copy loop
  cases c3 : ncpW (k + 1) s2.mem nm (UInt64.ofNat p0) 0 with
  | none => rw [c3] at h; simp [cnsK3] at h
  | some m3 =>
  rw [c3] at h
  obtain ⟨g1, g2⟩ := ncpW_words nm _ (by omega) hmw (k + 1) _ _ 0 c3 (by simp)
  have hS3 := ncpW_ind nm (UInt64.ofNat p0) (by omega) (fun m'' => StageR dn vis fe m'' a1)
    (fun _ _ _ h _ => h.set_iw _ _) (k + 1) _ _ 0 c3 (by simp) hS2
  have hg3 := ncpW_ind nm (UInt64.ofNat p0) (by omega) (fun m'' => IWGrow s1.mem m'')
    (fun _ x _ h hx => h.set_iw _ _ (by omega)) (k + 1) _ _ 0 c3 (by simp) hg2
  have hP3 := ncpW_ind nm (UInt64.ofNat p0) (by omega) (fun m'' => MFr [] [] s2.mem m'')
    (fun _ x _ h _ => h.trans (MFr.set_iw _ _ _)) (k + 1) _ _ 0 c3 (by simp) (MFr.refl _ _ _)
  have ht3 := ncpW_ind nm (UInt64.ofNat p0) (by omega) (fun m'' => iwTop m'' = iwTop s2.mem)
    (fun _ x _ h _ => by rw [cnsTop_set]; exact h) (k + 1) _ _ 0 c3 (by simp) rfl
  -- the record's tail and the result slot
  by_cases hb : ¬ ((nm + 9).toNat < (m3.arr64 IW).size ∧ (nm + 10).toNat < (m3.arr64 IW).size ∧
      (nm + 11).toNat < (m3.arr64 IW).size ∧ (nm + 12).toNat < (m3.arr64 IW).size ∧
      (qr + j).toNat < (m3.arr64 IW).size)
  · rw [cnsK3_bad (h := hb)] at h; cases h
  simp only [Decidable.not_not] at hb
  rw [cnsK3_ok (h := hb)] at h
  obtain ⟨b9, b10, b11, b12, bq⟩ := hb
  simp only [wrTail] at h
  generalize hA : m3.set64 IW (nm + 9) (r1.headD 0) = mA at h
  generalize hB : mA.set64 IW (nm + 10) (r1.tail.headD 0) = mB at h
  generalize hC : mB.set64 IW (nm + 11) (rdW (mB.arr64 IW) (UInt64.ofNat p0 + 11)) = mC at h
  generalize hD : mC.set64 IW (nm + 12) (rdW (mC.arr64 IW) (UInt64.ofNat p0 + 12)) = mD at h
  generalize hE : mD.set64 IW (qr + j) nm = m4 at h
  have hqb := hS.lt64 htop
  have hqj : (qr + j).toNat = qr.toNat + j.toNat := by rw [UInt64.toNat_add]; simp; omega
  have hn9 : (nm + 9).toNat = nm.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have hn10 : (nm + 10).toNat = nm.toNat + 10 := by rw [UInt64.toNat_add]; simp; omega
  have hn11 : (nm + 11).toNat = nm.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
  have hn12 : (nm + 12).toNat = nm.toNat + 12 := by rw [UInt64.toNat_add]; simp; omega
  have hmt : ∀ t, t < 13 → (UInt64.ofNat p0 + UInt64.ofNat t : Word).toNat = p0 + t := fun t ht => by
    rw [UInt64.toNat_add, hp0T]; simp; omega
  have hgm1 : iwTop m ≤ iwTop s1.mem := hg1.1
  have hqnm : qr.toNat + ml.toNat ≤ nm.toNat := by omega
  -- sizes
  have szA : (mA.arr64 IW).size = (m3.arr64 IW).size := by rw [← hA, size_set64]
  have szB : (mB.arr64 IW).size = (m3.arr64 IW).size := by rw [← hB, size_set64, szA]
  have szC : (mC.arr64 IW).size = (m3.arr64 IW).size := by rw [← hC, size_set64, szB]
  have szD : (mD.arr64 IW).size = (m3.arr64 IW).size := by rw [← hD, size_set64, szC]
  -- the stage relation, growth, tops, memos
  have hS4 : StageR dn vis fe m4 a1 := by
    rw [← hE, ← hD, ← hC, ← hB, ← hA]
    exact ((((hS3.set_iw _ _).set_iw _ _).set_iw _ _).set_iw _ _).set_iw _ _
  have hgD : IWGrow s1.mem mD := by
    rw [← hD, ← hC, ← hB, ← hA]
    exact (((hg3.set_iw _ _ (by omega)).set_iw _ _ (by omega)).set_iw _ _ (by omega)).set_iw _ _ (by omega)
  have hg4 : IWGrow mb m4 := by
    rw [← hE]; exact ((hg.trans hg1).trans hgD).set_iw _ _ (by omega)
  have hFr : FrX (qr.toNat + j.toNat) m m4 := by
    rw [← hE]; exact (FrX.trans_grow (FrX.of_grow hg1) hgD).set _ _ hqj
  have ht4 : iwTop m4 = iwTop s2.mem := by
    rw [← hE, ← hD, ← hC, ← hB, ← hA]; simp only [cnsTop_set]; exact ht3
  have hP4 : RcMR m4 := by
    rw [← hE, ← hD, ← hC, ← hB, ← hA]
    exact hP2.fr (hP3.trans ((((MFr.set_iw _ _ _).trans (MFr.set_iw _ _ _)).trans (MFr.set_iw _ _ _)).trans
      ((MFr.set_iw _ _ _).trans (MFr.set_iw _ _ _))))
  -- the record's words
  have hsrcw : ∀ t, t < 13 → ∀ v, (iwA (truncM mb))[p0 + t]? = some v →
      rdW (s2.mem.arr64 IW) (UInt64.ofNat p0 + UInt64.ofNat t) = v := by
    intro t ht v hv
    obtain ⟨hlt, hv'⟩ := truncM_iw_get hv
    have e : (s2.mem.arr64 IW)[p0 + t]? = (mb.arr64 IW)[p0 + t]? := ((hg.trans hg1).trans hg2).2.2.1 _ hlt
    simp only [rdW, hmt t ht, e]; simp only [iwA] at hv'; rw [hv']; rfl
  have hlow : ∀ i, i < nm.toNat → (mC.arr64 IW)[i]? = (s2.mem.arr64 IW)[i]? := by
    intro i hi
    rw [← hC, set64IW_get, if_neg (by omega), ← hB, set64IW_get, if_neg (by omega), ← hA, set64IW_get,
      if_neg (by omega)]
    exact g1 i (by omega)
  have hrdC : ∀ t, t < 13 → rdW (mC.arr64 IW) (UInt64.ofNat p0 + UInt64.ofNat t) =
      rdW (s2.mem.arr64 IW) (UInt64.ofNat p0 + UInt64.ofNat t) := by
    intro t ht; simp only [rdW, hmt t ht]; rw [hlow (p0 + t) (by omega)]
  have hrdB : ∀ t, t < 13 → rdW (mB.arr64 IW) (UInt64.ofNat p0 + UInt64.ofNat t) =
      rdW (s2.mem.arr64 IW) (UInt64.ofNat p0 + UInt64.ofNat t) := by
    intro t ht
    rw [← hrdC t ht, ← hC, rdW_set_ne (by rw [hmt t ht, hn11]; omega)]
  have hwords : ∀ k, k < 13 → k ≠ 9 → k ≠ 10 →
      (m4.arr64 IW)[nm.toNat + k]? = (iwA (truncM mb))[p0 + k]? := by
    intro k hk h9 h10
    obtain ⟨v, hv⟩ := decTM_get hsrc k hk
    rw [hv, ← hE, set64IW_get, if_neg (by omega)]
    by_cases k12 : k = 12
    · subst k12
      rw [← hD, set64IW_get, if_pos ⟨by omega, by rw [szC]; omega⟩]
      rw [show (12 : Word) = UInt64.ofNat 12 from rfl, hrdC 12 (by omega), hsrcw 12 (by omega) v hv]
    rw [← hD, set64IW_get, if_neg (by omega)]
    by_cases k11 : k = 11
    · subst k11
      rw [← hC, set64IW_get, if_pos ⟨by omega, by rw [szB]; omega⟩]
      rw [show (11 : Word) = UInt64.ofNat 11 from rfl, hrdB 11 (by omega), hsrcw 11 (by omega) v hv]
    rw [← hC, set64IW_get, if_neg (by omega), ← hB, set64IW_get, if_neg (by omega), ← hA, set64IW_get,
      if_neg (by omega), g2 k (by simp) (by omega), hsrcw k hk v hv]
  have hw9 : iwN m4 (nm.toNat + 9) = some (r1.headD 0).toNat := by
    simp only [iwN, nat?, iwA]
    rw [← hE, set64IW_get, if_neg (by omega), ← hD, set64IW_get, if_neg (by omega), ← hC, set64IW_get,
      if_neg (by omega), ← hB, set64IW_get, if_neg (by omega), ← hA, set64IW_get, if_pos ⟨by omega, by rw [hn9] at b9; exact b9⟩]
    rfl
  have hw10 : iwN m4 (nm.toNat + 10) = some (r1.tail.headD 0).toNat := by
    simp only [iwN, nat?, iwA]
    rw [← hE, set64IW_get, if_neg (by omega), ← hD, set64IW_get, if_neg (by omega), ← hC, set64IW_get,
      if_neg (by omega), ← hB, set64IW_get, if_pos ⟨by omega, by rw [szA]; rw [hn10] at b10; exact b10⟩]
    rfl
  have hFr1 : FrX (qr.toNat + j.toNat) s1.mem m4 := by
    rw [← hE]; exact (FrX.trans_grow (FrX.of_grow (IWGrow.refl _)) hgD).set _ _ hqj
  have hfr' : (r1.tail.headD 0).toNat = 0 ∨ qr.toNat + ml.toNat ≤ (r1.headD 0).toNat := by
    rcases hfr with h0 | h0
    · left; rw [h0]; rfl
    · right; omega
  have hes4 : decNL m4 (r1.headD 0).toNat (r1.tail.headD 0).toNat = some pse := by
    rw [decNL_frX hFr1 hes.2 (by omega)]
    exact hpse
  have hnew : CnsRec mb (CnsSrc mb mo ml) (qr.toNat + ml.toNat) m4 nm.toNat { ms[j.toNat]'(by omega) with nfs := es } :=
    ⟨p0, _, _, _, pse, hsrcmb, ⟨j.toNat, hjl, hp0m⟩, hqnm, by rw [ht4]; omega, hwords, hw9, hw10, hes4,
      by have := hes.2; rw [ht4]; omega, hfr', hpseb, rfl⟩
  -- the result slot
  have hws4 : decNL m4 qr.toNat (j + 1).toNat = some (ws ++ [nm.toNat]) := by
    rw [hj1, decNL_snoc, decNL_frX hFr (by omega) (by right; right; omega), hws]
    have : iwN m4 (qr.toNat + j.toNat) = some nm.toNat := by
      simp only [iwN, nat?, iwA]
      rw [← hE, set64IW_get, if_pos ⟨hqj.symm, by rw [szD]; rw [hqj] at bq; exact bq⟩]
      rfl
    simp [this]
  have hacc4 : FA2 (CnsRec mb (CnsSrc mb mo ml) (qr.toNat + ml.toNat) m4) (ws ++ [nm.toNat])
      (acc ++ [{ ms[j.toNat]'(by omega) with nfs := es }]) :=
    FA2.snoc (FA2.imp (fun _ _ hr => CnsRec.frame hr hFr (by omega)) hacc) hnew
  have hje1 : j + 1 ≤ ml := UInt64.le_iff_toNat_le.mpr (by omega)
  obtain ⟨rest, a', run', hS', hg', ht', hP', ws', hws', hacc'⟩ := ih m4 m' a1 (j + 1) _ _ h hS4 hg4
    (by rw [ht4]; omega) hP4 hje1 hws4 hacc4
  refine ⟨{ ms[j.toNat]'(by omega) with nfs := es } :: rest, a', ?_, hS', hg', ht', hP', ws', hws', by simpa using hacc'⟩
  rw [List.drop_eq_getElem_cons (by omega), ConRon.Arena.classesNfs]
  rw [hj1] at run'
  simp only [StateT.run_bind, run1, except_ok_bind, run']
  rfl

end loop

theorem cnsRec_mapM {mb mF : Mem} {S : Nat → Prop} {hi : Nat} (hg : IWGrow mb mF) :
    ∀ {ws : List Nat} {xs : List TargetMajor}, FA2 (CnsRec mb S hi mF) ws xs → ws.mapM (decTM (truncM mF)) = some xs
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h1 h2 => by
    simp only [List.mapM_cons, show decTM (truncM mF) _ = some _ from h1.decB hg, cnsRec_mapM hg h2]; rfl

/-- **`classes_nfs` refines `classesNfs`** (through `target_major_nfs`' contracts and stubs): the
block's shape (`BSOK`), former types, the walk's table and the classes decoded below the tops, the
walk memos well formed; the classes with their entries a pointer slice decoded below the tops.
Under `StageR`; the census link is `classesNfs_refinesC` (`IndT/RecGen28`). -/
theorem classesNfs_refines {p : Prog} (P : CnsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl tblo tbll mo ml : Word)
    (bs : BlockShape) (formerTys : List EIdx) (tbl : List NestCtorNf) (ms : List TargetMajor)
    (hS : StageR dn vis fe s₀.mem a₀) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (htbl : PSlR decNCN tbl tblo tbll s₀.mem) (hms : PSlR decTM ms mo ml s₀.mem) (hP : RcMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "classes_nfs" [vis, q, fto, ftl, tblo, tbll, mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀ ∧
      PSlR decTM (AM.res (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀) (r.headD 0) (r.tail.headD 0) s'.mem ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem; ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
  refine triple_post (cnfs_spec p P.cns n s₀ vis q fto ftl tblo tbll mo ml) ?_
  rintro r s' ⟨hl, hm⟩
  rw [cnfsW_eq] at hm
  cases c0 : callW p n "iw_alloc" [ml] s₀.mem with
  | none => rw [c0] at hm; cases hm
  | some x0 =>
  obtain ⟨r0, m0⟩ := x0
  rw [c0, cnfsK1_some] at hm
  cases c1 : cnsW p (n + 1) m0 vis q fto ftl tblo tbll mo ml (r0.headD 0) 0 with
  | none => rw [c1] at hm; cases hm
  | some mF =>
  rw [c1, cnfsK2_some] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm; obtain ⟨rfl, hmF⟩ := hm
  obtain ⟨s0, hs0, -, hw0⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩) (iwAlloc_specW p P.ha n _ ml) c0
  simp only at hs0 hw0; subst hs0
  obtain ⟨hS0, hg0, hq0, ht0⟩ := allocW_stage hw0 hS
  obtain ⟨rest, a', run, hSF, hgF, htF, hPF, ws', hws', hacc'⟩ := cnsW_ok P dn fe vis q fto ftl tblo tbll mo ml
    (r0.headD 0) bs formerTys tbl ms s₀.mem hq0 hms htbl hbs hft hftb (n + 1) s0.mem mF a₀ 0 [] [] c1 hS0 hg0
    (by omega) (hP.fr (allocW_mfr hw0)) UInt64.zero_le (by simp [decNL]) FA2.nil
  simp only [UInt64.toNat_zero, List.drop_zero, List.nil_append] at run hacc'
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  rw [← hmF]
  refine ⟨hl, hok, ?_, by rw [hst]; exact hSF, hgF, hPF⟩
  rw [hres]
  refine ⟨?_, by simpa using htF⟩
  show decPL (truncM mF) (decTM (truncM mF)) _ _ = some rest
  simp only [List.headD_cons, List.tail_cons]
  rw [decPL_eq_bind, show decNL (truncM mF) (r0.headD 0).toNat ml.toNat = some ws' from decNL_decB hws' htF]
  exact cnsRec_mapM hgF hacc'

end L.Ind
