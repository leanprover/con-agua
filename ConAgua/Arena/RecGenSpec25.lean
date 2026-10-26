import ConAgua.Arena.RecGenSpec24
import ConAgua.Arena.RecGenSpec22
import ConAgua.Front.Preserve

/-!
# `classCtorOf`'s entries: `class_ctor_of_nfs` (lane `indproofs4`, helper `cls`)

`class_ctor_of_nfs(nfs.off, nfs.len, name)`: the twin's `m.nfs.filter (·.ctor == name)`, the kept
entries' pointers written into a fresh slice of `nfs.len` words by a `while` loop (named block
`cnfLoop`, model `cnfW`). Its relational lemma (`cnfW_ok`, by induction on the loop fuel) carries
the written prefix of the result, decoded by the entries' decoder in the memory before the
allocation; the entries lie below that memory's top, the writes above it.

Also: every L run keeps the word arrays' sizes (`callW_keepW`; as `Front/Preserve.lean`'s `Keep`,
without the byte arrays, so with no program hypothesis).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Every L run keeps the word arrays' sizes -/

/-- Every word array has the same size. -/
def KeepW (m m' : Mem) : Prop := ∀ a, (m'.arr64 a).size = (m.arr64 a).size

theorem KeepW.refl (m : Mem) : KeepW m m := fun _ => rfl

theorem KeepW.trans {m₁ m₂ m₃ : Mem} (h₁ : KeepW m₁ m₂) (h₂ : KeepW m₂ m₃) : KeepW m₁ m₃ :=
  fun a => (h₂ a).trans (h₁ a)

theorem KeepW.set64 {m m' : Mem} (h : KeepW m m') (a : ArrId) (i v : Word) : KeepW m (m'.set64 a i v) := by
  intro b
  rw [← h b]
  simp only [Mem.set64, Mem.arr64]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases hb : a = b
  · subst hb
    by_cases ha : a < m'.words.size <;> simp [ha]
  · simp [hb]

theorem KeepW.set8 {m m' : Mem} (h : KeepW m m') (a : ArrId) (i v : Word) : KeepW m (m'.set8 a i v) := h

theorem KeepW.setG {m m' : Mem} (h : KeepW m m') (g : GVar) (v : Word) : KeepW m (m'.setG g v) := h

/-- A continuation that keeps `KeepW`. -/
theorem KeepW.copy64 {m m' : Mem} (h : KeepW m m') (d : ArrId) (di : Word) (s : ArrId) (si : Word)
    (n : Nat) : KeepW m (m'.copy64 d di s si n) := by
  induction n generalizing m' di si with
  | zero => exact h
  | succ n ih => exact ih (h.set64 _ _ _) _ _

theorem KeepW.copy8w {m m' : Mem} (h : KeepW m m') (d : ArrId) (di : Word) (b : Array UInt8) (si : Word)
    (n : Nat) : KeepW m (m'.copy8w d di b si n) := by
  induction n generalizing m' di si with
  | zero => exact h
  | succ n ih => exact ih (h.set64 _ _ _) _ _

def KeepWK (k : Stmt → M Sig) : Prop :=
  ∀ st m₀, ⦃fun s => KeepW m₀ s.mem⦄ k st ⦃fun _ s => KeepW m₀ s.mem; ⊤⦄

theorem invoke_keepW (p : Prog) (k : Stmt → M Sig) (hk : KeepWK k) (f : FnName) (m₀ : Mem)
    (vs : List Word) :
    ⦃fun s => KeepW m₀ s.mem⦄ invoke p k f vs ⦃fun _ s => KeepW m₀ s.mem; ⊤⦄ := by
  rcases h : p.lookup f with _ | fd
  · simp only [invoke, lookupFn, h]; vcgen <;> grind
  rw [invoke_eq _ h]
  simp only [callFn]
  vcgen [hk fd.body m₀] <;> grind

theorem step_keepW (p : Prog) (k : Stmt → M Sig) (hk : KeepWK k) : KeepWK (step p k) := by
  intro st m₀
  induction st with
  | «skip» => vcgen [step] <;> grind
  | «set» x e => vcgen [step, setLoc, evalE_same e] <;> grind [St.setLoc_mem]
  | «st8» a i e => vcgen [step, st8, evalE_same i, evalE_same e] <;> grind [KeepW.set8]
  | «st64» a i e => vcgen [step, st64, evalE_same i, evalE_same e] <;> grind [KeepW.set64]
  | «seq» s t ihs iht => vcgen [step, ihs, iht] <;> grind
  | «ite» c s t ihs iht => vcgen [step, evalC_same c, ihs, iht] <;> grind
  | «while» c s ih => vcgen [step, evalC_same c, ih, hk (.while c s) m₀] <;> grind
  | «brk» => vcgen [step] <;> grind
  | «ret» es => vcgen [step, evalArgs_same es] <;> grind
  | «call» xs f args =>
    vcgen [step, setLocs, evalArgs_same args, invoke_keepW p k hk f m₀] <;> grind [St.setLocs_mem']
  | «abort» e => vcgen [step, evalE_same e] <;> grind
  | «gset» g e => vcgen [step, setG, evalE_same e] <;> grind [KeepW.setG, St.setG_mem]
  | st64t a t i e =>
    vcgen [step, st64, evalE_same t, evalE_same i, evalE_same e] <;> grind [KeepW.set64]
  | copy64 d di s si n =>
    vcgen [step, warr_same d, warr_same s, evalE_same di, evalE_same si, evalE_same n] <;>
      grind [KeepW.copy64]
  | copy8w d di s si n =>
    vcgen [step, warr_same d, evalE_same di, evalE_same si, evalE_same n] <;> grind [KeepW.copy8w]
  | scan8 x s i e c => vcgen [step, setLoc, evalE_same i, evalE_same e] <;> grind [St.setLoc_mem]

theorem exec_keepW (p : Prog) (n : Nat) : KeepWK (exec p n) := by
  induction n with
  | zero => intro st m₀; vcgen [exec] <;> grind
  | succ n ih => exact step_keepW p (exec p n) ih

/-- **A returning call keeps the word arrays' sizes.** -/
theorem callW_keepW {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {m m' : Mem} {r : List Word}
    (h : callW p n f vs m = some (r, m')) : KeepW m m' := by
  simp only [callW] at h
  cases hr : (invoke p (exec p n) f vs).run ⟨m, Locals.init []⟩ with
  | error e => rw [hr] at h; cases h
  | ok q =>
    obtain ⟨r1, s1⟩ := q
    rw [hr] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact M.of_run (P := fun s => KeepW m s.mem) (Q := fun _ s => KeepW m s.mem) (KeepW.refl m) hr
      (invoke_keepW p (exec p n) (exec_keepW p n) f m vs)

/-! ## `class_ctor_of_nfs`: the loop as a named block -/

/-- The loop of `classCtorOfNfs` (RecGen.lean), named for its spec. -/
-- con-ron: none — `classCtorOfNfs`' own loop (`rfl`), a named block for the proof
def cnfLoop : Stmt := lblk (nfsOff, nfsLen, name, q, j, nf, rp) {
  while j < nfsLen {
    nf := IW.u64[nfsOff + j];
    if IW.u64[nf] == name { IW.u64[q + rp] := nf; rp += 1 };
    j += 1
  }
}

/-- `classCtorOfNfs`, with its loop spliced from `cnfLoop`. -/
-- con-ron: none — `classCtorOfNfs` itself (`rfl`), its loop a named block for the proof
def classCtorOfNfs' : FunDecl := lfn (nfsOff, nfsLen, name) locals (q, j, nf, rp) {
  q := call iw_alloc(nfsLen);
  j := 0;
  rp := 0;
  ⟪cnfLoop⟫;
  return (q, rp)
}

theorem classCtorOfNfs_eq : classCtorOfNfs = classCtorOfNfs' := rfl

/-- **The model of `class_ctor_of_nfs`' loop** at L fuel `k`: the kept count and the memory. -/
def cnfW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, nfo, nfl, nm, q, j, rp =>
    if j < nfl then
      if rdW (m.arr64 IW) (rdW (m.arr64 IW) (nfo + j)) = nm then
        if (q + rp).toNat < (m.arr64 IW).size then
          cnfW k (m.set64 IW (q + rp) (rdW (m.arr64 IW) (nfo + j))) nfo nfl nm q (j + 1) (rp + 1)
        else none
      else cnfW k m nfo nfl nm q (j + 1) rp
    else some (rp, m)

section arms
variable (k : Nat) (m : Mem) (nfo nfl nm q j rp : Word)
theorem cnfW_exit (h : ¬ j < nfl) : cnfW (k + 1) m nfo nfl nm q j rp = some (rp, m) := by
  simp only [cnfW]; rw [ite_eq_right h]
theorem cnfW_hit (h : j < nfl) (h1 : rdW (m.arr64 IW) (rdW (m.arr64 IW) (nfo + j)) = nm)
    (h2 : (q + rp).toNat < (m.arr64 IW).size) : cnfW (k + 1) m nfo nfl nm q j rp =
      cnfW k (m.set64 IW (q + rp) (rdW (m.arr64 IW) (nfo + j))) nfo nfl nm q (j + 1) (rp + 1) := by
  simp only [cnfW]; rw [ite_eq_left h, ite_eq_left h1, ite_eq_left h2]
theorem cnfW_oob (h : j < nfl) (h1 : rdW (m.arr64 IW) (rdW (m.arr64 IW) (nfo + j)) = nm)
    (h2 : ¬ (q + rp).toNat < (m.arr64 IW).size) : cnfW (k + 1) m nfo nfl nm q j rp = none := by
  simp only [cnfW]; rw [ite_eq_left h, ite_eq_left h1, ite_eq_right h2]
theorem cnfW_miss (h : j < nfl) (h1 : ¬ rdW (m.arr64 IW) (rdW (m.arr64 IW) (nfo + j)) = nm) :
    cnfW (k + 1) m nfo nfl nm q j rp = cnfW k m nfo nfl nm q (j + 1) rp := by
  simp only [cnfW]; rw [ite_eq_left h, ite_eq_right h1]
end arms

/-- After the loop. -/
def cnfK2 (q : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rp, m) => some ([q, rp], m)

/-- After the allocation: the loop. -/
def cnfK1 (n : Nat) (nfo nfl nm : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m) => cnfK2 q (cnfW (n + 1) m nfo nfl nm q 0 0)

/-- **The model of `class_ctor_of_nfs(nfs.off, nfs.len, name)`** (exec fuel `n + 1`). -/
def cnfF (n : Nat) (m : Mem) (nfo nfl nm : Word) : Option (List Word × Mem) :=
  cnfK1 n nfo nfl nm (allocW m nfl)

theorem cnfK2_some (q rp : Word) (m : Mem) : cnfK2 q (some (rp, m)) = some ([q, rp], m) := rfl
theorem cnfK1_some (n : Nat) (nfo nfl nm q : Word) (m : Mem) :
    cnfK1 n nfo nfl nm (some (q, m)) = cnfK2 q (cnfW (n + 1) m nfo nfl nm q 0 0) := rfl

attribute [ind_grind] cnfW_exit cnfW_hit cnfW_oob cnfW_miss cnfK2_some cnfK1_some

theorem cnfLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p k cnfLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 3 = s₀.loc 3 ∧
      cnfW k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 6) =
        some (s'.loc 6, s'.mem); ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := cnfLoop) rfl]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

theorem cnf_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "class_ctor_of_nfs" = some classCtorOfNfs) (n : Nat) (s₀ : St) (nfo nfl nm : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_ctor_of_nfs" [nfo, nfl, nm]
    ⦃fun r s' => LocEq s' s₀ ∧ cnfF n s₀.mem nfo nfl nm = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp, classCtorOfNfs_eq]
  simp only [callFn, classCtorOfNfs']
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, iwAlloc_specW p ha n,
      fun s => Triple.step_exec (cnfLoop_spec p (n + 1) s)] <;>
    finish (gen := 40) (instances := 20000) [cnfF]

/-! ## `class_ctor_of_nfs`: the relational side -/

theorem iwTop_set_iw (m : Mem) (k v : Word) : iwTop (m.set64 IW k v) = iwTop m := by
  simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]

/-- The entries' filter, one more entry. -/
theorem filter_take_succ {α : Type} (P : α → Bool) (xs : List α) (j : Nat) (hj : j < xs.length) :
    (xs.take (j + 1)).filter P = (xs.take j).filter P ++ (if P xs[j] then [xs[j]] else []) := by
  rw [List.take_add_one, List.filter_append, List.getElem?_eq_getElem hj]
  by_cases h : P xs[j] <;> simp [h]

section cnf
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} (m0 : Mem)
  (nfo nfl nm q : Word) (nfs : List NestCtorNf)

/-- **`class_ctor_of_nfs`' loop**: the kept entries written after the prefix `acc`. -/
theorem cnfW_ok (hnfs : DecB (fun m => decPL m (decNCN m) nfo.toNat nfl.toNat) m0 nfs) (hnm : H nm)
    (hq : q.toNat = iwTop m0) (k : Nat) :
    ∀ (m m' : Mem) (j rp rp' : Word),
    cnfW k m nfo nfl nm q j rp = some (rp', m') → StageR dn vis fe m a → IWGrow m0 m →
    iwTop m = q.toNat + nfl.toNat → j ≤ nfl → rp ≤ j →
    decPL m (decNCN (truncM m0)) q.toNat rp.toNat =
      some ((nfs.take j.toNat).filter (fun e => e.ctor == decI nm)) →
    StageR dn vis fe m' a ∧ IWGrow m0 m' ∧ iwTop m' = iwTop m ∧ MFr [] [] m m' ∧ rp' ≤ nfl ∧
      decPL m' (decNCN (truncM m0)) q.toNat rp'.toNat = some (nfs.filter (fun e => e.ctor == decI nm)) := by
  have hnfs0 : decPL (truncM m0) (decNCN (truncM m0)) nfo.toNat nfl.toNat = some nfs := hnfs
  have hlen := decPL_length _ hnfs0
  induction k with
  | zero => intro m m' j rp rp' h; simp [cnfW] at h
  | succ k ih =>
  intro m m' j rp rp' h hS hg htop hjn hrj hacc
  have hsz := hS.2.2.2.1
  have hjn' : j.toNat ≤ nfl.toNat := UInt64.le_iff_toNat_le.mp hjn
  have hrj' : rp.toNat ≤ j.toNat := UInt64.le_iff_toNat_le.mp hrj
  by_cases hj : j < nfl
  rotate_left
  · rw [cnfW_exit (h := hj)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have h1 : nfl.toNat ≤ j.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hj
    refine ⟨hS, hg, rfl, MFr.refl _ _ _, UInt64.le_trans hrj hjn, ?_⟩
    rw [hacc, List.take_of_length_le (by omega)]
  have hjl : j.toNat < nfl.toNat := UInt64.lt_iff_toNat_lt.mp hj
  have := nfl.toNat_lt
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  have hje1 : j + 1 ≤ nfl := UInt64.le_iff_toNat_le.mpr (by omega)
  -- the entry
  obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m0) hnfs0 j.toNat hjl
  obtain ⟨hvt, hv0⟩ := rec2IwN_trunc hv
  have hvm : iwN m (nfo.toNat + j.toNat) = some v := by
    simp only [iwN, nat?, iwA] at hv0 ⊢; rw [hg.2.2.1 _ hvt]; exact hv0
  have hrd := iwN_rdW_at (w := nfo) (k := j.toNat) hvm hsz
  have hnj : nfo + UInt64.ofNat j.toNat = nfo + j := by simp
  rw [hnj] at hrd
  have hkf : rdW (m.arr64 IW) (nfo + j) = UInt64.ofNat v := hrd.1
  have hvT : (UInt64.ofNat v : Word).toNat = v := UInt64.toNat_ofNat_of_lt' hrd.2
  have hdvB : DecB (fun m => decNCN m (UInt64.ofNat v : Word).toNat) m nfs[j.toNat] := by
    have : DecB (fun m => decNCN m v) m0 nfs[j.toNat] := by rw [← hlen] at hjl; exact hdv
    rw [hvT]; exact this.grow (decNCN_mono _) hg
  obtain ⟨hcH, hcD, -⟩ := decNCN_fields hdvB hsz
  have hiff : (rdW (m.arr64 IW) (UInt64.ofNat v) = nm) ↔ (nfs[j.toNat].ctor == decI nm) = true := by
    rw [← hcD, beq_iff_eq]
    exact ⟨fun e => by rw [e], fun e => decI_inj hcH hnm e⟩
  have hfil := filter_take_succ (fun e : NestCtorNf => e.ctor == decI nm) nfs j.toNat (by omega)
  by_cases hhit : rdW (m.arr64 IW) (UInt64.ofNat v) = nm
  · have hqr : (q + rp).toNat = q.toNat + rp.toNat := by
      rw [UInt64.toNat_add]; have := hS.2.1; simp <;> omega
    have hqb : (q + rp).toNat < (m.arr64 IW).size := by have := hS.2.1; omega
    rw [cnfW_hit (h := hj) (h1 := by rw [hkf]; exact hhit) (h2 := hqb), hkf] at h
    have hr1 : (rp + 1).toNat = rp.toNat + 1 := by rw [UInt64.toNat_add]; simp <;> omega
    have hS1 := hS.set_iw (q + rp) (UInt64.ofNat v)
    have hg1 : IWGrow m0 (m.set64 IW (q + rp) (UInt64.ofNat v)) := hg.set_iw _ _ (by omega)
    have hacc1 : decPL (m.set64 IW (q + rp) (UInt64.ofNat v)) (decNCN (truncM m0)) q.toNat (rp + 1).toNat =
        some ((nfs.take (j + 1).toNat).filter (fun e => e.ctor == decI nm)) := by
      rw [hr1, hj1, hfil, ite_eq_left (hiff.mp hhit)]
      exact sumDecPL_write m _ q.toNat rp.toNat (q + rp) (UInt64.ofNat v) _ _ hqr (by omega) hacc
        (by rw [hvT]; rw [← hlen] at hjl; exact hdv)
    obtain ⟨hS', hg', ht', hf', hr', hd'⟩ := ih _ m' (j + 1) (rp + 1) rp' h hS1 hg1
      (by rw [iwTop_set_iw]; exact htop) hje1 (UInt64.le_iff_toNat_le.mpr (by omega)) hacc1
    exact ⟨hS', hg', by rw [ht', iwTop_set_iw], (MFr.set_iw _ _ _).trans hf', hr', hd'⟩
  · rw [cnfW_miss (h := hj) (h1 := by rw [hkf]; exact hhit)] at h
    have hacc1 : decPL m (decNCN (truncM m0)) q.toNat rp.toNat =
        some ((nfs.take (j + 1).toNat).filter (fun e => e.ctor == decI nm)) := by
      rw [hj1, hfil, ite_eq_right (fun e => hhit (hiff.mpr e)), List.append_nil]; exact hacc
    exact ih m m' (j + 1) rp rp' h hS hg htop hje1 (UInt64.le_iff_toNat_le.mpr (by omega)) hacc1

/-- A pointer slice decoded with the decoder of an earlier memory is decoded below the tops. -/
theorem pslr_of_decPL {m0 m : Mem} (hg : IWGrow m0 m) {o l : Word} {xs : List NestCtorNf}
    (hb : o.toNat + l.toNat ≤ iwTop m) (h : decPL m (decNCN (truncM m0)) o.toNat l.toNat = some xs) :
    PSlR decNCN xs o l m := by
  refine ⟨?_, hb⟩
  show decPL (truncM m) (decNCN (truncM m)) o.toNat l.toNat = some xs
  rw [decPL_truncM_of (f := decNCN (truncM m0)) (fun j hj => by omega) ?_]
  · exact h
  intro j hj v hv
  obtain ⟨v', hv', hx⟩ := decPL_getH m h j hj
  rw [hv] at hv'; cases hv'
  rw [hx]
  exact (show DecB (fun m => decNCN m v) m0 _ from hx).grow (decNCN_mono _) hg

/-- **`class_ctor_of_nfs` refines the filter**: the entries of `nfs` (decoded below the tops) whose
constructor is `nm`, a pointer slice decoded below the tops. -/
theorem cnfF_ok (n : Nat) {m m' : Mem} {r : List Word} (h : cnfF n m nfo nfl nm = some (r, m'))
    (hS : StageR dn vis fe m a) (hnfs : DecB (fun m => decPL m (decNCN m) nfo.toNat nfl.toNat) m nfs)
    (hnm : H nm) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ MFr [] [] m m' ∧
      PSlR decNCN (nfs.filter (fun e => e.ctor == decI nm)) (r.headD 0) (r.tail.headD 0) m' := by
  simp only [cnfF] at h
  obtain ⟨⟨q, m1⟩, hal, h⟩ := of_K h rfl
  rw [cnfK1_some] at h
  obtain ⟨⟨rp, m2⟩, hl, h⟩ := of_K h rfl
  rw [cnfK2_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hS1, hg1, hq, ht1⟩ := allocW_stage hal hS
  obtain ⟨hS2, hg2, ht2, hf2, hr2, hd2⟩ := cnfW_ok m nfo nfl nm q nfs hnfs hnm hq (n + 1) m1 m2 0 0 rp hl hS1
    hg1 (by omega) UInt64.zero_le (UInt64.le_refl _) (by simp [decPL])
  have hr2' : rp.toNat ≤ nfl.toNat := UInt64.le_iff_toNat_le.mp hr2
  refine ⟨hS2, hg2, (allocW_mfr hal).trans hf2, ?_⟩
  simp only [List.headD_cons, List.tail_cons]
  exact pslr_of_decPL hg2 (by omega) hd2

end cnf

end L.Ind
