import ConAgua.Arena.IndInstallSpec22

/-!
# Refinements of `IndInstall`, part 23 (lane `indproofs2`, helper `install`): `checkBlockCtors`,
the relation
-/

noncomputable section


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A member's fields' sorts: a pointer to `[off, len]` of `[off, len]` level-handle slices. -/
def decISS (m : Mem) (q : Nat) : Option (List (List LIdx)) := decAt m (fun o l => decPL m (decIS m) o l) q

theorem decISS_mono (q : Nat) : OMono (fun m => decISS m q) :=
  OMono.decAt (fun o l => OMono.decPL decIS_mono o l) q

/-- A `bool?` word of a record decoded below the tops, read at its word address. -/
theorem installIwB {m : Mem} {w : Word} {k : Nat} {b : Bool} (h : iwB (truncM m) (w.toNat + k) = some b)
    (hsz : (m.arr64 IW).size < 2 ^ 64) : (rdW (m.arr64 IW) (w + UInt64.ofNat k) != 0) = b := by
  simp only [iwB, bool?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨hi, hx'⟩ := truncM_iw_get hx
  simp only [iwA] at hx'
  have hlt : w.toNat + k < (m.arr64 IW).size := (Array.getElem?_eq_some_iff.mp hx').1
  have hk : k < 2 ^ 64 := by omega
  have hwk : w.toNat + k < 2 ^ 64 := by omega
  have he : (w + UInt64.ofNat k).toNat = w.toNat + k := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hk]; exact Nat.mod_eq_of_lt hwk
  rw [rdW_of_get? he.symm hx']

/-! ## Member slices with their bound

A member's constructor slice `(o, l)` decoded below the tops says nothing about `o` when `l = 0`;
the positivity walk (`CssAt`) wants `o + l ≤ iwTop` for every member. `decPLB` carries the bound in
the decoding (below the tops the pool's size is its top), so it survives `sl_cons` and growth. -/

/-- A pointer slice whose end lies within the pool. -/
def decPLB {α : Type} (m : Mem) (f : Nat → Option α) (o l : Nat) : Option (List α) :=
  if o + l ≤ (iwA m).size then decPL m f o l else none

/-- A member's constructors with their slice's bound. -/
def decCNSB (m : Mem) (q : Nat) : Option (List (IConstantVal × Nat)) :=
  decAt m (fun o l => decPLB m (decCN m) o l) q

theorem iwA_size_mono {m m' : Mem} (he : PoolExt m m') : (iwA m).size ≤ (iwA m').size := by
  rcases Nat.eq_zero_or_pos (iwA m).size with h0 | h0
  · omega
  · have h1 : (iwA m)[(iwA m).size - 1]? = some ((iwA m)[(iwA m).size - 1]'(by omega)) :=
      Array.getElem?_eq_getElem _
    have := (Array.getElem?_eq_some_iff.mp (he.1 _ _ h1)).1
    omega

theorem decPLB_omono {α : Type} {f : Mem → Nat → Option α} (hf : ∀ q, OMono (fun m => f m q)) (o l : Nat) :
    OMono (fun m => decPLB m (f m) o l) := by
  refine ⟨fun m m' x he h => ?_⟩
  simp only [decPLB] at h ⊢
  split at h
  · rename_i hb
    rw [if_pos (Nat.le_trans hb (iwA_size_mono he))]
    exact (OMono.decPL hf o l).mono m m' x he h
  · cases h

theorem decCNSB_mono (q : Nat) : OMono (fun m => decCNSB m q) :=
  OMono.decAt (fun o l => decPLB_omono decCN_mono o l) q

/-- Below the tops, the pool's size is at most its top. -/
theorem iwA_truncM_size_le (m : Mem) : (iwA (truncM m)).size ≤ iwTop m := by
  apply Nat.le_of_not_lt
  intro h
  have := truncM_iw_get? m (iwTop m)
  rw [if_neg (Nat.lt_irrefl _)] at this
  rw [Array.getElem?_eq_getElem h] at this
  cases this

/-- … and at least every bound below the top, when the top lies within the pool. -/
theorem le_iwA_truncM_size {m : Mem} {k : Nat} (hk : k ≤ iwTop m) (hT : iwTop m ≤ (iwA m).size) :
    k ≤ (iwA (truncM m)).size := by
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · omega
  · have e := truncM_iw_get? m (k - 1)
    rw [if_pos (by omega), Array.getElem?_eq_getElem (show k - 1 < (iwA m).size by omega)] at e
    have := (Array.getElem?_eq_some_iff.mp e).1
    omega

/-- A `[off, len]` member record decoded with its bound: the bound. -/
theorem decCNSB_bound {m : Mem} {q : Nat} {cs : List (IConstantVal × Nat)}
    (h : DecB (fun m => decCNSB m q) m cs) :
    ∃ o l, iwN (truncM m) q = some o ∧ iwN (truncM m) (q + 1) = some l ∧ o + l ≤ iwTop m ∧
      decPL (truncM m) (decCN (truncM m)) o l = some cs := by
  have h' : decCNSB (truncM m) q = some cs := h
  simp only [decCNSB, decAt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h'
  obtain ⟨o, ho, l, hl, hd⟩ := h'
  simp only [decPLB] at hd
  split at hd
  · rename_i hb
    exact ⟨o, l, ho, hl, Nat.le_trans hb (iwA_truncM_size_le m), hd⟩
  · cases hd

/-- With the bound dropped. -/
theorem decCNSB_decCNS {m : Mem} {q : Nat} {cs : List (IConstantVal × Nat)}
    (h : DecB (fun m => decCNSB m q) m cs) : DecB (fun m => decCNS m q) m cs := by
  obtain ⟨o, l, ho, hl, -, hd⟩ := decCNSB_bound h
  show decAt (truncM m) _ q = some cs
  simp only [decAt, ho, hl, Option.bind_eq_bind, Option.bind_some]
  exact hd

/-- The lookups of `check_block_ctors`. -/
structure CtorsProg (p : Prog) : Prop extends CstProg p where
  rec2 : p.lookup "rec2" = some rec2
  erCopy : p.lookup "er_copy" = some erCopy
  erToIw : p.lookup "er_to_iw" = some erToIw
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  one : p.lookup "check_block_ctors_one" = some checkBlockCtorsOne
  go : p.lookup "check_block_ctors_go" = some checkBlockCtorsGo
  ctors : p.lookup "check_block_ctors" = some checkBlockCtors
  sum : SumProg p

/-- **A `rec2` header `[off, len]` of a slice decoded below the tops**, decoded below the tops. -/
theorem installRec2PSl {p : Prog} (hP : CtorsProg p) {n : Nat} {α : Type} {f : Mem → Nat → Option α}
    (hf : ∀ q, OMono (fun m => f m q)) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {a : AState} {m m' : Mem} {o l : Word} {r : List Word} {xs : List α}
    (h : callW p n "rec2" [o, l] m = some (r, m')) (hS : StageR dn vis fe m a) (hx : PSlR f xs o l m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      DecB (fun m => decAt m (fun o l => decPL m (f m) o l) (r.headD 0).toNat) m' xs := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (rec2_specW p hP.alloc n hP.rec2 _ _ _) h
  obtain ⟨hS', hg, hr, hget, htop⟩ := recW_stage hW hS rfl
  refine ⟨hS', hg, ?_⟩
  subst hr
  have hq0 : (rdW (m.arr64 CTL) 200).toNat < iwTop s'.mem := by rw [htop]; simp [iwTop]
  have hq1 : (rdW (m.arr64 CTL) 200).toNat + 1 < iwTop s'.mem := by rw [htop]; simp [iwTop]
  have w0 : iwN (truncM s'.mem) (rdW (m.arr64 CTL) 200).toNat = some o.toNat := by
    rw [iwN_truncM hq0]; have := hget 0 (by simp); simp only [Nat.add_zero] at this
    simp [iwN, nat?, iwA, this]
  have w1 : iwN (truncM s'.mem) ((rdW (m.arr64 CTL) 200).toNat + 1) = some l.toNat := by
    rw [iwN_truncM hq1]; have := hget 1 (by simp)
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
    simp [iwN, nat?, iwA, this]
  have hd := hx.1.grow (OMono.decPL hf _ _) hg
  show decAt (truncM s'.mem) _ _ = some xs
  simp only [decAt, List.headD_cons, w0, w1, Option.bind_eq_bind, Option.bind_some]
  exact hd

/-- **A `rec2` header `[off, len]` of a slice below the tops**, decoded with its bound. -/
theorem installRec2PSlB {p : Prog} (hP : CtorsProg p) {n : Nat} {α : Type} {f : Mem → Nat → Option α}
    (hf : ∀ q, OMono (fun m => f m q)) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {a : AState} {m m' : Mem} {o l : Word} {r : List Word} {xs : List α}
    (h : callW p n "rec2" [o, l] m = some (r, m')) (hS : StageR dn vis fe m a) (hx : PSlR f xs o l m) :
    DecB (fun m => decAt m (fun o l => decPLB m (f m) o l) (r.headD 0).toNat) m' xs := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (rec2_specW p hP.alloc n hP.rec2 _ _ _) h
  obtain ⟨hS', hg, hr, hget, htop⟩ := recW_stage hW hS rfl
  subst hr
  have hq0 : (rdW (m.arr64 CTL) 200).toNat < iwTop s'.mem := by rw [htop]; simp [iwTop]
  have hq1 : (rdW (m.arr64 CTL) 200).toNat + 1 < iwTop s'.mem := by rw [htop]; simp [iwTop]
  have w0 : iwN (truncM s'.mem) (rdW (m.arr64 CTL) 200).toNat = some o.toNat := by
    rw [iwN_truncM hq0]; have := hget 0 (by simp); simp only [Nat.add_zero] at this
    simp [iwN, nat?, iwA, this]
  have w1 : iwN (truncM s'.mem) ((rdW (m.arr64 CTL) 200).toNat + 1) = some l.toNat := by
    rw [iwN_truncM hq1]; have := hget 1 (by simp)
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
    simp [iwN, nat?, iwA, this]
  have hd := hx.1.grow (OMono.decPL hf _ _) hg
  show decAt (truncM s'.mem) _ _ = some xs
  simp only [decAt, List.headD_cons, w0, w1, Option.bind_eq_bind, Option.bind_some, decPLB]
  rw [if_pos (le_iwA_truncM_size (Nat.le_trans hx.2 hg.1) hS'.2.1)]
  exact hd

theorem lpsW_afr {n : Nat} {m m' : Mem} {q : Word} {r : List Word} (h : lpsW n m q = some (r, m')) :
    AFr m m' := by
  cases n with
  | zero => simp [lpsW] at h
  | succ n =>
    simp only [lpsW] at h
    afr_auto h [erToIwW_afr]

end L.Ind
