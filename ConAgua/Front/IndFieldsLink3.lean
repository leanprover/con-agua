import ConAgua.Front.IndFieldsLink2

/-!
# The fields pass of an `inductive` line, linked to con-leche: the block, and `ind_fields`

The block record (kind `4`, six words: the three lists' offsets and counts) and its loop, then
`indFields_link`.
-/

open L.Arena
open ConLeche.Frontend ConAgua.Scan ConAgua.Scan.RecordsLink
open ConAgua.Front.FieldsLink
open L.Front.Fields (rdNatN NONE rdLoopN listN itemsN)
open L.Front (lsCntN)
open L.Scan.Utf8 (byteW)
open L.Scan.Member (nextMemberN)
open L.Scan.Leaves (numEndN skipDigitsN keyEndN)


namespace L.Front.Ind

section blk
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

omit h64 hsize in
theorem runR_stab {α : Type} (Rec : Nat → α → Mem → Prop) (sz : Nat)
    (stab : ∀ t x m m' x0 x1, Rec t x m → 1 ≤ t → t + sz ≤ topN m IFR + 1 →
      IGrow m m' IFR x0 x1 → (t + sz ≤ x0 ∨ x1 ≤ t) → Rec t x m')
    (m m' : Mem) (x0 x1 : Nat) (hg : IGrow m m' IFR x0 x1) (o : Nat) (l : List α)
    (h : RunR Rec IFR sz m o l) (hd : x1 ≤ o) : RunR Rec IFR sz m' o l := by
  obtain ⟨r1, r2, r3⟩ := h
  have := hg.top IFR (.inl rfl)
  exact ⟨r1, by omega, fun j hj => stab _ _ m m' x0 x1 (r3 j hj) (by omega)
    (run_bound _ _ _ _ _ hj r2) hg (.inr (by omega))⟩

/-- A list of the block: its count, its offset past the block record, its records. -/
def LstR {α : Type} (Rec : Nat → α → Mem → Prop) (sz : Nat) (p : Word) (m : Mem) (off cnt : Word)
    (l : List α) : Prop :=
  cnt.toNat = l.length ∧ p.toNat + 6 ≤ off.toNat ∧ RunR Rec IFR sz m off.toNat l

omit h64 hsize in
theorem lstR_move {α : Type} (Rec : Nat → α → Mem → Prop) (sz : Nat)
    (stab : ∀ t x m m' x0 x1, Rec t x m → 1 ≤ t → t + sz ≤ topN m IFR + 1 →
      IGrow m m' IFR x0 x1 → (t + sz ≤ x0 ∨ x1 ≤ t) → Rec t x m')
    (p : Word) (m m' : Mem) (hg : IGrow m m' IFR p.toNat (p.toNat + 6)) (off cnt off' cnt' : Word)
    (ho : off' = off) (hc : cnt' = cnt) (l : List α) (h : LstR Rec sz p m off cnt l) :
    LstR Rec sz p m' off' cnt' l := by
  subst ho hc
  exact ⟨h.1, h.2.1, runR_stab Rec sz stab m m' _ _ hg _ l h.2.2 h.2.1⟩

/-- con-leche's block loop state. -/
structure BlkSt where
  ctors : List IndCtorRec
  recs : List IndRecRec
  types : List IndTypeRec

omit h64 hsize in
theorem tyStab : ∀ t x m m' x0 x1, TyF b m t x → 1 ≤ t → t + 11 ≤ topN m IFR + 1 →
    IGrow m m' IFR x0 x1 → (t + 11 ≤ x0 ∨ x1 ≤ t) → TyF b m' t x := tyF_stab b
omit h64 hsize in
theorem ctStab : ∀ t x m m' x0 x1, CtF b m t x → 1 ≤ t → t + 10 ≤ topN m IFR + 1 →
    IGrow m m' IFR x0 x1 → (t + 10 ≤ x0 ∨ x1 ≤ t) → CtF b m' t x := ctF_stab b
omit h64 hsize in
theorem recStab : ∀ t x m m' x0 x1, RecF b m t x → 1 ≤ t → t + 11 ≤ topN m IFR + 1 →
    IGrow m m' IFR x0 x1 → (t + 11 ≤ x0 ∨ x1 ≤ t) → RecF b m' t x := recF_stab b

/-- The block record read so far. -/
def BlkLR (m₁ : Mem) (p : Word) (seen : UInt32) (st : BlkSt) (m : Mem) : Prop :=
  RecInv IFR 6 p m₁ m ∧
    SeenR seen 16 (LstR (fun t x m => TyF b m t x) 11 p m (wd m IFR (p.toNat + 0))
      (wd m IFR (p.toNat + 1)) st.types) ∧
    SeenR seen 2 (LstR (fun t x m => CtF b m t x) 10 p m (wd m IFR (p.toNat + 2))
      (wd m IFR (p.toNat + 3)) st.ctors) ∧
    SeenR seen 8 (LstR (fun t x m => RecF b m t x) 11 p m (wd m IFR (p.toNat + 4))
      (wd m IFR (p.toNat + 5)) st.recs)

omit h64 hsize in
/-- A list read into the block record: slots `s`, `s + 1` written after the list's growth. -/
theorem blk_list_put (p s : Word) (hs : s.toNat + 1 < 6) (o c : Word) (m₁ m mL : Mem)
    (hI : RecInv IFR 6 p m₁ m) (hg : Grow m mL) (hR : Room mL) (ho : o.toNat = topN m IFR + 1) :
    RecInv IFR 6 p m₁ ((mL.set64 IFR (p + s) o).set64 IFR (p + (s + 1)) c) ∧
      IGrow m ((mL.set64 IFR (p + s) o).set64 IFR (p + (s + 1)) c) IFR p.toNat (p.toNat + 6) ∧
      IGrow mL ((mL.set64 IFR (p + s) o).set64 IFR (p + (s + 1)) c) IFR p.toNat (p.toNat + 6) ∧
      (∀ j, j < 6 → wd ((mL.set64 IFR (p + s) o).set64 IFR (p + (s + 1)) c) IFR (p.toNat + j) =
        if s.toNat + 1 = j then c else if s.toNat = j then o else wd m IFR (p.toNat + j)) ∧
      p.toNat + 6 ≤ o.toNat := by
  have hI1 := hI.grow hg hR
  have hs1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨p1, -, -, -, p5⟩ := slot_put IFR (.inl rfl) 6 (by decide) p s o m₁ mL hI1 (by omega)
  have e1 := slot_view IFR (.inl rfl) 6 (by decide) p s o m₁ mL hI1 (by omega)
  obtain ⟨p1', -, -, -, -⟩ := slot_put IFR (.inl rfl) 6 (by decide) p (s + 1) c m₁ _ p1 (by omega)
  have e1' := slot_view IFR (.inl rfl) 6 (by decide) p (s + 1) c m₁ _ p1 (by omega)
  obtain ⟨g, hR', hq1, hq6⟩ := hI
  have htm := g.top IFR (.inl rfl)
  have hp1 : (p + s).toNat = p.toNat + s.toNat := by
    rw [UInt64.toNat_add]; apply Nat.mod_eq_of_lt; have := hR'.2.2.1; have := hR'.1; omega
  have hp2 : (p + (s + 1)).toNat = p.toNat + s.toNat + 1 := by
    rw [UInt64.toNat_add, hs1]; apply Nat.mod_eq_of_lt; have := hR'.2.2.1; have := hR'.1; omega
  obtain ⟨u1, -, -⟩ := grow_set mL IFR (.inl rfl) (p + s) o p.toNat (p.toNat + 6) (by omega)
    (by omega) (by omega)
  obtain ⟨u1', -, -⟩ := grow_set (mL.set64 IFR (p + s) o) IFR (.inl rfl) (p + (s + 1)) c p.toNat
    (p.toNat + 6) (by omega) (by omega) (by omega)
  refine ⟨p1', (hg.ex IFR p.toNat (p.toNat + 6)).trans (u1.trans u1'), u1.trans u1', fun j hj => ?_,
    by omega⟩
  rw [e1', hs1]
  split
  · rfl
  rw [e1]
  split
  · rfl
  exact hg.keep IFR (.inl rfl) _ (by omega) (by omega) (by rintro ⟨-, -, h⟩; omega)

set_option hygiene false in
/-- A list key of the block: the list read by `lnk` into slots `s`, `s + 1` (`s1 = s + 1`), the
field `fnew`; the others carried. -/
macro "blk_list " kn:term "," s:term "," s1:term "," sub:term "," lnk:term "," st':term ","
    stb:term : tactic =>
    `(tactic| (
  ikey_res
  obtain ⟨o, c, mL, hl, rfl⟩ := list_arm b h64 hsize m m' 4 p $kn $s $sub i v e' rfl hiv hmem
  obtain ⟨l1, l2, l3, l4, l5, l6, -⟩ := $lnk b h64 hsize v m xv ev (o, c, e') mL hx hI.2.1 hl
  simp only at l1 l2 l3 l6
  subst l1
  rw [fldPutW_R _ _ _ _ _ (by decide), fldPutW_R _ _ _ _ _ (by decide)]
  obtain ⟨b1, b2, b2', b3, b4⟩ := blk_list_put p $s (by decide) o c m₁ m mL hI l4 l5 l6
  refine ⟨ev, _, $st', rfl, hok, b1, ?_⟩
  simp (config := {decide := true}) only [b3 0 (by decide), b3 1 (by decide), b3 2 (by decide),
    b3 3 (by decide), b3 4 (by decide), b3 5 (by decide), ↓reduceIte]
  refine ⟨?_, ?_, ?_⟩
  all_goals first
    | exact .inl ⟨l2, b4, runR_stab _ _ $stb _ _ _ _ b2' _ _ l3 b4⟩
    | exact seenR_or ‹_› (by decide) (fun hh => lstR_move _ _ (tyStab b) p m _ b2 _ _ _ _ rfl rfl _ hh)
    | exact seenR_or ‹_› (by decide) (fun hh => lstR_move _ _ (ctStab b) p m _ b2 _ _ _ _ rfl rfl _ hh)
    | exact seenR_or ‹_› (by decide) (fun hh => lstR_move _ _ (recStab b) p m _ b2 _ _ _ _ rfl rfl _
        hh)))

set_option maxHeartbeats 2000000 in
theorem blk_loop (m₁ : Mem) (p : Word) :
    IObjLoop b (fun i w seen (st : BlkSt) => scanIndDeclLoop b i w seen st.ctors st.recs st.types)
      4 p (BlkLR b m₁ p)
      (fun d m => RecInv IFR 6 p m₁ m ∧ ∀ tys cts rcs, d = .ind tys cts rcs →
        IndFR b m (wd m IFR (p.toNat + 0)) (wd m IFR (p.toNat + 1)) (wd m IFR (p.toNat + 2))
          (wd m IFR (p.toNat + 3)) (wd m IFR (p.toNat + 4)) (wd m IFR (p.toNat + 5)) tys cts rcs) := by
  constructor
  · dloop_stop scanIndDeclLoop
  · dloop_ws scanIndDeclLoop
  · dloop_close scanIndDeclLoop
    obtain ⟨hI, h1, h2, h3⟩ := hR
    obtain ⟨t1, -, t3⟩ := seenR_close h1 hM (by decide) (by decide)
    obtain ⟨c1, -, c3⟩ := seenR_close h2 hM (by decide) (by decide)
    obtain ⟨r1, -, r3⟩ := seenR_close h3 hM (by decide) (by decide)
    refine ⟨hI, fun tys cts rcs hd => ?_⟩
    cases hd
    exact ⟨t1, t3, c1, c3, r1, r3⟩
  · dloop_comma scanIndDeclLoop
  · dloop_quote scanIndDeclLoop
  · iloop_key scanIndDeclLoop
    all_goals obtain ⟨hI, h1, h2, h3⟩ := hR
    case kTypes =>
      rw [show UInt64.ofNat Key.kTypes.ctorIdx = (63 : Word) from rfl] at hmem
      blk_list 63, 0, 1, 0, tys_link, { st with types := xv }, tyStab b
    case kCtors =>
      rw [show UInt64.ofNat Key.kCtors.ctorIdx = (11 : Word) from rfl] at hmem
      blk_list 11, 2, 3, 1, cts_link, { st with ctors := xv }, ctStab b
    case kRecs =>
      rw [show UInt64.ofNat Key.kRecs.ctorIdx = (50 : Word) from rfl] at hmem
      blk_list 50, 4, 5, 2, recs_link, { st with recs := xv }, recStab b
    case kAll =>
      rw [show UInt64.ofNat Key.kAll.ctorIdx = (1 : Word) from rfl] at hmem
      ikey_res
      obtain ⟨he, rfl⟩ := all_arm b h64 hsize m m' 4 p _ 1 0 0 v xv ev e' rfl hx hmem
      subst he
      exact ⟨ev, _, st, rfl, hok, hI, seenR_or h1 (by decide) id, seenR_or h2 (by decide) id,
        seenR_or h3 (by decide) id⟩
    case kIsUnsafe =>
      rw [show UInt64.ofNat Key.kIsUnsafe.ctorIdx = (26 : Word) from rfl] at hmem
      ikey_res
      obtain ⟨he, rfl⟩ := boolp_arm b h64 hsize m m' 4 p _ 26 0 0 v xv ev e' rfl hx hmem
      subst he
      exact ⟨ev, _, st, rfl, hok, hI, seenR_or h1 (by decide) id, seenR_or h2 (by decide) id,
        seenR_or h3 (by decide) id⟩
  · dloop_other scanIndDeclLoop

/-- **The fields pass of an `inductive` line, linked**: on con-leche's `ok` path, a successful
`ind_fields(v)` returns the three lists of the block as runs of records related to con-leche's
(`IndFR`), and writes only `IFR`/`IFL`. -/
@[refines_part ConLeche.Frontend.scanIndDecl "the block's records (ind_fields)"]
theorem indFields_link (m m' : Mem)
    (hsz : (m.arr64 IFR).size < 2 ^ 63 ∧ (m.arr64 IFL).size < 2 ^ 63) (v : USize)
    (tys : List IndTypeRec) (cts : List IndCtorRec) (rcs : List IndRecRec) (e : USize)
    (hscan : scanIndDecl b v = .ok (.ind tys cts rcs) e) (r : List Word)
    (h : indFieldsW b.data m v.toUInt64 = some (r, m')) :
    ∃ to tn co cn ro rn, r = [to, tn, co, cn, ro, rn] ∧ IndFR b m' to tn co cn ro rn tys cts rcs ∧
      MemFrame [IFR, IFL] [] m m' ∧ Room m' := by
  unfold indFieldsW at h
  cases hr : ifResetW m with
  | none => rw [hr, fieldsK0_none] at h; cases h
  | some m1 =>
  rw [hr, fieldsK0_some] at h
  unfold ifResetW at hr
  split at hr
  · cases hr
  rename_i hlen
  simp only [Option.some.injEq] at hr
  subst hr
  -- the reset memory has room
  have hs1 : ((m.set64 IFR 0 0).set64 IFL 0 0).arr64 IFR = (m.arr64 IFR).set! 0 0 := by
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_same]; rfl
  have hs2 : ((m.set64 IFR 0 0).set64 IFL 0 0).arr64 IFL = (m.arr64 IFL).set! 0 0 := by
    rw [Mem.arr64_set64_same, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; rfl
  have hn1 : (m.arr64 IFR).size ≠ 0 := fun h0 => hlen (.inl (by simp [Mem.len64, h0]))
  have hn2 : (m.arr64 IFL).size ≠ 0 := fun h0 => hlen (.inr (by simp [Mem.len64, h0]))
  have hR1 : Room ((m.set64 IFR 0 0).set64 IFL 0 0) := by
    refine ⟨by rw [hs1]; simpa using hsz.1, by rw [hs2]; simpa using hsz.2, ?_, ?_⟩
    · simp only [topN, wd, hs1, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      simp [show 0 < (m.arr64 IFR).size by omega]
    · simp only [topN, wd, hs2, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      simp [show 0 < (m.arr64 IFL).size by omega]
  have hfr1 : MemFrame [IFR, IFL] [] m ((m.set64 IFR 0 0).set64 IFL 0 0) :=
    ((MemFrame.set64 m IFR (by decide) 0 0).mono (by simp) (by simp)).trans
      ((MemFrame.set64 _ IFL (by decide) 0 0).mono (by simp) (by simp))
  generalize (m.set64 IFR 0 0).set64 IFL 0 0 = m1 at h hR1 hfr1
  cases ha : allocW m1 IFR 6 with
  | none => rw [ha, fieldsK1_none] at h; cases h
  | some pm =>
  obtain ⟨p, m2⟩ := pm
  rw [ha, fieldsK1_some] at h
  have hI := recInv_alloc IFR (.inl rfl) 6 6 p m1 m2 hR1 rfl ha
  obtain ⟨-, -, -, a4, -, -, -⟩ := allocW_facts m1 m2 IFR (.inl rfl) 6 p hR1 ha
  cases ho : objW b.data m2 v.toUInt64 4 p with
  | none => rw [ho, fieldsK2_none] at h; cases h
  | some em =>
  obtain ⟨e3, m3⟩ := em
  rw [ho, fieldsK2_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨-, hI3, hF⟩ := item_gen b h64 hsize
    (fun i w seen (st : BlkSt) => scanIndDeclLoop b i w seen st.ctors st.recs st.types) 4 IFR 6
    (fun m₁ q d m => RecInv IFR 6 q m₁ m ∧ ∀ tys cts rcs, d = .ind tys cts rcs →
        IndFR b m (wd m IFR (q.toNat + 0)) (wd m IFR (q.toNat + 1)) (wd m IFR (q.toNat + 2))
          (wd m IFR (q.toNat + 3)) (wd m IFR (q.toNat + 4)) (wd m IFR (q.toNat + 5)) tys cts rcs)
    (BlkLR b) ⟨[], [], []⟩ (scanIndDecl b) (fun i x e h => by
      unfold scanIndDecl at h; split at h
      · exact h
      · cases h) (blk_loop b h64 hsize) v m2 p _ e e3 m3 hscan
    ⟨hI, seenR_zero _ _, seenR_zero _ _, seenR_zero _ _⟩ ho
  have hp : ∀ k : Nat, k < 6 → (p + UInt64.ofNat k).toNat = p.toNat + k := by
    intro k hk
    have := hI3.2.1.2.2.1
    have := hI3.2.1.1
    have := hI3.2.2.2
    have := hI3.1.top IFR (.inl rfl)
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)]
    apply Nat.mod_eq_of_lt; omega
  refine ⟨_, _, _, _, _, _, rfl, ?_, hfr1.trans (a4.fr.trans hI3.1.fr), hI3.2.1⟩
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
    show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl,
    show UInt64.ofNat 5 = (5 : Word) from rfl] at h1 h2 h3 h4 h5
  simp only [rdW_wd, h1, h2, h3, h4, h5]
  exact hF tys cts rcs rfl

end blk

end L.Front.Ind
