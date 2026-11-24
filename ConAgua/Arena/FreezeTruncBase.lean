module

public import ConAgua.Arena.FreezeRel

@[expose] public section

/-!
# The truncation theorem, part 1: what `truncFrozen` does to each array (lane parmode)

`truncFrozen m` (`FreezeRel.lean`) cuts every frozen array to its extent and leaves every other
array, the number of arrays and `CTL` alone:

* `truncFrozen_other`: an array that is not frozen (`fzSrcs`) is unchanged (so is `CTL`);
* `truncFrozen_mem`: a frozen array is its prefix of length `fzExt m z`;

and reading a prefix below its length reads the array (`rdW_extract`, `get?_extract`).
-/

namespace L.Arena

open ConRon.Arena

/-! ## Prefixes -/

theorem get?_extract (a : Array Word) {e i : Nat} (h : i < e) : (a.extract 0 e)[i]? = a[i]? := by
  simp only [Array.getElem?_extract, Nat.sub_zero, Nat.zero_add]
  split
  · rfl
  · rename_i hn
    have : a.size ≤ i := by omega
    simp [Array.getElem?_eq_none this]

theorem rdW_extract (a : Array Word) {e : Nat} {x : Word} (h : x.toNat < e) :
    rdW (a.extract 0 e) x = rdW a x := by
  simp only [rdW, get?_extract a h]

theorem size_extract0 (a : Array Word) (e : Nat) : (a.extract 0 e).size = min e a.size := by
  simp [Array.size_extract]

theorem getD_extract (a : Array Word) {e i : Nat} (h : i < e) :
    (a.extract 0 e)[i]?.getD 0 = a[i]?.getD 0 := by rw [get?_extract a h]

/-! ## Replacing one array -/

/-- `m` with word array `b` replaced by `v`. -/
def _root_.L.Mem.setA (m : Mem) (b : TieredArray) (v : Array Word) : Mem :=
  { m with words := fun s => if s = b then v else m.words s }

theorem Mem.setA_arr (m : Mem) (b c : TieredArray) (v : Array Word) :
    (m.setA b v).arr64 c = if c = b then v else m.arr64 c := rfl

theorem Mem.setA_self (m m' : Mem) (b : TieredArray) :
    (m.setA b (m'.arr64 b)).arr64 b = m'.arr64 b := by
  rw [Mem.setA_arr, ite_eq_left rfl]

/-! ## `truncList` -/

theorem truncList_other (m₀ : Mem) (b : TieredArray) :
    ∀ (zs : List (ArrId × Fz)) (m : Mem), (∀ e ∈ zs, (e.2.src : TieredArray) ≠ b) →
      (truncList m₀ m zs).arr64 b = m.arr64 b
  | [], _, _ => rfl
  | (x, z) :: zs, m, h => by
    rw [truncList, truncList_other m₀ b zs _ (fun e he => h e (List.mem_cons_of_mem _ he))]
    exact ite_eq_right (h (x, z) List.mem_cons_self).symm

theorem truncList_mem (m₀ : Mem) (x : ArrId) (z : Fz) :
    ∀ (zs : List (ArrId × Fz)) (m : Mem), (x, z) ∈ zs →
      zs.Pairwise (fun e e' => e.2.src ≠ e'.2.src) →
      (truncList m₀ m zs).arr64 z.src = (m₀.arr64 z.src).extract 0 (fzExt m₀ z)
  | [], _, h, _ => by cases h
  | (x', z') :: zs, m, h, hp => by
    rw [List.pairwise_cons] at hp
    rw [truncList]
    rcases List.mem_cons.mp h with e | e
    · cases e
      rw [truncList_other m₀ z.src zs _ (fun e he => TieredArray.t0_ne (hp.1 e he).symm)]
      exact ite_eq_left rfl
    · exact truncList_mem m₀ x z zs _ e hp.2

/-! ## `truncFrozen` -/

/-- The frozen arrays (sources), as a literal. -/
def fzSrcs : List TieredArray := tier0s
  [POOL, REC, SLOT, AREC, ASLOT, SREC, SSLOT, ZREC, ZSLOT, MREC, MSLOT, IREC, ISLOT, PREC, PSLOT,
   SOREC, SOSLOT, CREC, CSLOT, LEREC, LESLOT, BREC, BSLOT, FVREC, FVSLOT, LAREC, LASLOT, FAREC,
   FASLOT, PJREC, PJSLOT, NAREC, NASLOT, NSREC, NSSLOT, NNREC, NNSLOT, LSREC, LSSLOT, ADER, LADER,
   FADER, LEDER, PJDER, SHP, MHP, IHP, LSHP, SOLP, CLP, FVLP, PINS, EIXA, EIXS, EIXN, TIXA, TIXS,
   TIXN, EREC, FIRSTS, L.Front.DECL, L.Front.DLP, SIXA, SIXS, SIXN, STXA, STXS, STXN, MATA, MATS,
   MATN]

theorem frozen_srcs : (frozen.drop 1).map (fun e => (e.2.src : TieredArray)) = fzSrcs := by decide

theorem fzSrcs_nodup : fzSrcs.Nodup := by decide

theorem frozen_pairwise : (frozen.drop 1).Pairwise (fun e e' => e.2.src ≠ e'.2.src) := by
  have := fzSrcs_nodup
  rw [← frozen_srcs, List.Nodup, List.pairwise_map] at this
  exact this.imp fun h e => h (congrArg TieredArray.t0 e)

/-- **An array that is not frozen is unchanged.** -/
theorem truncFrozen_other (m : Mem) (b : TieredArray) (hb : b ∉ fzSrcs) :
    (truncFrozen m).arr64 b = m.arr64 b :=
  truncList_other m b _ m (fun e he hs => hb (by
    rw [← frozen_srcs, List.mem_map]; exact ⟨e, he, hs⟩))

theorem truncFrozen_ctl (m : Mem) : (truncFrozen m).arr64 CTL = m.arr64 CTL :=
  truncFrozen_other m CTL (by decide)

/-- **A frozen array is its prefix up to its extent.** -/
theorem truncFrozen_mem (m : Mem) {x : ArrId} {z : Fz} (h : (x, z) ∈ frozen.drop 1) :
    (truncFrozen m).arr64 z.src = (m.arr64 z.src).extract 0 (fzExt m z) :=
  truncList_mem m x z _ m h frozen_pairwise

theorem frozen_drop1 : frozen.drop 1 =
    [(POOL, ⟨POOL, fzCtl 0⟩)] ++
    fzStores.flatMap (fun (ra, sa, w, ca) =>
      [(ra, ⟨ra, .bin .mul (fzCtl ca) (fzC w)⟩), (sa, ⟨sa, fzSlotExt sa⟩)]) ++
    fzPCols.map (fun (c, ca) => (c, ⟨c, fzPExt ca⟩)) ++
    fzCols.map (fun (c, ca) => (c, ⟨c, fzCtl ca⟩)) ++
    [(PINS, ⟨PINS, fzC 73⟩),
     (EIXA, ⟨EIXA, .bin .mul (fzC 2) (fzCtl nanonCS.ca.toNat)⟩),
     (EIXS, ⟨EIXS, .bin .mul (fzC 2) (fzCtl nstrCS.ca.toNat)⟩),
     (EIXN, ⟨EIXN, .bin .mul (fzC 2) (fzCtl nnumCS.ca.toNat)⟩),
     (TIXA, ⟨TIXA, .bin .mul (fzC 2) (fzCtl nanonCS.ca.toNat)⟩),
     (TIXS, ⟨TIXS, .bin .mul (fzC 2) (fzCtl nstrCS.ca.toNat)⟩),
     (TIXN, ⟨TIXN, .bin .mul (fzC 2) (fzCtl nnumCS.ca.toNat)⟩),
     (EREC, ⟨EREC, fzCtl 129⟩),
     (FIRSTS, ⟨FIRSTS, fzDeclX⟩),
     (L.Front.DECL, ⟨L.Front.DECL, .bin .add (fzC 1) (.bin .mul (fzC 8) fzDeclX)⟩),
     (L.Front.DLP, ⟨L.Front.DLP, .bin .add (fzC 1) fzDlpX⟩)] ++
    [(SIXA, ⟨SIXA, fzSolExt nanonCS.ca.toNat⟩), (SIXS, ⟨SIXS, fzSolExt nstrCS.ca.toNat⟩),
     (SIXN, ⟨SIXN, fzSolExt nnumCS.ca.toNat⟩), (STXA, ⟨STXA, fzSolExt nanonCS.ca.toNat⟩),
     (STXS, ⟨STXS, fzSolExt nstrCS.ca.toNat⟩), (STXN, ⟨STXN, fzSolExt nnumCS.ca.toNat⟩),
     (MATA, ⟨MATA, fzSolExt nanonCS.ca.toNat⟩), (MATS, ⟨MATS, fzSolExt nstrCS.ca.toNat⟩),
     (MATN, ⟨MATN, fzSolExt nnumCS.ca.toNat⟩)] := by
  simp only [frozen, List.cons_append, List.drop_succ_cons, List.drop_zero, List.nil_append,
    List.append_assoc]

/-! ### The extents -/

theorem fzExt_ctl (m : Mem) (b : ArrId) (k : Nat) :
    fzExt m ⟨b, fzCtl k⟩ = (rdW (m.arr64 CTL) (UInt64.ofNat k)).toNat := by
  simp only [fzExt, fzCtl, Expr.pval, rd64, rdW, Array.getD_eq_getD_getElem?]

theorem fzExt_pext (m : Mem) (b : ArrId) (k : Nat) :
    fzExt m ⟨b, fzPExt k⟩ = ((rdW (m.arr64 CTL) (UInt64.ofNat k) + 1) >>> 1).toNat := by
  simp only [fzExt, fzPExt, fzCtl, fzC, Expr.pval, BinOp.eval, rd64, rdW, Array.getD_eq_getD_getElem?]
  rfl

theorem fzExt_mulC (m : Mem) (b : ArrId) (k w : Nat) :
    fzExt m ⟨b, .bin .mul (fzCtl k) (fzC w)⟩ =
      (rdW (m.arr64 CTL) (UInt64.ofNat k) * UInt64.ofNat w).toNat := by
  simp only [fzExt, fzCtl, fzC, Expr.pval, BinOp.eval, rd64, rdW, Array.getD_eq_getD_getElem?]

theorem fzExt_Cmul (m : Mem) (b : ArrId) (k w : Nat) :
    fzExt m ⟨b, .bin .mul (fzC w) (fzCtl k)⟩ =
      (UInt64.ofNat w * rdW (m.arr64 CTL) (UInt64.ofNat k)).toNat := by
  simp only [fzExt, fzCtl, fzC, Expr.pval, BinOp.eval, rd64, rdW, Array.getD_eq_getD_getElem?]

theorem fzExt_slot (m : Mem) (sa : ArrId) :
    fzExt m ⟨sa, fzSlotExt sa⟩ = (2 + (rdW (m.arr64 sa) 0 + SN0)).toNat := by
  simp only [fzExt, fzSlotExt, fzC, Expr.pval, BinOp.eval, rd64, rdW, Array.getD_eq_getD_getElem?]
  rfl

/-! ### Each frozen array -/

theorem truncFrozen_pool (m : Mem) :
    (truncFrozen m).arr64 POOL = (m.arr64 POOL).extract 0 m.top.toNat := by
  have := truncFrozen_mem m (x := POOL) (z := ⟨POOL, fzCtl 0⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_ctl]; rfl

theorem truncFrozen_ra (m : Mem) {ra sa : ArrId} {w ca : Nat} (h : (ra, sa, w, ca) ∈ fzStores) :
    (truncFrozen m).arr64 ra = (m.arr64 ra).extract 0
      (rdW (m.arr64 CTL) (UInt64.ofNat ca) * UInt64.ofNat w).toNat := by
  have := truncFrozen_mem m (x := ra) (z := ⟨ra, .bin .mul (fzCtl ca) (fzC w)⟩) (by
    rw [frozen_drop1]
    simp only [List.mem_append, List.mem_flatMap]
    exact .inl (.inl (.inl (.inl (.inr ⟨_, h, by simp⟩)))))
  rw [this, fzExt_mulC]

theorem truncFrozen_sa (m : Mem) {ra sa : ArrId} {w ca : Nat} (h : (ra, sa, w, ca) ∈ fzStores) :
    (truncFrozen m).arr64 sa = (m.arr64 sa).extract 0 (2 + (rdW (m.arr64 sa) 0 + SN0)).toNat := by
  have := truncFrozen_mem m (x := sa) (z := ⟨sa, fzSlotExt sa⟩) (by
    rw [frozen_drop1]
    simp only [List.mem_append, List.mem_flatMap]
    exact .inl (.inl (.inl (.inl (.inr ⟨_, h, by simp⟩)))))
  rw [this, fzExt_slot]

theorem truncFrozen_col (m : Mem) {c : ArrId} {ca : Nat} (h : (c, ca) ∈ fzCols) :
    (truncFrozen m).arr64 c = (m.arr64 c).extract 0 (rdW (m.arr64 CTL) (UInt64.ofNat ca)).toNat := by
  have := truncFrozen_mem m (x := c) (z := ⟨c, fzCtl ca⟩) (by
    rw [frozen_drop1]
    simp only [List.mem_append, List.mem_map]
    exact .inl (.inl (.inr ⟨_, h, rfl⟩)))
  rw [this, fzExt_ctl]

theorem truncFrozen_pcol (m : Mem) {c : ArrId} {ca : Nat} (h : (c, ca) ∈ fzPCols) :
    (truncFrozen m).arr64 c =
      (m.arr64 c).extract 0 ((rdW (m.arr64 CTL) (UInt64.ofNat ca) + 1) >>> 1).toNat := by
  have := truncFrozen_mem m (x := c) (z := ⟨c, fzPExt ca⟩) (by
    rw [frozen_drop1]
    simp only [List.mem_append, List.mem_map]
    exact .inl (.inl (.inl (.inr ⟨_, h, rfl⟩))))
  rw [this, fzExt_pext]

theorem truncFrozen_pins (m : Mem) : (truncFrozen m).arr64 PINS = (m.arr64 PINS).extract 0 73 := by
  have := truncFrozen_mem m (x := PINS) (z := ⟨PINS, fzC 73⟩) (by rw [frozen_drop1]; simp)
  rw [this]; rfl

theorem truncFrozen_eixa (m : Mem) : (truncFrozen m).arr64 EIXA =
    (m.arr64 EIXA).extract 0 (2 * rdW (m.arr64 CTL) (UInt64.ofNat nanonCS.ca.toNat)).toNat := by
  have := truncFrozen_mem m (x := EIXA)
    (z := ⟨EIXA, .bin .mul (fzC 2) (fzCtl nanonCS.ca.toNat)⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_Cmul]; rfl

theorem truncFrozen_eixs (m : Mem) : (truncFrozen m).arr64 EIXS =
    (m.arr64 EIXS).extract 0 (2 * rdW (m.arr64 CTL) (UInt64.ofNat nstrCS.ca.toNat)).toNat := by
  have := truncFrozen_mem m (x := EIXS)
    (z := ⟨EIXS, .bin .mul (fzC 2) (fzCtl nstrCS.ca.toNat)⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_Cmul]; rfl

theorem truncFrozen_eixn (m : Mem) : (truncFrozen m).arr64 EIXN =
    (m.arr64 EIXN).extract 0 (2 * rdW (m.arr64 CTL) (UInt64.ofNat nnumCS.ca.toNat)).toNat := by
  have := truncFrozen_mem m (x := EIXN)
    (z := ⟨EIXN, .bin .mul (fzC 2) (fzCtl nnumCS.ca.toNat)⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_Cmul]; rfl

theorem truncFrozen_tixa (m : Mem) : (truncFrozen m).arr64 TIXA =
    (m.arr64 TIXA).extract 0 (2 * rdW (m.arr64 CTL) (UInt64.ofNat nanonCS.ca.toNat)).toNat := by
  have := truncFrozen_mem m (x := TIXA)
    (z := ⟨TIXA, .bin .mul (fzC 2) (fzCtl nanonCS.ca.toNat)⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_Cmul]; rfl

theorem truncFrozen_tixs (m : Mem) : (truncFrozen m).arr64 TIXS =
    (m.arr64 TIXS).extract 0 (2 * rdW (m.arr64 CTL) (UInt64.ofNat nstrCS.ca.toNat)).toNat := by
  have := truncFrozen_mem m (x := TIXS)
    (z := ⟨TIXS, .bin .mul (fzC 2) (fzCtl nstrCS.ca.toNat)⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_Cmul]; rfl

theorem truncFrozen_tixn (m : Mem) : (truncFrozen m).arr64 TIXN =
    (m.arr64 TIXN).extract 0 (2 * rdW (m.arr64 CTL) (UInt64.ofNat nnumCS.ca.toNat)).toNat := by
  have := truncFrozen_mem m (x := TIXN)
    (z := ⟨TIXN, .bin .mul (fzC 2) (fzCtl nnumCS.ca.toNat)⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_Cmul]; rfl

theorem truncFrozen_erec (m : Mem) : (truncFrozen m).arr64 EREC = (m.arr64 EREC).extract 0 (erTop m) := by
  have := truncFrozen_mem m (x := EREC) (z := ⟨EREC, fzCtl 129⟩) (by rw [frozen_drop1]; simp)
  rw [this, fzExt_ctl]; rfl

/-- The compared run's extent form at `m`: `e` with the flag `CTL[cmpCW]` off, `CTL[k]` with it
on (`fzCmpOr`). -/
def cmpOrW (m : Mem) (e : Word) (k : Nat) : Word :=
  e + rdW (m.arr64 CTL) (UInt64.ofNat cmpCW) * (rdW (m.arr64 CTL) (UInt64.ofNat k) - e)

/-- The extent of `FIRSTS` (`fzDeclX`). -/
def xD (m : Mem) : Word := cmpOrW m (rdW (m.arr64 L.Front.DECL) 0) cmpKD

/-- The pool top the extent of `DLP` covers (`fzDlpX`). -/
def xP (m : Mem) : Word := cmpOrW m (rdW (m.arr64 L.Front.DLP) 0) cmpKP

theorem cmpOrW_off {m : Mem} (h : rdW (m.arr64 CTL) (UInt64.ofNat cmpCW) = 0) (e : Word) (k : Nat) :
    cmpOrW m e k = e := by
  simp [cmpOrW, h]

theorem cmpOrW_on {m : Mem} (h : rdW (m.arr64 CTL) (UInt64.ofNat cmpCW) = 1) (e : Word) (k : Nat) :
    cmpOrW m e k = rdW (m.arr64 CTL) (UInt64.ofNat k) := by
  simp only [cmpOrW, h, UInt64.one_mul]; grind

theorem truncFrozen_firsts (m : Mem) :
    (truncFrozen m).arr64 FIRSTS = (m.arr64 FIRSTS).extract 0 (xD m).toNat := by
  have := truncFrozen_mem m (x := FIRSTS) (z := ⟨FIRSTS, fzDeclX⟩) (by rw [frozen_drop1]; simp)
  rw [this]; simp only [fzExt, fzDeclX, fzDlpX, fzCmpOr, fzDecl, fzCtl, fzC, Expr.pval, BinOp.eval, rd64, rdW, xD, xP, cmpOrW, cmpCW, cmpKD, cmpKP, Array.getD_eq_getD_getElem?]; rfl

theorem truncFrozen_decl (m : Mem) : (truncFrozen m).arr64 L.Front.DECL =
    (m.arr64 L.Front.DECL).extract 0 (1 + 8 * xD m).toNat := by
  have := truncFrozen_mem m (x := L.Front.DECL)
    (z := ⟨L.Front.DECL, .bin .add (fzC 1) (.bin .mul (fzC 8) fzDeclX)⟩) (by rw [frozen_drop1]; simp)
  rw [this]; simp only [fzExt, fzDeclX, fzDlpX, fzCmpOr, fzDecl, fzCtl, fzC, Expr.pval, BinOp.eval, rd64, rdW, xD, xP, cmpOrW, cmpCW, cmpKD, cmpKP, Array.getD_eq_getD_getElem?]; rfl

theorem truncFrozen_dlp (m : Mem) : (truncFrozen m).arr64 L.Front.DLP =
    (m.arr64 L.Front.DLP).extract 0 (1 + xP m).toNat := by
  have := truncFrozen_mem m (x := L.Front.DLP)
    (z := ⟨L.Front.DLP, .bin .add (fzC 1) fzDlpX⟩) (by rw [frozen_drop1]; simp)
  rw [this]; simp only [fzExt, fzDeclX, fzDlpX, fzCmpOr, fzDecl, fzCtl, fzC, Expr.pval, BinOp.eval, rd64, rdW, xD, xP, cmpOrW, cmpCW, cmpKD, cmpKP, Array.getD_eq_getD_getElem?]; rfl

/-- **A solution row** (`SIX*`, `STX*`, `MAT*`) with the compare flag `CTL[cmpCW] = 1`: its
prefix of `2 · CTL[k]` words. -/
theorem truncFrozen_sol (m : Mem) {a : ArrId} {k : Nat} (h : (a, ⟨a, fzSolExt k⟩) ∈ frozen.drop 1)
    (hf : rdW (m.arr64 CTL) (UInt64.ofNat cmpCW) = 1) :
    (truncFrozen m).arr64 a = (m.arr64 a).extract 0 (2 * rdW (m.arr64 CTL) (UInt64.ofNat k)).toNat := by
  rw [truncFrozen_mem m h]
  simp only [fzExt, fzSolExt, fzCtl, fzC, Expr.pval, BinOp.eval, rd64, rdW,
    Array.getD_eq_getD_getElem?] at hf ⊢
  have e : (Nat.toUInt64 cmpCW).toNat = (UInt64.ofNat cmpCW).toNat := rfl
  rw [e, hf, UInt64.one_mul]; rfl

end L.Arena
