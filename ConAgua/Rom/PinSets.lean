import ConAgua.Rom.PinReadSpec
import ConAgua.Rom.DecExpr

/-!
# The pin-set reader in the decoder direction (lane `romload`)

`intern_pin_sets` (`ConAgua/Rom/PinRead.lean`, model `internPinSetsW`) on the untrusted pin data:
a model run that returns interned **some** variant list `pins` exactly as the twin's
`internPinSets pins` does (`internPinSetsW_dec`). Each pin is one expression at a fresh memo (a
memo reset, then `romExprW_dec`/`dec_child`, as `internExpr e = (internExprGo ∅ e).2`); each
certificate list is a reset, then its expressions at one memo (`internExprList`).

The result in L is `PinSetsR`: the list of 40-word `EREC` records at `CTL[150]` (offset) and
`CTL[151]` (count); a record holds the eight pin handles, then per certificate list its `EREC`
slice `(offset, length)`, then per type-pin list its `EREC` slice `(offset, length)` of `length`
pairs `[name, type]` (a type pin is a name, then its type at a fresh memo, as `internTypePins`). Every allocation is above the record pool's top `CTL[129]`, which only
grows, so a record written early is not overwritten later: the stage's writes are tracked by `EW`
("`EREC` below the old top changed only in `[lo, hi)`").
-/

open ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend

namespace L.Rom

open L.Arena L.Ind

/-! ## The relation -/

/-- The variant's pins, in field order. -/
def pinsOf (ip : INatOpPinSet) : List EIdx :=
  [ip.divPin, ip.modPin, ip.gcdPin, ip.landPin, ip.lorPin, ip.xorPin, ip.shiftLeftPin, ip.shiftRightPin]

/-- The variant's certificate lists, in field order. -/
def certsOf (ip : INatOpPinSet) : List (List EIdx) :=
  [ip.divProofs, ip.modProofs, ip.gcdProofs, ip.landProofs, ip.lorProofs, ip.xorProofs,
   ip.shiftLeftProofs, ip.shiftRightProofs]

theorem certsOf_length (ip : INatOpPinSet) : (certsOf ip).length = 8 := rfl

/-- The variant's type-pin lists, in field order. -/
def tpinsOf (ip : INatOpPinSet) : List (List (NIdx × EIdx)) :=
  [ip.divTypePins, ip.modTypePins, ip.gcdTypePins, ip.landTypePins, ip.lorTypePins, ip.xorTypePins,
   ip.shiftLeftTypePins, ip.shiftRightTypePins]

theorem tpinsOf_length (ip : INatOpPinSet) : (tpinsOf ip).length = 8 := rfl

/-- **An `EREC` slice holds the handles `hs`**: `l` words at `o`, below the pool's top. -/
def SliceR (mem : Mem) (o l : Word) (hs : List EIdx) : Prop :=
  o.toNat + l.toNat ≤ erecTop mem ∧ l.toNat = hs.length ∧
  ∀ i (hi : i < hs.length), rdW (mem.arr64 EREC) (o + UInt64.ofNat i) = hs[i].word.toUInt64

/-- Certificate list `j` of the record at `r`: the slice whose offset and length are at
`r + 8 + 2j`, `r + 9 + 2j`. -/
def HdrR (mem : Mem) (r : Word) (j : Nat) (hs : List EIdx) : Prop :=
  SliceR mem (rdW (mem.arr64 EREC) (r + 8 + 2 * UInt64.ofNat j))
    (rdW (mem.arr64 EREC) (r + 9 + 2 * UInt64.ofNat j)) hs

/-- **An `EREC` slice holds the type pins `ps`**: `l` pairs at `o` (the name at `o + 2i`, the type
at `o + 2i + 1`), below the pool's top. -/
def TPinsR (mem : Mem) (o l : Word) (ps : List (NIdx × EIdx)) : Prop :=
  o.toNat + 2 * l.toNat ≤ erecTop mem ∧ l.toNat = ps.length ∧
  ∀ i (hi : i < ps.length),
    rdW (mem.arr64 EREC) (o + 2 * UInt64.ofNat i) = ps[i].1.word.toUInt64 ∧
    rdW (mem.arr64 EREC) (o + 2 * UInt64.ofNat i + 1) = ps[i].2.word.toUInt64

/-- Type-pin list `j` of the record at `r`: the slice whose offset and length are at
`r + 24 + 2j`, `r + 25 + 2j`. -/
def THdrR (mem : Mem) (r : Word) (j : Nat) (ps : List (NIdx × EIdx)) : Prop :=
  TPinsR mem (rdW (mem.arr64 EREC) (r + 24 + 2 * UInt64.ofNat j))
    (rdW (mem.arr64 EREC) (r + 25 + 2 * UInt64.ofNat j)) ps

/-- **The variant `ip` in the 40-word record at `r`** (pins at `r + 0 ‥ 7`; certificate list `j`'s
slice `(off, len)` at `r + 8 + 2j`, `r + 9 + 2j`; type-pin list `j`'s at `r + 24 + 2j`,
`r + 25 + 2j`); handle words are `x.word.toUInt64`. Everything is below the pool's top. -/
def PinSetR (mem : Mem) (r : Word) (ip : INatOpPinSet) : Prop :=
  r.toNat + 40 ≤ erecTop mem ∧ SliceR mem r 8 (pinsOf ip) ∧
  (∀ j (hj : j < 8), HdrR mem r j ((certsOf ip)[j]'(by rw [certsOf_length]; exact hj))) ∧
  ∀ j (hj : j < 8), THdrR mem r j ((tpinsOf ip)[j]'(by rw [tpinsOf_length]; exact hj))

/-- **The interned variant list**: `CTL[151]` records, their pointers at `EREC[CTL[150] ‥]`. -/
def PinSetsR (mem : Mem) (ips : List INatOpPinSet) : Prop :=
  (rdW (mem.arr64 CTL) 151).toNat = ips.length ∧
  (rdW (mem.arr64 CTL) 150).toNat + ips.length ≤ erecTop mem ∧ ∀ k (hk : k < ips.length),
    PinSetR mem (rdW (mem.arr64 EREC) (rdW (mem.arr64 CTL) 150 + UInt64.ofNat k)) ips[k]

/-- The frame of the stage: the record pool, its top, the variant list's header, and the
expression reader's frame. -/
def PinsA : List ArrId := EREC :: ExprA
def PinsC : List Word := 129 :: 150 :: 151 :: ExprC

/-! ## Word arithmetic -/

theorem addN {x y : Word} (h : x.toNat + y.toNat < 2 ^ 64) : (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h

theorem top_lt (m : Mem) : erecTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt

theorem ofNatN {i : Nat} (h : i < 2 ^ 64) : (UInt64.ofNat i).toNat = i := by
  rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h

/-! ## `EW`: what a step wrote in `EREC` -/

/-- **`EREC` below `m`'s top changed only in `[lo, hi)`**; the top did not go down; the
variant list's header `CTL[150]`, `CTL[151]` unchanged. -/
structure EW (lo hi : Nat) (m m' : Mem) : Prop where
  top : erecTop m ≤ erecTop m'
  low : ∀ i, i < erecTop m → (i < lo ∨ hi ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?
  size : (m'.arr64 EREC).size = (m.arr64 EREC).size
  c150 : rdW (m'.arr64 CTL) 150 = rdW (m.arr64 CTL) 150
  c151 : rdW (m'.arr64 CTL) 151 = rdW (m.arr64 CTL) 151

theorem EW.refl (lo hi : Nat) (m : Mem) : EW lo hi m m :=
  ⟨Nat.le_refl _, fun _ _ _ => rfl, rfl, rfl, rfl⟩

/-- Two steps, the second's window outside the first's frame below the first's top. -/
theorem EW.trans {lo hi lo₂ hi₂ : Nat} {m₁ m₂ m₃ : Mem} (h₁ : EW lo hi m₁ m₂) (h₂ : EW lo₂ hi₂ m₂ m₃)
    (hd : ∀ i, i < erecTop m₁ → (i < lo ∨ hi ≤ i) → (i < lo₂ ∨ hi₂ ≤ i)) : EW lo hi m₁ m₃ :=
  ⟨Nat.le_trans h₁.top h₂.top,
   fun i hi' hw => (h₂.low i (Nat.lt_of_lt_of_le hi' h₁.top) (hd i hi' hw)).trans (h₁.low i hi' hw),
   h₂.size.trans h₁.size, h₂.c150.trans h₁.c150, h₂.c151.trans h₁.c151⟩

/-- A frame that keeps `EREC`, its top and the header is an `EW` of any window. -/
theorem EW.frame {A : List ArrId} {C : List Word} {m m' : Mem} (lo hi : Nat) (hf : MemFrame A C m m')
    (hA : EREC ∉ A) (h1 : (129 : Word) ∉ C) (h2 : (150 : Word) ∉ C) (h3 : (151 : Word) ∉ C) :
    EW lo hi m m' := by
  have hE := hf.1 EREC hA (by decide)
  refine ⟨?_, fun i _ _ => by rw [hE], by rw [hE], hf.2.1 150 h2, hf.2.1 151 h3⟩
  simp only [erecTop]; rw [hf.2.1 129 h1]; exact Nat.le_refl _

/-- One `EREC` write. -/
theorem EW.set (m : Mem) (x v : Word) : EW x.toNat (x.toNat + 1) m (m.set64 EREC x v) := by
  have hc : (m.set64 EREC x v).arr64 CTL = m.arr64 CTL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨by simp only [erecTop, hc]; exact Nat.le_refl _, fun i _ hw => ?_, Mem.size_arr64_set64 _ _ _ _,
    by rw [hc], by rw [hc]⟩
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  rw [ite_eq_right (by omega)]

/-- **`erec_alloc`**: the old top, raised by `k`, inside `EREC`. -/
theorem erAlloc_ok {m m' : Mem} {k o : Word} (h : erAllocW m k = some (o, m'))
    (hc : 151 < (m.arr64 CTL).size) :
    o.toNat = erecTop m ∧ erecTop m' = o.toNat + k.toNat ∧ o.toNat + k.toNat ≤ (m.arr64 EREC).size ∧
      MemFrame [] [129] m m' ∧ ∀ lo hi, EW lo hi m m' := by
  simp only [erAllocW] at h
  by_cases h1 : m.len64 EREC < rdW (m.arr64 CTL) 129
  · simp [h1] at h
  by_cases h2 : m.len64 EREC - rdW (m.arr64 CTL) 129 < k
  · simp [h1, h2] at h
  simp only [h1, h2, ite_false, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hlen : (m.len64 EREC).toNat = (m.arr64 EREC).size % 2 ^ 64 := by simp [Mem.len64]
  have hml := Nat.mod_le (m.arr64 EREC).size (2 ^ 64)
  have hml2 := Nat.mod_lt (m.arr64 EREC).size (show 2 ^ 64 > 0 by decide)
  have hq : (rdW (m.arr64 CTL) 129).toNat ≤ (m.arr64 EREC).size % 2 ^ 64 := by
    have : ¬ (m.len64 EREC).toNat < (rdW (m.arr64 CTL) 129).toNat := h1
    omega
  have hroom : (rdW (m.arr64 CTL) 129).toNat + k.toNat ≤ (m.arr64 EREC).size % 2 ^ 64 := by
    have : ¬ (m.len64 EREC - rdW (m.arr64 CTL) 129).toNat < k.toNat := h2
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)] at this
    omega
  have hf : MemFrame [] [129] m (erAllocMem m k) := MemFrame.setCtl m 129 _
  have htop : erecTop (erAllocMem m k) = (rdW (m.arr64 CTL) 129).toNat + k.toNat := by
    simp only [erecTop, erAllocMem, rdW_set64]
    rw [ite_eq_left ⟨trivial, trivial, by simp; omega⟩, addN (by omega)]
  refine ⟨rfl, htop, by omega, hf, fun lo hi => ?_⟩
  have hE : (erAllocMem m k).arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp) (by decide)
  exact ⟨by rw [htop]; simp only [erecTop]; omega, fun i _ _ => by rw [hE], by rw [hE],
    hf.2.1 150 (by decide), hf.2.1 151 (by decide)⟩

/-! ## Slices -/

theorem SliceR.nil {m : Mem} {o : Word} (h : o.toNat ≤ erecTop m) : SliceR m o 0 [] :=
  ⟨by simpa using h, rfl, fun i hi => by simp at hi⟩

theorem SliceR.frame {m m' : Mem} {o l : Word} {hs : List EIdx} {lo hi : Nat} (h : SliceR m o l hs)
    (hw : EW lo hi m m') (hd : o.toNat + l.toNat ≤ lo ∨ hi ≤ o.toNat) : SliceR m' o l hs := by
  obtain ⟨hb, hl, hv⟩ := h
  refine ⟨Nat.le_trans hb hw.top, hl, fun i hi' => ?_⟩
  have ht := top_lt m
  have hx : (o + UInt64.ofNat i).toNat = o.toNat + i := by
    rw [addN] <;> rw [ofNatN (by omega)] <;> omega
  rw [← hv i hi', rdW, rdW, hx, hw.low _ (by omega) (by omega)]

/-- A slice: its first word, then the rest. -/
theorem SliceR.cons {m : Mem} {o o' l l' : Word} {h : EIdx} {hs : List EIdx}
    (h₁ : rdW (m.arr64 EREC) o = h.word.toUInt64) (h₂ : SliceR m o' l hs) (ho : o' = o + 1)
    (hl : l'.toNat = l.toNat + 1) (hb : o.toNat + 1 ≤ erecTop m) : SliceR m o l' (h :: hs) := by
  obtain ⟨hb2, hl2, hv⟩ := h₂
  have ht := top_lt m
  have ho' : o'.toNat = o.toNat + 1 := by subst ho; rw [addN (by simp; omega)]; simp
  refine ⟨by omega, by simp; omega, fun i hi => ?_⟩
  cases i with
  | zero => simpa using h₁
  | succ i =>
    have := hv i (by simpa using hi)
    rw [ho] at this
    simp only [List.getElem_cons_succ]
    rw [← this]
    congr 1
    rw [UInt64.ofNat_add, UInt64.ofNat_one]; ac_rfl

/-! ## The invariants -/

/-- The stage's invariant between expressions (no memo). -/
structure SInv (mem : Mem) (a : AState) : Prop where
  arena : ArenaD mem a
  rset : RsetR mem
  ok : StateOK a
  stk : (stkTop mem).toNat < 2 ^ 61
  ctl : 151 < (mem.arr64 CTL).size
  top : erecTop mem ≤ (mem.arr64 EREC).size
  /-- The pool's mode (lane tierpool). -/
  mode : ModeOK mem

theorem hiA : ∀ b ∈ ([EREC] : List ArrId), 64 ≤ b ∧ b < 256 := by decide
theorem hiC : ∀ x ∈ ([129, 150, 151] : List Word), 64 ≤ x.toNat := by simp
theorem hiC' : ∀ x ∈ ([132, 148, 149] : List Word), 64 ≤ x.toNat := by simp

/-- The decoder's invariant across the record pool's writes. -/
theorem DecInv.frameE {mem mem' : Mem} {a : AState} {seen : List ConLeche.Expr} {m : EMemo}
    (inv : DecInv mem a seen m) (hf : MemFrame [EREC] [129, 150, 151] mem mem') : DecInv mem' a seen m :=
  ⟨ArenaD.frameHi hf hiA hiC inv.arena,
   inv.memo.of_eq (hf.1 RMEMO (by decide) (by decide)) (hf.2.1 132 (by decide)) (hf.2.2.1 CTL),
   inv.nodup, inv.comp, inv.fits, inv.rset.frame hf (by decide) (by decide) (by decide) (by decide),
   inv.ok, inv.emok, by simp only [stkTop]; rw [hf.2.1 131 (by decide)]; exact inv.stk,
   by rw [hf.2.2.1 CTL]; exact inv.ctl, inv.mode.frame hf (by decide) (by decide)⟩

theorem SInv.frameE {mem mem' : Mem} {a : AState} (inv : SInv mem a)
    (hf : MemFrame [EREC] [129, 150, 151] mem mem') (ht : erecTop mem' ≤ (mem'.arr64 EREC).size) :
    SInv mem' a :=
  ⟨ArenaD.frameHi hf hiA hiC inv.arena,
   inv.rset.frame hf (by decide) (by decide) (by decide) (by decide),
   inv.ok, by simp only [stkTop]; rw [hf.2.1 131 (by decide)]; exact inv.stk,
   by rw [hf.2.2.1 CTL]; exact inv.ctl, ht, inv.mode.frame hf (by decide) (by decide)⟩

/-- After an expression: the decoder's invariant, sizes and top as before. -/
theorem SInv.of_dec {mem mem' : Mem} {a a' : AState} {seen : List ConLeche.Expr} {m : EMemo}
    (inv : SInv mem a) (hd : DecInv mem' a' seen m) (hf : MemFrame PinsA ExprC mem mem') : SInv mem' a' :=
  ⟨hd.arena, hd.rset, hd.ok, hd.stk, by rw [hf.2.2.1 CTL]; exact inv.ctl, by
    simp only [erecTop]; rw [hf.2.1 129 (by decide), hf.2.2.1 EREC]; exact inv.top, hd.mode⟩

/-- A memo reset: the decoder's invariant at the empty memo. -/
theorem SInv.reset {mem : Mem} {a : AState} (inv : SInv mem a) (hok : rclearOK mem) :
    DecInv (resetMem mem) a [] (∅ : EMemo) :=
  ⟨ArenaD.frameHi (resetMem_frame1 mem) (by simp) hiC' inv.arena,
   MemoR.fresh mem (by have := inv.ctl; omega), List.nodup_nil, by simp, by simp,
   RsetR.reset inv.rset hok, inv.ok, EMemoOK.empty _, by rw [resetMem_stk]; exact inv.stk,
   by rw [(resetMem_frame1 mem).2.2.1 CTL]; have := inv.ctl; omega,
   (memFrame_top (resetMem_frame1 mem) (by decide)).mode inv.arena.1.lit.1 inv.mode⟩

theorem resetMem_EW (lo hi : Nat) (mem : Mem) : EW lo hi mem (resetMem mem) :=
  EW.frame lo hi (resetMem_frame1 mem) (by simp) (by decide) (by decide) (by decide)

theorem resetMem_top (mem : Mem) : erecTop (resetMem mem) = erecTop mem := by
  simp only [erecTop]; rw [(resetMem_frame1 mem).2.1 129 (by decide)]

theorem resetMem_size (mem : Mem) : ((resetMem mem).arr64 EREC).size = (mem.arr64 EREC).size :=
  (resetMem_frame1 mem).2.2.1 EREC

theorem frame_set (m : Mem) (x v : Word) : MemFrame [EREC] [129, 150, 151] m (m.set64 EREC x v) :=
  (MemFrame.set64 m EREC (by decide) x v).mono (by simp) (by simp)

theorem frame_pins_set (m : Mem) (x v : Word) : MemFrame PinsA PinsC m (m.set64 EREC x v) :=
  (MemFrame.set64 m EREC (by decide) x v).mono (by simp [PinsA]) (by simp)

theorem frame_pins_expr {m m' : Mem} (h : MemFrame ExprA ExprC m m') : MemFrame PinsA PinsC m m' :=
  h.mono (fun b hb => by simp [PinsA, hb]) (fun x hx => by simp [PinsC, hx])

theorem frame_pins_reset (m : Mem) : MemFrame PinsA PinsC m (resetMem m) :=
  frame_pins_expr (resetMem_frame m)

theorem erec_notin : EREC ∉ ExprA := by simp [ExprA, RomA, StoreA]; decide

theorem c_notin (x : Word) (hx : 64 ≤ x.toNat) (h1 : x ≠ 132) (h2 : x ≠ 148) (h3 : x ≠ 149)
    (h4 : x ≠ 131) : x ∉ ExprC := by
  simp only [ExprC, RomC, List.mem_cons, not_or]
  exact ⟨h1, h2, h3, h4, not_mem_storeC x hx⟩

theorem EW.expr {m m' : Mem} (lo hi : Nat) (hf : MemFrame ExprA ExprC m m') : EW lo hi m m' :=
  EW.frame lo hi hf erec_notin (c_notin _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (c_notin _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (c_notin _ (by decide) (by decide) (by decide) (by decide) (by decide))

theorem expr_top {m m' : Mem} (hf : MemFrame ExprA ExprC m m') : erecTop m' = erecTop m := by
  simp only [erecTop]
  rw [hf.2.1 129 (c_notin _ (by decide) (by decide) (by decide) (by decide) (by decide))]

/-- An `EREC` write in bounds reads back. -/
theorem rdW_setE (m : Mem) (x v : Word) (hx : x.toNat < (m.arr64 EREC).size) :
    rdW ((m.set64 EREC x v).arr64 EREC) x = v := by
  rw [rdW_set64]; simp [hx]

theorem EW.get {lo hi : Nat} {m m' : Mem} (hw : EW lo hi m m') (x : Word) (hx : x.toNat < erecTop m)
    (hd : x.toNat < lo ∨ hi ≤ x.toNat) : rdW (m'.arr64 EREC) x = rdW (m.arr64 EREC) x := by
  rw [rdW, rdW, hw.low _ hx hd]

theorem sub8 {k : Word} (hk : k.toNat ≤ 8) : (8 - k).toNat = 8 - k.toNat := by
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using hk)]; simp

theorem succN {k : Word} (hk : k.toNat < 8) : (k + 1).toNat = k.toNat + 1 := addN (by simp; omega)

theorem hdrIdx {r j : Word} (hr : r.toNat + 24 < 2 ^ 64) (hj : j.toNat < 8) :
    (r + 8 + 2 * j).toNat = r.toNat + 8 + 2 * j.toNat ∧ (r + 9 + 2 * j).toNat = r.toNat + 9 + 2 * j.toNat := by
  simp only [UInt64.toNat_add, UInt64.toNat_mul]
  simp only [UInt64.reduceToNat]
  omega

theorem thdrIdx {r j : Word} (hr : r.toNat + 40 < 2 ^ 64) (hj : j.toNat < 8) :
    (r + 24 + 2 * j).toNat = r.toNat + 24 + 2 * j.toNat ∧
      (r + 25 + 2 * j).toNat = r.toNat + 25 + 2 * j.toNat := by
  simp only [UInt64.toNat_add, UInt64.toNat_mul]
  simp only [UInt64.reduceToNat]
  omega

/-! ## Type-pin slices -/

theorem TPinsR.nil {m : Mem} {o : Word} (h : o.toNat ≤ erecTop m) : TPinsR m o 0 [] :=
  ⟨by simpa using h, rfl, fun i hi => by simp at hi⟩

theorem pairIdx {o : Word} {i : Nat} (h : o.toNat + 2 * i + 2 < 2 ^ 64) :
    (o + 2 * UInt64.ofNat i).toNat = o.toNat + 2 * i ∧
      (o + 2 * UInt64.ofNat i + 1).toNat = o.toNat + 2 * i + 1 := by
  have hi : (UInt64.ofNat i).toNat = i := ofNatN (by omega)
  have h2 : (2 * UInt64.ofNat i).toNat = 2 * i := by
    rw [UInt64.toNat_mul, hi]; simp only [UInt64.reduceToNat]; omega
  have h3 : (o + 2 * UInt64.ofNat i).toNat = o.toNat + 2 * i := by rw [addN (by omega), h2]
  exact ⟨h3, by rw [addN (by simp; omega), h3]; simp⟩

theorem TPinsR.frame {m m' : Mem} {o l : Word} {ps : List (NIdx × EIdx)} {lo hi : Nat}
    (h : TPinsR m o l ps) (hw : EW lo hi m m') (hd : o.toNat + 2 * l.toNat ≤ lo ∨ hi ≤ o.toNat) :
    TPinsR m' o l ps := by
  obtain ⟨hb, hl, hv⟩ := h
  refine ⟨Nat.le_trans hb hw.top, hl, fun i hi' => ?_⟩
  have ht := top_lt m
  obtain ⟨h0, h1⟩ := pairIdx (o := o) (i := i) (by omega)
  obtain ⟨v0, v1⟩ := hv i hi'
  rw [← v0, ← v1, rdW, rdW, rdW, rdW, h0, h1, hw.low _ (by omega) (by omega),
    hw.low _ (by omega) (by omega)]
  exact ⟨rfl, rfl⟩

/-- A type-pin slice: its first pair, then the rest. -/
theorem TPinsR.cons {m : Mem} {o o' l l' : Word} {x : NIdx × EIdx} {ps : List (NIdx × EIdx)}
    (h₁ : rdW (m.arr64 EREC) o = x.1.word.toUInt64) (h₂ : rdW (m.arr64 EREC) (o + 1) = x.2.word.toUInt64)
    (h₃ : TPinsR m o' l ps) (ho : o' = o + 2) (hl : l'.toNat = l.toNat + 1)
    (hb : o.toNat + 2 ≤ erecTop m) : TPinsR m o l' (x :: ps) := by
  obtain ⟨hb2, hl2, hv⟩ := h₃
  have ht := top_lt m
  have ho' : o'.toNat = o.toNat + 2 := by subst ho; rw [addN (by simp; omega)]; simp
  refine ⟨by omega, by simp; omega, fun i hi => ?_⟩
  cases i with
  | zero => simpa using ⟨h₁, h₂⟩
  | succ i =>
    have := hv i (by simpa using hi)
    rw [ho] at this
    simp only [List.getElem_cons_succ]
    have e : o + 2 + 2 * UInt64.ofNat i = o + 2 * UInt64.ofNat (i + 1) := by
      rw [UInt64.ofNat_add, UInt64.ofNat_one, UInt64.mul_add, UInt64.mul_one]; ac_rfl
    rw [e] at this
    exact this

/-! ## Records kept by a run that only grows the record pool -/

/-- `EREC` below `m`'s top unchanged, the top not lower. -/
def PinEKeep (m m' : Mem) : Prop :=
  erecTop m ≤ erecTop m' ∧ ∀ i, i < erecTop m → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?

theorem PinEKeep.get {m m' : Mem} (h : PinEKeep m m') {x : Word} (hx : x.toNat < erecTop m) :
    rdW (m'.arr64 EREC) x = rdW (m.arr64 EREC) x := by
  simp only [rdW, h.2 _ hx]

theorem SliceR.keep {m m' : Mem} {o l : Word} {hs : List EIdx} (h : SliceR m o l hs) (hk : PinEKeep m m') :
    SliceR m' o l hs := by
  obtain ⟨hb, hl, hv⟩ := h
  refine ⟨Nat.le_trans hb hk.1, hl, fun i hi' => ?_⟩
  have ht := top_lt m
  have hx : (o + UInt64.ofNat i).toNat = o.toNat + i := by
    rw [addN] <;> rw [ofNatN (by omega)] <;> omega
  rw [← hv i hi', hk.get (by rw [hx]; omega)]

theorem TPinsR.keep {m m' : Mem} {o l : Word} {ps : List (NIdx × EIdx)} (h : TPinsR m o l ps)
    (hk : PinEKeep m m') : TPinsR m' o l ps := by
  obtain ⟨hb, hl, hv⟩ := h
  refine ⟨Nat.le_trans hb hk.1, hl, fun i hi' => ?_⟩
  have ht := top_lt m
  obtain ⟨h0, h1⟩ := pairIdx (o := o) (i := i) (by omega)
  rw [hk.get (by rw [h0]; omega), hk.get (by rw [h1]; omega)]
  exact hv i hi'

theorem PinSetR.keep {m m' : Mem} {r : Word} {ip : INatOpPinSet} (h : PinSetR m r ip)
    (hk : PinEKeep m m') : PinSetR m' r ip := by
  obtain ⟨hb, hp, hc, htp⟩ := h
  have ht := top_lt m
  refine ⟨Nat.le_trans hb hk.1, hp.keep hk, fun j hj => ?_, fun j hj => ?_⟩
  · have := hdrIdx (r := r) (j := UInt64.ofNat j) (by omega) (by rw [ofNatN (by omega)]; exact hj)
    rw [ofNatN (by omega)] at this
    have h1 := hc j hj
    unfold HdrR at h1 ⊢
    rw [hk.get (by rw [this.1]; omega), hk.get (by rw [this.2]; omega)]
    exact h1.keep hk
  · have := thdrIdx (r := r) (j := UInt64.ofNat j) (by omega) (by rw [ofNatN (by omega)]; exact hj)
    rw [ofNatN (by omega)] at this
    have h1 := htp j hj
    unfold THdrR at h1 ⊢
    rw [hk.get (by rw [this.1]; omega), hk.get (by rw [this.2]; omega)]
    exact h1.keep hk

/-! ## The twin's runs -/

theorem run_internExpr {e : ConLeche.Expr} {m' : EMemo} {h : EIdx} {a a' : AState}
    (hr : (internExprGo (∅ : EMemo) e).run a = .ok ((m', h), a')) :
    (ConRon.Arena.internExpr e).run a = .ok (h, a') := by
  simp only [ConRon.Arena.internExpr, Frontend.internExpr]
  rw [run_bind_of _ _ _ _ _ hr]; rfl

theorem run_internExprList {es : List ConLeche.Expr} {m' : EMemo} {hs : List EIdx} {a a' : AState}
    (hr : (Frontend.internExprList (∅ : EMemo) es).run a = .ok ((m', hs), a')) :
    (ConRon.Arena.internExprList es).run a = .ok (hs, a') := by
  simp only [ConRon.Arena.internExprList]
  rw [run_bind_of _ _ _ _ _ hr]; rfl

theorem run_list_cons {m m₁ m₂ : EMemo} {e : ConLeche.Expr} {es : List ConLeche.Expr} {h : EIdx}
    {hs : List EIdx} {a a₁ a₂ : AState} (h₁ : (internExprGo m e).run a = .ok ((m₁, h), a₁))
    (h₂ : (Frontend.internExprList m₁ es).run a₁ = .ok ((m₂, hs), a₂)) :
    (Frontend.internExprList m (e :: es)).run a = .ok ((m₂, h :: hs), a₂) := by
  simp only [Frontend.internExprList]
  rw [run_bind_of _ _ _ _ _ h₁]
  show (Frontend.internExprList m₁ es >>= _).run a₁ = _
  rw [run_bind_of _ _ _ _ _ h₂]; rfl

theorem run_list_one {m m' : EMemo} {e : ConLeche.Expr} {x : EIdx} {a a' : AState}
    (h : (Frontend.internExprList m [e]).run a = .ok ((m', [x]), a')) :
    (internExprGo m e).run a = .ok ((m', x), a') := by
  cases hg : (internExprGo m e).run a with
  | error err =>
    have : (Frontend.internExprList m [e]).run a = .error err := by
      simp only [Frontend.internExprList]; rw [StateT.run_bind, hg]; rfl
    rw [this] at h; cases h
  | ok v =>
    obtain ⟨⟨m₁, x₁⟩, a₁⟩ := v
    have h2 : (Frontend.internExprList m₁ []).run a₁ = .ok ((m₁, []), a₁) := rfl
    rw [run_list_cons hg h2] at h
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq] at h
    obtain ⟨⟨rfl, rfl, -⟩, rfl⟩ := h
    rfl

theorem run_mapM_cons {α β : Type} {f : α → AM β} {x : α} {xs : List α} {y : β} {ys : List β}
    {a a₁ a₂ : AState} (h₁ : (f x).run a = .ok (y, a₁)) (h₂ : (xs.mapM f).run a₁ = .ok (ys, a₂)) :
    ((x :: xs).mapM f).run a = .ok (y :: ys, a₂) := by
  rw [List.mapM_cons, run_bind_of _ _ _ _ _ h₁, run_bind_of _ _ _ _ _ h₂]; rfl

/-- The pinned expressions of a variant, in field order. -/
def pinsE (ps : ConLeche.NatOpPinSet) : List ConLeche.Expr :=
  [ps.divPin, ps.modPin, ps.gcdPin, ps.landPin, ps.lorPin, ps.xorPin, ps.shiftLeftPin, ps.shiftRightPin]

/-- The certificate lists of a variant, in field order. -/
def certsE (ps : ConLeche.NatOpPinSet) : List (List ConLeche.Expr) :=
  [ps.divProofs, ps.modProofs, ps.gcdProofs, ps.landProofs, ps.lorProofs, ps.xorProofs,
   ps.shiftLeftProofs, ps.shiftRightProofs]

/-- The type-pin lists of a variant, in field order. -/
def tpinsE (ps : ConLeche.NatOpPinSet) : List (List (ConLeche.Name × ConLeche.Expr)) :=
  [ps.divTypePins, ps.modTypePins, ps.gcdTypePins, ps.landTypePins, ps.lorTypePins, ps.xorTypePins,
   ps.shiftLeftTypePins, ps.shiftRightTypePins]

/-- The record of eight pin handles, eight certificate lists and eight type-pin lists. -/
def mkIP (tc : String) : List EIdx → List (List EIdx) → List (List (NIdx × EIdx)) → INatOpPinSet
  | [h0, h1, h2, h3, h4, h5, h6, h7], [c0, c1, c2, c3, c4, c5, c6, c7],
    [t0, t1, t2, t3, t4, t5, t6, t7] =>
    ⟨tc, h0, h1, h2, h3, h4, h5, h6, h7, c0, c1, c2, c3, c4, c5, c6, c7, t0, t1, t2, t3, t4, t5, t6, t7⟩
  | _, _, _ => ⟨tc, decI 0, decI 0, decI 0, decI 0, decI 0, decI 0, decI 0, decI 0, [], [], [], [], [], [],
      [], [], [], [], [], [], [], [], [], []⟩

/-- **`internPinSet` is the pins, then the lists, then the type pins.** -/
theorem internPinSet_eq (ps : ConLeche.NatOpPinSet) :
    internPinSet ps = (do
      let hs ← (pinsE ps).mapM ConRon.Arena.internExpr
      let hss ← (certsE ps).mapM ConRon.Arena.internExprList
      let tss ← (tpinsE ps).mapM internTypePins
      pure (mkIP ps.toolchain hs hss tss)) := by
  simp only [internPinSet, internPinSetTypePins, pinsE, certsE, tpinsE, List.mapM_cons, List.mapM_nil,
    bind_assoc, pure_bind, mkIP]

theorem run_internTypePins_cons {x : ConLeche.Name} {e : ConLeche.Expr}
    {tps : List (ConLeche.Name × ConLeche.Expr)} {n : NIdx} {t : EIdx} {r : List (NIdx × EIdx)}
    {a a₁ a₂ a₃ : AState} (h₁ : (ConRon.Arena.internName x).run a = .ok (n, a₁))
    (h₂ : (ConRon.Arena.internExpr e).run a₁ = .ok (t, a₂)) (h₃ : (internTypePins tps).run a₂ = .ok (r, a₃)) :
    (internTypePins ((x, e) :: tps)).run a = .ok ((n, t) :: r, a₃) := by
  simp only [internTypePins]
  rw [run_bind_of _ _ _ _ _ h₁, run_bind_of _ _ _ _ _ h₂, run_bind_of _ _ _ _ _ h₃]; rfl

theorem len8 {α : Type} (l : List α) (h : l.length = 8) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7, l = [x0, x1, x2, x3, x4, x5, x6, x7] := by
  match l, h with
  | [x0, x1, x2, x3, x4, x5, x6, x7], _ => exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩

/-- A variant decoded: eight pins, eight certificate lists and eight type-pin lists, interned as
the twin's `internPinSet` of the variant made of them (any toolchain string). -/
theorem run_internPinSet {es : List ConLeche.Expr} {ess : List (List ConLeche.Expr)}
    {tss : List (List (ConLeche.Name × ConLeche.Expr))} {hs : List EIdx}
    {hss : List (List EIdx)} {hts : List (List (NIdx × EIdx))} {a a₁ a₂ a₃ : AState}
    (he : es.length = 8) (hes : ess.length = 8) (hts8 : tss.length = 8)
    (hh : hs.length = 8) (hhs : hss.length = 8) (hht : hts.length = 8)
    (h₁ : (es.mapM ConRon.Arena.internExpr).run a = .ok (hs, a₁))
    (h₂ : (ess.mapM ConRon.Arena.internExprList).run a₁ = .ok (hss, a₂))
    (h₃ : (tss.mapM internTypePins).run a₂ = .ok (hts, a₃)) :
    ∃ (ps : ConLeche.NatOpPinSet) (ip : INatOpPinSet), (internPinSet ps).run a = .ok (ip, a₃) ∧
      pinsOf ip = hs ∧ certsOf ip = hss ∧ tpinsOf ip = hts := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, rfl⟩ := len8 es he
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, rfl⟩ := len8 ess hes
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, rfl⟩ := len8 tss hts8
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, rfl⟩ := len8 hs hh
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, rfl⟩ := len8 hss hhs
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, rfl⟩ := len8 hts hht
  refine ⟨⟨"", e0, e1, e2, e3, e4, e5, e6, e7, s0, s1, s2, s3, s4, s5, s6, s7,
      u0, u1, u2, u3, u4, u5, u6, u7⟩,
    mkIP "" [h0, h1, h2, h3, h4, h5, h6, h7] [c0, c1, c2, c3, c4, c5, c6, c7]
      [t0, t1, t2, t3, t4, t5, t6, t7], ?_, rfl, rfl, rfl⟩
  rw [internPinSet_eq]
  simp only [pinsE, certsE, tpinsE]
  rw [run_bind_of _ _ _ _ _ h₁, run_bind_of _ _ _ _ _ h₂, run_bind_of _ _ _ _ _ h₃]
  rfl

theorem run_internPinSets_cons {ps : ConLeche.NatOpPinSet} {pins : List ConLeche.NatOpPinSet}
    {ip : INatOpPinSet} {ips : List INatOpPinSet} {a a₁ a₂ : AState}
    (h₁ : (internPinSet ps).run a = .ok (ip, a₁)) (h₂ : (internPinSets pins).run a₁ = .ok (ips, a₂)) :
    (internPinSets (ps :: pins)).run a = .ok (ip :: ips, a₂) := by
  simp only [internPinSets]
  rw [run_bind_of _ _ _ _ _ h₁, run_bind_of _ _ _ _ _ h₂]; rfl

/-! ## Records kept -/

/-- The record at `r`, its certificate slices and its type-pin slices are at or above `b`. -/
def LowB (b : Nat) (mem : Mem) (r : Word) : Prop :=
  b ≤ r.toNat ∧ (∀ j, j < 8 → b ≤ (rdW (mem.arr64 EREC) (r + 8 + 2 * UInt64.ofNat j)).toNat) ∧
    ∀ j, j < 8 → b ≤ (rdW (mem.arr64 EREC) (r + 24 + 2 * UInt64.ofNat j)).toNat

/-- **A record is kept by writes below it.** -/
theorem PinSetR.frame {m m' : Mem} {r : Word} {ip : INatOpPinSet} {b lo hi : Nat} (h : PinSetR m r ip)
    (hl : LowB b m r) (hw : EW lo hi m m') (hb : hi ≤ b) : PinSetR m' r ip ∧ LowB b m' r := by
  obtain ⟨ht, hp, hc, htp⟩ := h
  have htl := top_lt m
  have hix : ∀ j, j < 8 → (r + 8 + 2 * UInt64.ofNat j).toNat = r.toNat + 8 + 2 * j ∧
      (r + 9 + 2 * UInt64.ofNat j).toNat = r.toNat + 9 + 2 * j := by
    intro j hj
    have := hdrIdx (r := r) (j := UInt64.ofNat j) (by omega) (by rw [ofNatN (by omega)]; exact hj)
    rw [ofNatN (by omega)] at this; exact this
  have tix : ∀ j, j < 8 → (r + 24 + 2 * UInt64.ofNat j).toNat = r.toNat + 24 + 2 * j ∧
      (r + 25 + 2 * UInt64.ofNat j).toNat = r.toNat + 25 + 2 * j := by
    intro j hj
    have := thdrIdx (r := r) (j := UInt64.ofNat j) (by omega) (by rw [ofNatN (by omega)]; exact hj)
    rw [ofNatN (by omega)] at this; exact this
  have tk : ∀ j, j < 8 → rdW (m'.arr64 EREC) (r + 24 + 2 * UInt64.ofNat j) =
        rdW (m.arr64 EREC) (r + 24 + 2 * UInt64.ofNat j) ∧
      rdW (m'.arr64 EREC) (r + 25 + 2 * UInt64.ofNat j) = rdW (m.arr64 EREC) (r + 25 + 2 * UInt64.ofNat j) := by
    intro j hj
    have := tix j hj; have := hl.1
    exact ⟨hw.get _ (by omega) (by omega), hw.get _ (by omega) (by omega)⟩
  have hk : ∀ j, j < 8 → rdW (m'.arr64 EREC) (r + 8 + 2 * UInt64.ofNat j) =
        rdW (m.arr64 EREC) (r + 8 + 2 * UInt64.ofNat j) ∧
      rdW (m'.arr64 EREC) (r + 9 + 2 * UInt64.ofNat j) = rdW (m.arr64 EREC) (r + 9 + 2 * UInt64.ofNat j) := by
    intro j hj
    have := hix j hj; have := hl.1
    exact ⟨hw.get _ (by omega) (by omega), hw.get _ (by omega) (by omega)⟩
  refine ⟨⟨Nat.le_trans ht hw.top, hp.frame hw (by have := hl.1; omega), fun j hj => ?_, fun j hj => ?_⟩,
    hl.1, fun j hj => by rw [(hk j hj).1]; exact hl.2.1 j hj,
    fun j hj => by rw [(tk j hj).1]; exact hl.2.2 j hj⟩
  · have h1 := hc j hj
    simp only [HdrR] at h1 ⊢
    rw [(hk j hj).1, (hk j hj).2]
    exact h1.frame hw (by have := hl.2.1 j hj; omega)
  · have h1 := htp j hj
    simp only [THdrR] at h1 ⊢
    rw [(tk j hj).1, (tk j hj).2]
    exact h1.frame hw (by have := hl.2.2 j hj; omega)

/-! ## `rom_exprs_to` -/

section dec
variable (rom : List UInt8) (hr : RomOK rom)
include hr

/-- **`rom_exprs_to` in the decoder direction**: `k` expressions at the current memo, the twin's
`internExprList` on them, their handles in the slice `(o, k)`. -/
theorem exprsTo_dec : ∀ (n : Nat) (mem : Mem) (a : AState) (seen : List ConLeche.Expr) (m : EMemo)
    (q o k q' : Word) (mem' : Mem), DecInv mem a seen m → o.toNat + k.toNat ≤ erecTop mem →
    erecTop mem ≤ (mem.arr64 EREC).size → romExprsToW rom n mem q o k = some (q', mem') →
    ∃ (es : List ConLeche.Expr) (hs : List EIdx) (m' : EMemo) (a' : AState) (seen' : List ConLeche.Expr),
      (Frontend.internExprList m es).run a = .ok ((m', hs), a') ∧ es.length = k.toNat ∧
      DecInv mem' a' seen' m' ∧ SliceR mem' o k hs ∧ EW o.toNat (o.toNat + k.toNat) mem mem' ∧
      MemFrame PinsA ExprC mem mem' := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ hW; simp [romExprsToW] at hW
  | succ n ih =>
  intro mem a seen m q o k q' mem' inv hb ht hW
  have htl := top_lt mem
  by_cases hk : k = 0
  · subst hk
    rw [romExprsToW_zero] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    exact ⟨[], [], m, a, seen, rfl, rfl, inv, SliceR.nil (by simpa using hb), EW.refl _ _ _,
      MemFrame.refl _ _ _⟩
  rw [romExprsToW_succ rom n mem q o k hk] at hW
  rcases hE : romExprW rom n mem q with _ | ⟨h, q₁, m₁⟩ <;> rw [hE] at hW
  · simp [exsToK] at hW
  rw [exsToK_some] at hW
  obtain ⟨e, rest, m₂, a₁, -, -, hrun, inv₁, -, -, hlt, -, hf₁⟩ :=
    dec_child rom hr (romExprW_dec rom hr n) inv hE
  have hk1 : 1 ≤ k.toNat := by
    have : k.toNat ≠ 0 := fun h' => hk (UInt64.toNat_inj.mp (by simpa using h'))
    omega
  have hkm : (k - 1).toNat = k.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using hk1)]; simp
  have ho1 : (o + 1).toNat = o.toNat + 1 := addN (by simp; omega)
  have ht₁ := expr_top hf₁
  have hs₁ : (m₁.arr64 EREC).size = (mem.arr64 EREC).size := hf₁.2.2.1 EREC
  have inv₂ := inv₁.frameE (frame_set m₁ o h)
  have ht₂ : erecTop (m₁.set64 EREC o h) = erecTop m₁ := by
    simp only [erecTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hs₂ : ((m₁.set64 EREC o h).arr64 EREC).size = (m₁.arr64 EREC).size := Mem.size_arr64_set64 _ _ _ _
  obtain ⟨es, hs, m', a', seen', hrun₂, hlen, inv', hsl, hew, hfr⟩ :=
    ih _ a₁ _ m₂ q₁ (o + 1) (k - 1) q' mem' inv₂ (by omega) (by omega) hW
  have h0 : rdW (mem'.arr64 EREC) o = (decI h : EIdx).word.toUInt64 := by
    rw [rdW, hew.low _ (by omega) (by omega), ← rdW, rdW_setE _ _ _ (by omega)]
    exact ((word_decI _ h hlt).mpr rfl).symm
  refine ⟨e :: es, decI h :: hs, m', a', seen', run_list_cons hrun hrun₂, by simp; omega, inv',
    SliceR.cons h0 hsl rfl (by omega) (by have := hsl.1; omega), ?_, ?_⟩
  · exact ((EW.expr _ _ hf₁).trans (EW.set m₁ o h) (by omega)).trans hew (by omega)
  · exact ((hf₁.mono (fun b hb => by simp [PinsA, hb]) (fun _ h => h)).trans
      ((MemFrame.set64 m₁ EREC (by decide) o h).mono (by simp [PinsA]) (by simp))).trans hfr

/-- **`rom_pins_to` in the decoder direction**: pins `k ‥ 7`, each a reset and one expression,
the twin's `internExpr` on each, their handles at `r + k ‥ r + 7`. -/
theorem pinsTo_dec : ∀ (n : Nat) (mem : Mem) (a : AState) (q r k q' : Word) (mem' : Mem),
    SInv mem a → k.toNat ≤ 8 → r.toNat + 8 ≤ erecTop mem →
    romPinsToW rom n mem q r k = some (q', mem') →
    ∃ (es : List ConLeche.Expr) (hs : List EIdx) (a' : AState),
      (es.mapM ConRon.Arena.internExpr).run a = .ok (hs, a') ∧ es.length = 8 - k.toNat ∧
      SInv mem' a' ∧ SliceR mem' (r + k) (8 - k) hs ∧ EW (r.toNat + k.toNat) (r.toNat + 8) mem mem' ∧
      MemFrame PinsA PinsC mem mem' := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ hW; simp [romPinsToW] at hW
  | succ n ih =>
  intro mem a q r k q' mem' inv hk hb hW
  have htl := top_lt mem
  by_cases h8 : k = 8
  · subst h8
    rw [romPinsToW_end] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    have : (8 : Word) - 8 = 0 := by decide
    rw [this]
    exact ⟨[], [], a, rfl, by simp, inv, SliceR.nil (by rw [addN (by simp; omega)]; simp; omega),
      EW.refl _ _ _, MemFrame.refl _ _ _⟩
  by_cases hc' : ¬ rclearOK mem
  · simp [romPinsToW, h8, hc'] at hW
  have hc : rclearOK mem := Decidable.not_not.mp hc'
  rw [romPinsToW_step rom n mem q k r h8 hc] at hW
  rcases hX : romExprsToW rom n (resetMem mem) q (r + k) 1 with _ | ⟨q₁, m₁⟩ <;> rw [hX] at hW
  · simp [pinsK] at hW
  rw [pinsK_some] at hW
  have hk8 : k.toNat < 8 := by
    have : k.toNat ≠ 8 := fun h' => h8 (UInt64.toNat_inj.mp (by simpa using h'))
    omega
  have hrk : (r + k).toNat = r.toNat + k.toNat := addN (by omega)
  obtain ⟨es₁, hs₁, mm, a₁, seen₁, hrun₁, hlen₁, inv₁, hsl₁, hew₁, hfr₁⟩ :=
    exprsTo_dec rom hr n _ a [] ∅ q (r + k) 1 q₁ m₁ (inv.reset hc)
      (by rw [resetMem_top]; simp; omega) (by rw [resetMem_top, resetMem_size]; exact inv.top) hX
  obtain ⟨e, rfl⟩ : ∃ e, es₁ = [e] := by
    match es₁, hlen₁ with
    | [e], _ => exact ⟨e, rfl⟩
  have hl₁ := hsl₁.2.1
  obtain ⟨x, rfl⟩ : ∃ x, hs₁ = [x] := by
    match hs₁, hl₁ with
    | [x], _ => exact ⟨x, rfl⟩
  have hrunE := run_internExpr (run_list_one hrun₁)
  have hfm : MemFrame PinsA ExprC mem m₁ :=
    ((resetMem_frame mem).mono (fun b hb => by simp [PinsA, hb]) (fun _ h => h)).trans hfr₁
  have inv₁' : SInv m₁ a₁ := inv.of_dec inv₁ hfm
  have htop₁ : erecTop m₁ = erecTop mem := by
    simp only [erecTop]; rw [hfm.2.1 129 (by decide)]
  obtain ⟨es, hs, a', hrun₂, hlen, inv', hsl, hew, hfr⟩ :=
    ih m₁ a₁ q₁ r (k + 1) q' mem' inv₁' (by rw [succN hk8]; omega) (by omega) hW
  have h0 : rdW (mem'.arr64 EREC) (r + k) = x.word.toUInt64 := by
    rw [hew.get _ (by omega) (by rw [succN hk8]; omega)]
    have := hsl₁.2.2 0 (by simp)
    simpa using this
  have h8k : (8 - k).toNat = (8 - (k + 1)).toNat + 1 := by
    rw [sub8 (by omega), sub8 (by rw [succN hk8]; omega), succN hk8]; omega
  refine ⟨e :: es, x :: hs, a', run_mapM_cons hrunE hrun₂, by simp [hlen, succN hk8]; omega, inv',
    SliceR.cons h0 hsl (by rw [UInt64.add_assoc]) h8k (by have := hsl.1; have := hew.top; omega), ?_, ?_⟩
  · exact ((resetMem_EW _ _ mem).trans hew₁ (by simp; omega)).trans hew (by rw [succN hk8]; omega)
  · exact ((frame_pins_reset mem).trans
      (hfr₁.mono (fun _ h => h) (fun x hx => by simp [PinsC, hx]))).trans hfr

/-- **`rom_lists_to` in the decoder direction**: certificate lists `j ‥ 7`, each a fresh slice,
a reset and the list's expressions at one memo (the twin's `internExprList`); list `j + i`'s
header at `r + 8 + 2 (j + i)`, its slice above the old top. -/
theorem listsTo_dec : ∀ (n : Nat) (mem : Mem) (a : AState) (q r j q' : Word) (mem' : Mem),
    SInv mem a → j.toNat ≤ 8 → r.toNat + 24 ≤ erecTop mem →
    romListsToW rom n mem q r j = some (q', mem') →
    ∃ (ess : List (List ConLeche.Expr)) (hss : List (List EIdx)) (a' : AState),
      (ess.mapM ConRon.Arena.internExprList).run a = .ok (hss, a') ∧ ess.length = 8 - j.toNat ∧
      hss.length = 8 - j.toNat ∧ SInv mem' a' ∧
      (∀ i (hi : i < hss.length), HdrR mem' r (j.toNat + i) hss[i] ∧
        erecTop mem ≤ (rdW (mem'.arr64 EREC) (r + 8 + 2 * UInt64.ofNat (j.toNat + i))).toNat) ∧
      EW (r.toNat + 8 + 2 * j.toNat) (r.toNat + 24) mem mem' ∧ MemFrame PinsA PinsC mem mem' := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ hW; simp [romListsToW] at hW
  | succ n ih =>
  intro mem a q r j q' mem' inv hj hb hW
  have htl := top_lt mem
  by_cases h8 : j = 8
  · subst h8
    rw [romListsToW_end] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    exact ⟨[], [], a, rfl, by simp, by simp, inv, fun i hi => by simp at hi, EW.refl _ _ _,
      MemFrame.refl _ _ _⟩
  by_cases hu : ¬ u64OK rom q
  · simp [romListsToW, h8, hu] at hW
  have hu' : u64OK rom q := Decidable.not_not.mp hu
  rw [romListsToW_step rom n mem q r j h8 hu'] at hW
  have hj8 : j.toNat < 8 := by
    have : j.toNat ≠ 8 := fun h' => h8 (UInt64.toNat_inj.mp (by simpa using h'))
    omega
  rcases hA : erAllocW mem (u64W rom q) with _ | ⟨o, m₁⟩ <;> rw [hA] at hW
  · simp [listsK] at hW
  generalize hl : u64W rom q = l at hA hW
  obtain ⟨ho, ht₁, hroom, hf₁, hew₁⟩ := erAlloc_ok hA inv.ctl
  obtain ⟨hi8, hi9⟩ := hdrIdx (r := r) (j := j) (by omega) hj8
  have hs₁ : (m₁.arr64 EREC).size = (mem.arr64 EREC).size := hf₁.2.2.1 EREC
  have inv₁ : SInv m₁ a := inv.frameE (hf₁.mono (by simp) (by simp)) (by omega)
  -- the header
  generalize hmA : m₁.set64 EREC (r + 8 + 2 * j) o = mA
  generalize hmh : mA.set64 EREC (r + 9 + 2 * j) l = mh
  have hlh : listHdr m₁ r j o l = mh := by rw [← hmh, ← hmA]; rfl
  have hcA : mA.arr64 CTL = m₁.arr64 CTL := by rw [← hmA, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hch : mh.arr64 CTL = mA.arr64 CTL := by rw [← hmh, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hsA : (mA.arr64 EREC).size = (m₁.arr64 EREC).size := by rw [← hmA, Mem.size_arr64_set64]
  have hsh : (mh.arr64 EREC).size = (mA.arr64 EREC).size := by rw [← hmh, Mem.size_arr64_set64]
  have htA : erecTop mA = erecTop m₁ := by simp only [erecTop, hcA]
  have hth : erecTop mh = erecTop mA := by simp only [erecTop, hch]
  have invA : SInv mA a := inv₁.frameE (by rw [← hmA]; exact frame_set _ _ _) (by omega)
  have invh : SInv mh a := invA.frameE (by rw [← hmh]; exact frame_set _ _ _) (by omega)
  have ewA : EW (r.toNat + 8 + 2 * j.toNat) (r.toNat + 8 + 2 * j.toNat + 1) m₁ mA := by
    rw [← hmA, ← hi8]; exact EW.set _ _ _
  have ewh : EW (r.toNat + 9 + 2 * j.toNat) (r.toNat + 9 + 2 * j.toNat + 1) mA mh := by
    rw [← hmh, ← hi9]; exact EW.set _ _ _
  simp only [listsK, hlh] at hW
  by_cases hc' : ¬ rclearOK mh
  · simp [hc'] at hW
  have hc : rclearOK mh := Decidable.not_not.mp hc'
  simp only [ite_eq_left hc] at hW
  rcases hX : romExprsToW rom n (resetMem mh) (q + 8) o l with _ | ⟨q₁, m₂⟩ <;> rw [hX] at hW
  · simp [lists2K] at hW
  rw [lists2K_some] at hW
  obtain ⟨es, hs, mm, a₁, seen₁, hrun₁, hlen₁, inv₂, hsl₂, hew₂, hfr₂⟩ :=
    exprsTo_dec rom hr n _ a [] ∅ (q + 8) o l q₁ m₂ (invh.reset hc)
      (by rw [resetMem_top]; omega) (by rw [resetMem_top, resetMem_size]; exact invh.top) hX
  have hfm : MemFrame PinsA ExprC mh m₂ :=
    ((resetMem_frame mh).mono (fun b hb => by simp [PinsA, hb]) (fun _ h => h)).trans hfr₂
  have inv₂' : SInv m₂ a₁ := invh.of_dec inv₂ hfm
  have ht₂ : erecTop m₂ = erecTop mh := by simp only [erecTop]; rw [hfm.2.1 129 (by decide)]
  obtain ⟨ess, hss, a', hrun₂, hl1, hl2, inv', hall, hew', hfr'⟩ :=
    ih m₂ a₁ q₁ r (j + 1) q' mem' inv₂' (by rw [succN hj8]; omega) (by omega) hW
  rw [succN hj8] at hl1 hl2 hew'
  -- the header words, kept to the end
  have hEh : EW 0 0 mh (resetMem mh) := resetMem_EW 0 0 mh
  have hkeep : ∀ x : Word, x.toNat < erecTop mh → x.toNat < o.toNat →
      x.toNat < r.toNat + 8 + 2 * (j.toNat + 1) → rdW (mem'.arr64 EREC) x = rdW (mh.arr64 EREC) x := by
    intro x hx hxo hxr
    rw [hew'.get _ (by have := hew₂.top; rw [resetMem_top] at this; omega) (by omega),
      hew₂.get _ (by rw [resetMem_top]; omega) (by omega), hEh.get _ hx (by omega)]
  have hv8 : rdW (mem'.arr64 EREC) (r + 8 + 2 * j) = o := by
    rw [hkeep _ (by omega) (by omega) (by omega), ← hmh, rdW_set64, ite_eq_right (by
      intro ⟨_, h', _⟩; have := congrArg UInt64.toNat h'; omega), ← hmA, rdW_setE _ _ _ (by omega)]
  have hv9 : rdW (mem'.arr64 EREC) (r + 9 + 2 * j) = l := by
    rw [hkeep _ (by omega) (by omega) (by omega), ← hmh, rdW_setE _ _ _ (by omega)]
  have hsl' : SliceR mem' o l hs := by
    have := hsl₂.frame hew' (by omega)
    exact this
  refine ⟨es :: ess, hs :: hss, a', run_mapM_cons (run_internExprList hrun₁) hrun₂, by simp; omega,
    by simp; omega, inv', fun i hi => ?_, ?_, ?_⟩
  · cases i with
    | zero =>
      simp only [HdrR, Nat.add_zero, UInt64.ofNat_toNat, List.getElem_cons_zero, hv8, hv9]
      exact ⟨hsl', by omega⟩
    | succ i =>
      have := hall i (by simpa using hi)
      rw [succN hj8, show j.toNat + 1 + i = j.toNat + (i + 1) by omega] at this
      simp only [List.getElem_cons_succ]
      exact ⟨this.1, by have := hew₂.top; rw [resetMem_top] at this; omega⟩
  · have e1 := ((hew₁ (r.toNat + 8 + 2 * j.toNat) (r.toNat + 24)).trans ewA (by omega)).trans ewh
      (by omega)
    have e2 : EW o.toNat (o.toNat + l.toNat) mh m₂ :=
      (resetMem_EW _ _ mh).trans hew₂ (fun _ _ h => h)
    exact (e1.trans e2 (by omega)).trans hew' (by omega)
  · have fA : MemFrame PinsA PinsC m₁ mA := by rw [← hmA]; exact frame_pins_set _ _ _
    have fh : MemFrame PinsA PinsC mA mh := by rw [← hmh]; exact frame_pins_set _ _ _
    exact (((((hf₁.mono (by simp) (by simp [PinsC])).trans fA).trans fh).trans
      (frame_pins_reset mh)).trans (hfr₂.mono (fun _ h => h) (fun x hx => by simp [PinsC, hx]))).trans hfr'

/-- **`rom_tpairs_to` in the decoder direction**: `k` type pins, each a name (`internName`), then a
reset and one expression (`internExpr`), the twin's `internTypePins` on them, their handles in the
pair slice `(o, k)`. -/
theorem tpairsTo_dec : ∀ (n : Nat) (mem : Mem) (a : AState) (q o k q' : Word) (mem' : Mem),
    SInv mem a → o.toNat + 2 * k.toNat ≤ erecTop mem → romTPairsToW rom n mem q o k = some (q', mem') →
    ∃ (tps : List (ConLeche.Name × ConLeche.Expr)) (hs : List (NIdx × EIdx)) (a' : AState),
      (internTypePins tps).run a = .ok (hs, a') ∧ tps.length = k.toNat ∧ SInv mem' a' ∧
      TPinsR mem' o k hs ∧ EW o.toNat (o.toNat + 2 * k.toNat) mem mem' ∧
      MemFrame PinsA PinsC mem mem' := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ hW; simp [romTPairsToW] at hW
  | succ n ih =>
  intro mem a q o k q' mem' inv hb hW
  have htl := top_lt mem
  by_cases hk : k = 0
  · subst hk
    rw [romTPairsToW_zero] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    exact ⟨[], [], a, rfl, rfl, inv, TPinsR.nil (by simpa using hb), EW.refl _ _ _, MemFrame.refl _ _ _⟩
  rw [romTPairsToW_succ rom n mem q o k hk] at hW
  have hk1 : 1 ≤ k.toNat := by
    have : k.toNat ≠ 0 := fun h' => hk (UInt64.toNat_inj.mp (by simpa using h'))
    omega
  have hkm : (k - 1).toNat = k.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using hk1)]; simp
  have ho1 : (o + 1).toNat = o.toNat + 1 := addN (by simp; omega)
  have ho2 : (o + 2).toNat = o.toNat + 2 := addN (by simp; omega)
  -- the name
  rcases hN : romNameW rom n mem q with _ | ⟨h, q₁, m₁⟩ <;> rw [hN] at hW
  · simp [tpK] at hW
  obtain ⟨x, rest, hd, fit, -⟩ := romNameW_dec rom hr n mem q h q₁ m₁ hN
  obtain ⟨ok1, hR1, hres1, hlt1, -, hf1⟩ :=
    romNameW_ok rom hr x fit n mem a q rest h q₁ m₁ inv.arena inv.mode hd hN
  have hrunN : (ConRon.Arena.internName x).run a = .ok (decI h, AM.st (ConRon.Arena.internName x) a) := by
    rw [← hres1]; exact AM.run_of_ok _ _ ok1
  have hstN := (ConRon.Bridge.Frontend.internName_sstep inv.ok hrunN).1
  have hfE := frame_storeE hf1
  have ht₁ := expr_top hfE
  have hs₁ : (m₁.arr64 EREC).size = (mem.arr64 EREC).size := hfE.2.2.1 EREC
  have inv₁ : SInv m₁ (AM.st (ConRon.Arena.internName x) a) :=
    ⟨hR1, inv.rset.frameS hf1, hstN.ok, by rw [frame_exprA_stk hf1]; exact inv.stk,
      by rw [hf1.2.2.1 CTL]; exact inv.ctl, by rw [ht₁, hs₁]; exact inv.top,
      (romNameW_topK hN).mode inv.arena.1.lit.1 inv.mode⟩
  -- its handle
  by_cases hc' : ¬ rclearOK (m₁.set64 EREC o h)
  · simp [tpK, hc'] at hW
  have hc₀ : rclearOK (m₁.set64 EREC o h) := Decidable.not_not.mp hc'
  rw [tpK_some (hc := hc₀)] at hW
  generalize hmA : m₁.set64 EREC o h = mA at hW hc₀
  have hc : rclearOK mA := hc₀
  have htA : erecTop mA = erecTop m₁ := by
    rw [← hmA]; simp only [erecTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hsA : (mA.arr64 EREC).size = (m₁.arr64 EREC).size := by rw [← hmA, Mem.size_arr64_set64]
  have invA : SInv mA (AM.st (ConRon.Arena.internName x) a) :=
    inv₁.frameE (by rw [← hmA]; exact frame_set _ _ _) (by have := inv₁.top; omega)
  -- the type
  rcases hX : romExprsToW rom n (resetMem mA) q₁ (o + 1) 1 with _ | ⟨q₂, m₂⟩ <;> rw [hX] at hW
  · simp [tp2K] at hW
  rw [tp2K_some] at hW
  obtain ⟨es₁, hs₁', mm, a₁, seen₁, hrun₁, hlen₁, inv₂, hsl₂, hew₂, hfr₂⟩ :=
    exprsTo_dec rom hr n _ _ [] ∅ q₁ (o + 1) 1 q₂ m₂ (invA.reset hc)
      (by rw [resetMem_top]; simp; omega) (by rw [resetMem_top, resetMem_size]; exact invA.top) hX
  simp only [show (1 : Word).toNat = 1 from rfl, ho1] at hew₂
  obtain ⟨e, rfl⟩ : ∃ e, es₁ = [e] := by
    match es₁, hlen₁ with
    | [e], _ => exact ⟨e, rfl⟩
  have hl₂ := hsl₂.2.1
  obtain ⟨y, rfl⟩ : ∃ y, hs₁' = [y] := by
    match hs₁', hl₂ with
    | [y], _ => exact ⟨y, rfl⟩
  have hrunE := run_internExpr (run_list_one hrun₁)
  have hfm : MemFrame PinsA ExprC mA m₂ :=
    ((resetMem_frame mA).mono (fun b hb => by simp [PinsA, hb]) (fun _ h => h)).trans hfr₂
  have inv₂' : SInv m₂ a₁ := invA.of_dec inv₂ hfm
  have ht₂ : erecTop m₂ = erecTop mA := by simp only [erecTop]; rw [hfm.2.1 129 (by decide)]
  -- the rest
  obtain ⟨tps, hs, a', hrun₃, hlen, inv', htp, hew, hfr⟩ :=
    ih m₂ a₁ q₂ (o + 2) (k - 1) q' mem' inv₂' (by rw [ho2, hkm]; omega) hW
  rw [ho2, hkm] at hew
  have hsz0 := inv.top
  have h0 : rdW (mem'.arr64 EREC) o = (decI h : NIdx).word.toUInt64 := by
    rw [hew.get _ (by omega) (by omega), hew₂.get _ (by rw [resetMem_top]; omega) (by omega),
      (resetMem_EW 0 0 mA).get _ (by omega) (by omega), ← hmA, rdW_setE _ _ _ (by omega)]
    exact ((word_decI _ h hlt1).mpr rfl).symm
  have h1 : rdW (mem'.arr64 EREC) (o + 1) = y.word.toUInt64 := by
    rw [hew.get _ (by have := hew₂.top; rw [resetMem_top] at this; omega) (by omega)]
    have := hsl₂.2.2 0 (by simp)
    simpa using this
  refine ⟨(x, e) :: tps, (decI h, y) :: hs, a', run_internTypePins_cons hrunN hrunE hrun₃,
    by simp [hlen]; omega, inv', TPinsR.cons h0 h1 htp rfl (by rw [hkm]; omega)
      (by have := htp.1; have := hew.top; omega), ?_, ?_⟩
  · have eA : EW o.toNat (o.toNat + 1) m₁ mA := by rw [← hmA]; exact EW.set m₁ o h
    exact (((((EW.expr o.toNat (o.toNat + 2 * k.toNat) hfE).trans eA (by omega)).trans
      (resetMem_EW (o.toNat + 1) (o.toNat + 2) mA) (by omega)).trans hew₂ (by omega)).trans hew
      (by omega))
  · exact (((frame_pins_expr hfE).trans (by rw [← hmA]; exact frame_pins_set _ _ _)).trans
      ((frame_pins_reset mA).trans (hfr₂.mono (fun _ h => h) (fun x hx => by simp [PinsC, hx])))).trans hfr

/-- **`rom_tpins_to` in the decoder direction**: type-pin lists `j ‥ 7`, each a fresh pair slice and
the twin's `internTypePins`; list `j + i`'s header at `r + 24 + 2 (j + i)`, its slice above the
old top. -/
theorem tpinsTo_dec : ∀ (n : Nat) (mem : Mem) (a : AState) (q r j q' : Word) (mem' : Mem),
    SInv mem a → j.toNat ≤ 8 → r.toNat + 40 ≤ erecTop mem →
    romTPinsToW rom n mem q r j = some (q', mem') →
    ∃ (tss : List (List (ConLeche.Name × ConLeche.Expr))) (hts : List (List (NIdx × EIdx))) (a' : AState),
      (tss.mapM internTypePins).run a = .ok (hts, a') ∧ tss.length = 8 - j.toNat ∧
      hts.length = 8 - j.toNat ∧ SInv mem' a' ∧
      (∀ i (hi : i < hts.length), THdrR mem' r (j.toNat + i) hts[i] ∧
        erecTop mem ≤ (rdW (mem'.arr64 EREC) (r + 24 + 2 * UInt64.ofNat (j.toNat + i))).toNat) ∧
      EW (r.toNat + 24 + 2 * j.toNat) (r.toNat + 40) mem mem' ∧ MemFrame PinsA PinsC mem mem' := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ hW; simp [romTPinsToW] at hW
  | succ n ih =>
  intro mem a q r j q' mem' inv hj hb hW
  have htl := top_lt mem
  by_cases h8 : j = 8
  · subst h8
    rw [romTPinsToW_end] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    exact ⟨[], [], a, rfl, by simp, by simp, inv, fun i hi => by simp at hi, EW.refl _ _ _,
      MemFrame.refl _ _ _⟩
  by_cases hu : ¬ u64OK rom q
  · simp [romTPinsToW, h8, hu] at hW
  have hu' : u64OK rom q := Decidable.not_not.mp hu
  by_cases hbig : 4294967296 ≤ u64W rom q
  · simp [romTPinsToW, h8, hu', hbig] at hW
  rw [romTPinsToW_step rom n mem q r j h8 hu' hbig] at hW
  have hj8 : j.toNat < 8 := by
    have : j.toNat ≠ 8 := fun h' => h8 (UInt64.toNat_inj.mp (by simpa using h'))
    omega
  generalize hl : u64W rom q = l at hW hbig
  have hlt : l.toNat < 4294967296 := by
    have : ¬ (4294967296 : Word).toNat ≤ l.toNat := fun h' => hbig (UInt64.le_iff_toNat_le.mpr h')
    simpa using this
  have h2l : (2 * l).toNat = 2 * l.toNat := by
    rw [UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
  rcases hA : erAllocW mem (2 * l) with _ | ⟨o, m₁⟩ <;> rw [hA] at hW
  · simp [tpinsK] at hW
  obtain ⟨ho, ht₁, hroom, hf₁, hew₁⟩ := erAlloc_ok hA inv.ctl
  rw [h2l] at ht₁ hroom
  obtain ⟨hi8, hi9⟩ := thdrIdx (r := r) (j := j) (by omega) hj8
  have hs₁ : (m₁.arr64 EREC).size = (mem.arr64 EREC).size := hf₁.2.2.1 EREC
  have inv₁ : SInv m₁ a := inv.frameE (hf₁.mono (by simp) (by simp)) (by omega)
  -- the header
  generalize hmA : m₁.set64 EREC (r + 24 + 2 * j) o = mA
  generalize hmh : mA.set64 EREC (r + 25 + 2 * j) l = mh
  have hlh : tpinsHdr m₁ r j o l = mh := by rw [← hmh, ← hmA]; rfl
  have hcA : mA.arr64 CTL = m₁.arr64 CTL := by rw [← hmA, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hch : mh.arr64 CTL = mA.arr64 CTL := by rw [← hmh, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hsA : (mA.arr64 EREC).size = (m₁.arr64 EREC).size := by rw [← hmA, Mem.size_arr64_set64]
  have hsh : (mh.arr64 EREC).size = (mA.arr64 EREC).size := by rw [← hmh, Mem.size_arr64_set64]
  have htA : erecTop mA = erecTop m₁ := by simp only [erecTop, hcA]
  have hth : erecTop mh = erecTop mA := by simp only [erecTop, hch]
  have invA : SInv mA a := inv₁.frameE (by rw [← hmA]; exact frame_set _ _ _) (by omega)
  have invh : SInv mh a := invA.frameE (by rw [← hmh]; exact frame_set _ _ _) (by omega)
  have ewA : EW (r.toNat + 24 + 2 * j.toNat) (r.toNat + 24 + 2 * j.toNat + 1) m₁ mA := by
    rw [← hmA, ← hi8]; exact EW.set _ _ _
  have ewh : EW (r.toNat + 25 + 2 * j.toNat) (r.toNat + 25 + 2 * j.toNat + 1) mA mh := by
    rw [← hmh, ← hi9]; exact EW.set _ _ _
  rw [tpinsK_some, hlh] at hW
  rcases hX : romTPairsToW rom n mh (q + 8) o l with _ | ⟨q₁, m₂⟩ <;> rw [hX] at hW
  · simp [tpins2K] at hW
  rw [tpins2K_some] at hW
  obtain ⟨tps, hs, a₁, hrun₁, hlen₁, inv₂, htp₂, hew₂, hfr₂⟩ :=
    tpairsTo_dec rom hr n mh a (q + 8) o l q₁ m₂ invh (by omega) hX
  have ht₂ := hew₂.top
  obtain ⟨tss, hts, a', hrun₂, hl1, hl2, inv', hall, hew', hfr'⟩ :=
    ih m₂ a₁ q₁ r (j + 1) q' mem' inv₂ (by rw [succN hj8]; omega) (by omega) hW
  rw [succN hj8] at hl1 hl2 hew'
  -- the header words, kept to the end
  have hkeep : ∀ x : Word, x.toNat < erecTop mh → x.toNat < o.toNat →
      x.toNat < r.toNat + 24 + 2 * (j.toNat + 1) → rdW (mem'.arr64 EREC) x = rdW (mh.arr64 EREC) x := by
    intro x hx hxo hxr
    rw [hew'.get _ (by have := hew₂.top; omega) (by omega), hew₂.get _ hx (by omega)]
  have hv8 : rdW (mem'.arr64 EREC) (r + 24 + 2 * j) = o := by
    rw [hkeep _ (by omega) (by omega) (by omega), ← hmh, rdW_set64, ite_eq_right (by
      intro ⟨_, h', _⟩; have := congrArg UInt64.toNat h'; omega), ← hmA, rdW_setE _ _ _ (by omega)]
  have hv9 : rdW (mem'.arr64 EREC) (r + 25 + 2 * j) = l := by
    rw [hkeep _ (by omega) (by omega) (by omega), ← hmh, rdW_setE _ _ _ (by omega)]
  have htp' : TPinsR mem' o l hs := htp₂.frame hew' (by omega)
  refine ⟨tps :: tss, hs :: hts, a', run_mapM_cons hrun₁ hrun₂, by simp; omega,
    by simp; omega, inv', fun i hi => ?_, ?_, ?_⟩
  · cases i with
    | zero =>
      simp only [THdrR, Nat.add_zero, UInt64.ofNat_toNat, List.getElem_cons_zero, hv8, hv9]
      exact ⟨htp', by omega⟩
    | succ i =>
      have := hall i (by simpa using hi)
      rw [succN hj8, show j.toNat + 1 + i = j.toNat + (i + 1) by omega] at this
      simp only [List.getElem_cons_succ]
      exact ⟨this.1, by have := hew₂.top; omega⟩
  · have e1 := ((hew₁ (r.toNat + 24 + 2 * j.toNat) (r.toNat + 40)).trans ewA (by omega)).trans ewh
      (by omega)
    exact (e1.trans hew₂ (by omega)).trans hew' (by omega)
  · have fA : MemFrame PinsA PinsC m₁ mA := by rw [← hmA]; exact frame_pins_set _ _ _
    have fh : MemFrame PinsA PinsC mA mh := by rw [← hmh]; exact frame_pins_set _ _ _
    exact ((((hf₁.mono (by simp) (by simp [PinsC])).trans fA).trans fh).trans hfr₂).trans hfr'

/-- **`rom_sets_to` in the decoder direction**: `k` variants, the twin's `internPinSets` on them,
record `i`'s pointer at `o + i`, every record above the old top. -/
theorem setsTo_dec : ∀ (n : Nat) (mem : Mem) (a : AState) (q o k q' : Word) (mem' : Mem),
    SInv mem a → o.toNat + k.toNat ≤ erecTop mem → romSetsToW rom n mem q o k = some (q', mem') →
    ∃ (pins : List ConLeche.NatOpPinSet) (ips : List INatOpPinSet) (a' : AState),
      (internPinSets pins).run a = .ok (ips, a') ∧ ips.length = k.toNat ∧ SInv mem' a' ∧
      (∀ i (hi : i < ips.length), PinSetR mem' (rdW (mem'.arr64 EREC) (o + UInt64.ofNat i)) ips[i] ∧
        LowB (erecTop mem) mem' (rdW (mem'.arr64 EREC) (o + UInt64.ofNat i))) ∧
      EW o.toNat (o.toNat + k.toNat) mem mem' ∧ MemFrame PinsA PinsC mem mem' := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ hW; simp [romSetsToW] at hW
  | succ n ih =>
  intro mem a q o k q' mem' inv hb hW
  have htl := top_lt mem
  by_cases hk : k = 0
  · subst hk
    rw [romSetsToW_zero] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    exact ⟨[], [], a, rfl, by simp, inv, fun i hi => by simp at hi, EW.refl _ _ _, MemFrame.refl _ _ _⟩
  rw [romSetsToW_succ rom n mem q o k hk] at hW
  have hk1 : 1 ≤ k.toNat := by
    have : k.toNat ≠ 0 := fun h' => hk (UInt64.toNat_inj.mp (by simpa using h'))
    omega
  have hkm : (k - 1).toNat = k.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using hk1)]; simp
  have ho1 : (o + 1).toNat = o.toNat + 1 := addN (by simp; omega)
  rcases hA : erAllocW mem 40 with _ | ⟨r, m₁⟩ <;> rw [hA] at hW
  · simp [setsK] at hW
  rw [setsK_some] at hW
  obtain ⟨hr₀, ht₁, hroom, hf₁, hew₁⟩ := erAlloc_ok hA inv.ctl
  have hs₁ : (m₁.arr64 EREC).size = (mem.arr64 EREC).size := hf₁.2.2.1 EREC
  have h24 : (40 : Word).toNat = 40 := rfl
  have inv₁ : SInv m₁ a := inv.frameE (hf₁.mono (by simp) (by simp)) (by omega)
  rcases hP : romPinsToW rom n m₁ q r 0 with _ | ⟨q₁, m₂⟩ <;> rw [hP] at hW
  · simp [sets2K] at hW
  rw [sets2K_some] at hW
  obtain ⟨es, hs, a₁, hrunP, hlenE, inv₂, hslP, ewP, frP⟩ :=
    pinsTo_dec rom hr n m₁ a q r 0 q₁ m₂ inv₁ (by decide) (by omega) hP
  rcases hL : romListsToW rom n m₂ q₁ r 0 with _ | ⟨q₂, m₃₀⟩ <;> rw [hL] at hW
  · simp [sets3K] at hW
  rw [sets3K_some] at hW
  obtain ⟨ess, hss, a₂, hrunL, hl1, hl2, inv₃₀, hallL, ewL, frL⟩ :=
    listsTo_dec rom hr n m₂ a₁ q₁ r 0 q₂ m₃₀ inv₂ (by decide) (by have := ewP.top; omega) hL
  rcases hT : romTPinsToW rom n m₃₀ q₂ r 0 with _ | ⟨q₃, m₃⟩ <;> rw [hT] at hW
  · simp [sets4K] at hW
  rw [sets4K_some] at hW
  obtain ⟨tss, hts, a₃, hrunT, ht1, ht2, inv₃, hallT, ewT, frT⟩ :=
    tpinsTo_dec rom hr n m₃₀ a₂ q₂ r 0 q₃ m₃ inv₃₀ (by decide)
      (by have := ewP.top; have := ewL.top; omega) hT
  simp only [UInt64.add_zero, show (8 : Word) - 0 = 8 from rfl, show (0 : Word).toNat = 0 from rfl,
    Nat.add_zero, Nat.mul_zero, Nat.sub_zero, Nat.zero_add] at hslP ewP hlenE hl1 hl2 ewL hallL
  simp only [show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero, Nat.sub_zero,
    Nat.zero_add] at ht1 ht2 ewT hallT
  have hh8 : hs.length = 8 := hslP.2.1.symm
  obtain ⟨ps, ip, hrunV, hpins, hcerts, htpins⟩ :=
    run_internPinSet hlenE hl1 ht1 hh8 hl2 ht2 hrunP hrunL hrunT
  have htop₂ := ewP.top
  have htop₃₀ := ewL.top
  have htop₃ := ewT.top
  have hrec : PinSetR m₃ r ip ∧ LowB (erecTop mem) m₃ r := by
    have htl₁ := top_lt m₁
    have hkL : ∀ j, j < 8 → rdW (m₃.arr64 EREC) (r + 8 + 2 * UInt64.ofNat j) =
          rdW (m₃₀.arr64 EREC) (r + 8 + 2 * UInt64.ofNat j) ∧
        rdW (m₃.arr64 EREC) (r + 9 + 2 * UInt64.ofNat j) = rdW (m₃₀.arr64 EREC) (r + 9 + 2 * UInt64.ofNat j) := by
      intro j hj
      have := hdrIdx (r := r) (j := UInt64.ofNat j) (by omega) (by rw [ofNatN (by omega)]; exact hj)
      rw [ofNatN (by omega)] at this
      exact ⟨ewT.get _ (by omega) (by omega), ewT.get _ (by omega) (by omega)⟩
    refine ⟨⟨by omega, by rw [hpins]; exact (hslP.frame ewL (by simp)).frame ewT (by first | (simp; done) | (simp; omega)),
      fun j hj => ?_, fun j hj => ?_⟩, by omega, fun j hj => ?_, fun j hj => ?_⟩
    · have := (hallL j (by rw [← hcerts, certsOf_length]; exact hj))
      simp only [hcerts]
      simp only [HdrR] at this ⊢
      rw [(hkL j hj).1, (hkL j hj).2]
      exact this.1.frame ewT (by have := this.2; omega)
    · have := (hallT j (by rw [← htpins, tpinsOf_length]; exact hj)).1
      simp only [htpins]
      exact this
    · rw [(hkL j hj).1]; have := (hallL j (by omega)).2; omega
    · have := (hallT j (by omega)).2
      omega
  generalize hm₄ : m₃.set64 EREC o r = m₄ at hW
  have hs₃ : (m₃.arr64 EREC).size = (mem.arr64 EREC).size := by rw [ewT.size, ewL.size, ewP.size, hs₁]
  have hc₄ : m₄.arr64 CTL = m₃.arr64 CTL := by rw [← hm₄, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have ht₄ : erecTop m₄ = erecTop m₃ := by simp only [erecTop, hc₄]
  have hsz₄ : (m₄.arr64 EREC).size = (m₃.arr64 EREC).size := by rw [← hm₄, Mem.size_arr64_set64]
  have inv₄ : SInv m₄ a₃ := inv₃.frameE (by rw [← hm₄]; exact frame_set _ _ _) (by have := inv₃.top; omega)
  have ew₄ : EW o.toNat (o.toNat + 1) m₃ m₄ := by rw [← hm₄]; exact EW.set _ _ _
  obtain ⟨pins, ips, a', hrunS, hlen', inv', hall', ew', fr'⟩ :=
    ih m₄ a₃ q₃ (o + 1) (k - 1) q' mem' inv₄ (by omega) hW
  rw [ho1, hkm] at ew'
  have hslot : rdW (mem'.arr64 EREC) (o + UInt64.ofNat 0) = r := by
    simp only [show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]
    rw [ew'.get _ (by omega) (by omega), ← hm₄, rdW_setE _ _ _ (by omega)]
  refine ⟨ps :: pins, ip :: ips, a', run_internPinSets_cons hrunV hrunS, by simp; omega, inv',
    fun i hi => ?_, ?_, ?_⟩
  · cases i with
    | zero =>
      rw [hslot]
      have h1 := hrec.1.frame hrec.2 ew₄ (by omega)
      exact h1.1.frame h1.2 ew' (by omega)
    | succ i =>
      have := hall' i (by simpa using hi)
      rw [show o + 1 + UInt64.ofNat i = o + UInt64.ofNat (i + 1) by
        rw [UInt64.ofNat_add, UInt64.ofNat_one]; ac_rfl] at this
      exact ⟨this.1, by have := this.2.1; omega, fun j hj => by have := this.2.2.1 j hj; omega,
        fun j hj => by have := this.2.2.2 j hj; omega⟩
  · exact (((((hew₁ o.toNat (o.toNat + k.toNat)).trans ewP (by omega)).trans ewL (by omega)).trans
      ewT (by omega)).trans ew₄ (by omega)).trans ew' (by omega)
  · have f₄ : MemFrame PinsA PinsC m₃ m₄ := by rw [← hm₄]; exact frame_pins_set _ _ _
    exact (((((hf₁.mono (by simp) (by simp [PinsC])).trans frP).trans frL).trans frT).trans f₄).trans fr'

end dec

/-! ## `intern_pin_sets` -/

/-- **`intern_pin_sets` refines `internPinSets` in the decoder direction**: a model run that
returns read some variant list `pins`; the twin's `internPinSets pins` succeeds, and the records
are in `EREC` as `PinSetsR` says. Every write is to fresh records (`ErecGrow`), in the stage's
frame. -/
theorem internPinSetsW_dec (rom : List UInt8) (hr : RomOK rom) (n : Nat) (mem : Mem) (a : AState)
    (q q' : Word) (mem' : Mem) (hA : ArenaD mem a) (hmo : ModeOK mem) (hR : RsetR mem) (hok : StateOK a)
    (hstk : (stkTop mem).toNat < 2 ^ 61) (hc : 151 < (mem.arr64 CTL).size)
    (hW : internPinSetsW rom n mem q = some (q', mem')) :
    ∃ (pins : List ConLeche.NatOpPinSet) (ips : List INatOpPinSet) (a' : AState),
      (internPinSets pins).run a = .ok (ips, a') ∧ ArenaD mem' a' ∧ PinSetsR mem' ips ∧ StateOK a' ∧
      RsetR mem' ∧ (stkTop mem').toNat < 2 ^ 61 ∧ ErecGrow mem mem' ∧ MemFrame PinsA PinsC mem mem' ∧
      erecTop mem' ≤ (mem'.arr64 EREC).size ∧ ModeOK mem' := by
  cases n with
  | zero => simp [internPinSetsW] at hW
  | succ n =>
  by_cases hu : ¬ u64OK rom q
  · simp [internPinSetsW, hu] at hW
  rw [internPinSetsW_eq rom n mem q (Decidable.not_not.mp hu)] at hW
  generalize hcw : u64W rom q = c at hW
  rcases hAl : erAllocW mem c with _ | ⟨o, m₁⟩ <;> rw [hAl] at hW
  · simp [ipsK] at hW
  rw [ipsK_some] at hW
  obtain ⟨ho, ht₁, hroom, hf₁, -⟩ := erAlloc_ok hAl hc
  generalize hm₂ : (m₁.set64 CTL 150 o).set64 CTL 151 c = m₂ at hW
  have hf₂ : MemFrame [EREC] [129, 150, 151] mem m₂ := by
    rw [← hm₂]
    exact ((hf₁.mono (by simp) (by simp)).trans ((MemFrame.setCtl _ 150 o).mono (by simp) (by simp))).trans
      ((MemFrame.setCtl _ 151 c).mono (by simp) (by simp))
  have hc₁ : 151 < (m₁.arr64 CTL).size := by rw [hf₁.2.2.1 CTL]; exact hc
  have hE₂ : m₂.arr64 EREC = mem.arr64 EREC := by
    rw [← hm₂, Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    exact hf₁.1 EREC (by simp) (by decide)
  have h150' : 150 < (m₁.arr64 CTL).size := by omega
  have h129 : rdW (m₂.arr64 CTL) 129 = rdW (m₁.arr64 CTL) 129 := by
    rw [← hm₂]; simp [rdW_set64]
  have h150 : rdW (m₂.arr64 CTL) 150 = o := by
    rw [← hm₂]; simp [rdW_set64, h150']
  have h151 : rdW (m₂.arr64 CTL) 151 = c := by
    rw [← hm₂]; simp [rdW_set64, Mem.size_arr64_set64]; intro h; omega
  have ht₂ : erecTop m₂ = erecTop m₁ := by simp only [erecTop, h129]
  have inv₂ : SInv m₂ a := ⟨ArenaD.frameHi hf₂ hiA hiC hA,
    hR.frame hf₂ (by decide) (by decide) (by decide) (by decide), hok,
    by simp only [stkTop]; rw [hf₂.2.1 131 (by decide)]; exact hstk,
    by rw [hf₂.2.2.1 CTL]; exact hc, by rw [ht₂, ht₁, hE₂]; exact hroom, hmo.frame hf₂ (by decide) (by decide)⟩
  obtain ⟨pins, ips, a', hrun, hlen, inv', hall, ew, fr⟩ :=
    setsTo_dec rom hr n m₂ a (q + 8) o c q' mem' inv₂ (by omega) hW
  refine ⟨pins, ips, a', hrun, inv'.arena, ⟨by rw [ew.c151, h151, hlen], by
    rw [ew.c150, h150]; have := ew.top; omega, fun k hk => by rw [ew.c150, h150]; exact (hall k hk).1⟩,
    inv'.ok, inv'.rset, inv'.stk, ⟨by have := ew.top; omega, fun i hi => ?_, by rw [ew.size, hE₂]⟩,
    (hf₂.mono (by simp [PinsA]) (by simp [PinsC])).trans fr, inv'.top, inv'.mode⟩
  rw [ew.low i (by omega) (by omega), hE₂]

end L.Rom
