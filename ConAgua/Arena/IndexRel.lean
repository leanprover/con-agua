module

public import ConAgua.Arena.Env
public import ConRon.Arena.StreamIndex
import ConAgua.Arena.View

@[expose] public section

/-!
# The stream index in L and a job's start

`IndexR m I` relates the stream index's rows (`EIX*`, `TIX*`), `FIRSTS` and the next counter
`CTL[128]` to the twin's `IStreamIndex` (what `build_index` builds). A job (`record_job`) bumps
the stamp above every own row (`OwnBelow`), so the own layer reads empty (`OwnEmpty`), and sets
the view words `CTL[134]`, `CTL[135]`: then `EnvR` holds at `vis = 0` of the twin's
`IStreamIndex.view` (`EnvR.ofIndex`).
-/

namespace L.Arena
open ConRon.Arena

section rel
/-! ### A job's start: the stream index's view and a fresh own layer -/

/-- **The stream index** (`IStreamIndex`, as `build_index` leaves it): the base rows are the
twin's `base.idx`/`base.tbls` (as `EnvR`'s `base`/`btbl`), `FIRSTS` holds `firsts`, `CTL[128]` is
`next`. -/
structure IndexR (m : Mem) (I : IStreamIndex) : Prop where
  base : ∀ n : NIdx,
    (I.base.idx[n]?).map (fun e => (e.1, some e.2)) =
      (if (baseRow m n.word.toUInt64).1 = 0 then none
       else some ((baseRow m n.word.toUInt64).1.toNat - 1,
         decCI (erecP m) (baseRow m n.word.toUInt64).2.toNat))
  btbl : ∀ n : NIdx,
    (I.base.tbls[n]?).map (fun e => (e.1, some e.2)) =
      (if (baseTbl m n.word.toUInt64).1 = 0 then none
       else some ((baseTbl m n.word.toUInt64).1.toNat - 1,
         decTbl (erecP m) (baseTbl m n.word.toUInt64).2.toNat))
  firsts : ∀ i (h : i < I.firsts.size), (rdW (m.arr64 FIRSTS) (UInt64.ofNat i)).toNat = I.firsts[i]
  firstsSize : I.firsts.size ≤ (m.arr64 FIRSTS).size
  next : (rdW (m.arr64 CTL) 128).toNat = I.next

/-- An optional counter as a word (`IStreamIndex.natFrom`/`strFrom`): `0` for none, `k + 1` for
`some k`. -/
def optW (w : Word) : Option Nat := if w = 0 then none else some (w.toNat - 1)

/-- **The frozen stream index** (`IStreamIndex.freeze`, at the end of `build_index`): the literal
names are the words `CTL[162‥171]` (`EnvR`'s `lits`), the flags' thresholds `natFrom`/`strFrom`
the words `CTL[172]`, `CTL[173]` (`optW`). -/
structure FrozenR (m : Mem) (I : IStreamIndex) : Prop where
  lits : I.base.lits.map (·.word.toUInt64) = litWords m
  natFrom : I.natFrom = optW (rdW (m.arr64 CTL) 172)
  strFrom : I.strFrom = optW (rdW (m.arr64 CTL) 173)

/-- The `CTL` words `FrozenR` reads. -/
def frozenCtl : List Word := [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]

theorem litW_mem_frozenCtl : ∀ i < 10, (162 + UInt64.ofNat i : Word) ∈ frozenCtl := by decide

theorem FrozenR.congr {m m' : Mem} {I : IStreamIndex}
    (hc : ∀ x ∈ frozenCtl, rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x) (h : FrozenR m I) :
    FrozenR m' I :=
  ⟨by rw [litWords_congr (fun i hi => hc _ (litW_mem_frozenCtl i hi))]; exact h.lits,
   by rw [hc 172 (by decide)]; exact h.natFrom, by rw [hc 173 (by decide)]; exact h.strFrom⟩

theorem FrozenR.frame {A : List TieredArray} {C : List Word} {m m' : Mem} {I : IStreamIndex}
    (hC : ∀ x ∈ C, x ∉ frozenCtl) (hf : MemFrame A C m m') (h : FrozenR m I) : FrozenR m' I :=
  h.congr fun x hx => hf.ctl x (fun hm => hC x hm hx)

theorem not_mem_frozenCtl {x : Word} (h : x.toNat < 162 ∨ 174 ≤ x.toNat) : x ∉ frozenCtl :=
  fun hm => by
    simp only [frozenCtl, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with e | e | e | e | e | e | e | e | e | e | e | e <;> subst e <;> simp at h

/-- The own layer is empty. -/
def OwnEmpty (m : Mem) : Prop := ∀ w, (ownRaw m w).1 = 0 ∧ ownTbl m w = 0

/-- **A stamp above every row's empties the own layer.** -/
theorem OwnEmpty.of_below {m : Mem} (_h : OwnBelow m) (hlt : ∀ w, rowTag w ≤ 2 →
    ((ownRow m w).1 >>> 32).toNat < (stampW m).toNat ∧
      (rdN (m.arr64 (otxArrT w)) (rowIx w)).toNat < (stampW m).toNat) : OwnEmpty m := by
  intro w
  by_cases ht : rowTag w ≤ 2
  · obtain ⟨a, b⟩ := hlt w ht
    refine ⟨?_, ?_⟩
    · simp only [ownRaw, ht, true_and]
      rw [ite_eq_right (fun e => by rw [e] at a; omega)]
    · rw [ownTbl_eq]; simp only [ht, true_and]
      rw [ite_eq_right (fun e => by rw [e] at b; omega)]
  · exact ⟨by simp [ownRaw, ht], by simp [ownTbl, ht]⟩

/-- **The environment at a job's start**: the stream index at the view of position `k`, an empty
own layer, `vis = 0`. -/
theorem EnvR.ofIndex {m : Mem} {I : IStreamIndex} {k : Nat} (hI : IndexR m I) (hF : FrozenR m I)
    (hO : OwnEmpty m)
    (hB : OwnBelow m) (hs : (stampW m).toNat < 2 ^ 32) (h134 : (rdW (m.arr64 CTL) 134).toNat = I.firsts.getD k I.next)
    (h135 : (rdW (m.arr64 CTL) 135).toNat = k)
    (h160 : (rdW (m.arr64 CTL) 160 != 0) = fromLe I.natFrom (I.firsts.getD k I.next))
    (h161 : (rdW (m.arr64 CTL) 161 != 0) = fromLe I.strFrom (I.firsts.getD k I.next)) :
    EnvR m 0 (I.view k) := by
  refine ⟨fun n => ?_, fun n hn => absurd (hO _).1 hn, fun n hn => absurd (hO _).1 hn,
    fun n _ hn => absurd (hO _).1 hn, fun n => ?_, fun n hn => absurd (hO _).2 hn, ?_, ?_,
    fun n => hI.base n, fun n => hI.btbl n, hs, hB, by simp only [IStreamIndex.view, h160],
    by simp only [IStreamIndex.view, h161], by simp only [IStreamIndex.view]; exact hF.lits⟩
  · simp [IStreamIndex.view, ownFind]
  · simp [IStreamIndex.view, (hO _).2]
  · simp only [IStreamIndex.view]; rw [h134]
  · simp only [IStreamIndex.view]; rw [h135]

/-! ### One step of `insertConsts`, `insertTables`, and a record's first counter -/

theorem baseSet_arr_of {m : Mem} {w c p : Word} {b : TieredArray}
    (h : b ≠ (eixArr (rowTag w) : TieredArray)) : (baseSet m w c p).arr64 b = m.arr64 b := by
  simp only [baseSet, Mem.arr64_set64_ne _ _ _ _ _ h]

theorem baseTblSet_arr_of {m : Mem} {w r p : Word} {b : TieredArray}
    (h : b ≠ (tixArr (rowTag w) : TieredArray)) : (baseTblSet m w r p).arr64 b = m.arr64 b := by
  simp only [baseTblSet, Mem.arr64_set64_ne _ _ _ _ _ h]

theorem eix_ne {w : Word} {b : TieredArray} (h : b.arr ≠ 132 ∧ b.arr ≠ 133 ∧ b.arr ≠ 134) :
    b ≠ (eixArr (rowTag w) : TieredArray) := fun e => by
  have := eixArr_arr (rowTag w); rw [← e] at this; omega

theorem tix_ne {w : Word} {b : TieredArray} (h : b.arr ≠ 129 ∧ b.arr ≠ 130 ∧ b.arr ≠ 131) :
    b ≠ (tixArr (rowTag w) : TieredArray) := fun e => by
  have := tixArr_arr (rowTag w); rw [← e] at this; omega

/-- A memory change outside `EREC`, `FIRSTS`, the base rows and the `CTL` words `128‥130` keeps
the decodings. -/
theorem erecP_congr' {m m' : Mem} (h1 : m'.arr64 EREC = m.arr64 EREC)
    (h2 : m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC))
    (h3 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129) (h4 : rdW (m'.arr64 CTL) 130 = rdW (m.arr64 CTL) 130) :
    erecP m' = erecP m := by
  funext i; simp only [erecP, erTop, erecTop1, h1, h2, h3, h4]
  rfl

theorem rdW_set_ctl (m : Mem) (k v x : Word) (h : k ≠ x) :
    rdW ((m.set64 CTL k v).arr64 CTL) x = rdW (m.arr64 CTL) x := by
  rw [rdW_set64]; simp [h]

/-- **One step of `insertConsts`** (`idx_consts`' loop body): the constant record at `q` (its name
`w`), at the next counter: its base row written if it has none, the counter moved. -/
theorem IndexR.insertConst {m : Mem} {I : IStreamIndex} (h : IndexR m I) {q : Word}
    {ci : IConstantInfo} (hci : decCI (erecP m) q.toNat = some ci) {w : Word}
    (hw : erecP m (q.toNat + CI.cv.toNat) = some w) (hnx : I.next < 2 ^ 32 - 2)
    (hset : (baseRow m w).1 = 0 → rowTag w ≤ 2 ∧ rowTier w = 0 ∧
      rowIx w + 1 < (m.arr64 (eixArr (rowTag w))).size) (hc : 128 < (m.arr64 CTL).size) :
    IndexR ((if (baseRow m w).1 = 0 then baseSet m w (rdW (m.arr64 CTL) 128 + 1) q else m).set64 CTL 128
        (rdW (m.arr64 CTL) 128 + 1))
      { I with base := { I.base with idx := I.base.idx.insertIfNew ci.name (I.next, ci) },
               next := I.next + 1 } := by
  obtain ⟨w', hw', hw32, hname⟩ := decCI_name hci
  rw [hw] at hw'; cases hw'
  have hn := h.next
  have hnx1 : (rdW (m.arr64 CTL) 128 + 1).toNat = I.next + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  generalize hm1 : (if (baseRow m w).1 = 0 then baseSet m w (rdW (m.arr64 CTL) 128 + 1) q else m) = m1
  have a1 : ∀ b : TieredArray, b.arr ≠ 132 ∧ b.arr ≠ 133 ∧ b.arr ≠ 134 → m1.arr64 b = m.arr64 b := by
    intro b hb; rw [← hm1]; split
    · exact baseSet_arr_of (eix_ne hb)
    · rfl
  have a2 : ∀ b : TieredArray, b ≠ CTL → b.arr ≠ 132 ∧ b.arr ≠ 133 ∧ b.arr ≠ 134 →
      (m1.set64 CTL 128 (rdW (m.arr64 CTL) 128 + 1)).arr64 b = m.arr64 b := fun b h1 h2 => by
    rw [Mem.arr64_set64_ne _ _ _ _ _ h1, a1 b h2]
  have hctl : ∀ x : Word, x ≠ 128 → rdW ((m1.set64 CTL 128 (rdW (m.arr64 CTL) 128 + 1)).arr64 CTL) x =
      rdW (m.arr64 CTL) x := fun x hx => by
    rw [rdW_set_ctl _ _ _ _ (Ne.symm hx), a1 (CTL : TieredArray) (by decide)]
  have hP : erecP (m1.set64 CTL 128 (rdW (m.arr64 CTL) 128 + 1)) = erecP m :=
    erecP_congr' (a2 _ (by decide) (by decide)) (a2 _ (by decide) (by decide))
      (hctl 129 (by decide)) (hctl 130 (by decide))
  have hbr : ∀ x : Word, baseRow (m1.set64 CTL 128 (rdW (m.arr64 CTL) 128 + 1)) x = baseRow m1 x := by
    intro x; have := eixArr_arr (rowTag x)
    have n1 : (eixArr (rowTag x) : TieredArray) ≠ CTL := by
      unfold eixArr; split <;> (try split) <;> decide
    simp only [baseRow, Mem.arr64_set64_ne _ _ _ _ _ n1]
  have hbt : ∀ x : Word, baseTbl (m1.set64 CTL 128 (rdW (m.arr64 CTL) 128 + 1)) x = baseTbl m x := by
    intro x; have := tixArr_arr (rowTag x)
    have n1 : (tixArr (rowTag x) : TieredArray) ≠ CTL := by
      unfold tixArr; split <;> (try split) <;> decide
    have n2 : (tixArr (rowTag x) : TieredArray).arr ≠ 132 ∧ (tixArr (rowTag x) : TieredArray).arr ≠ 133 ∧
      (tixArr (rowTag x) : TieredArray).arr ≠ 134 := by omega
    simp only [baseTbl, a2 _ n1 n2]
  have hname' : ∀ n : NIdx, (ci.name == n) = decide (n.word.toUInt64 = w) := by
    intro n; rw [hname, nidx_beq, decI_word_self w hw32]
  have hmem : ci.name ∈ I.base.idx ↔ (baseRow m w).1 ≠ 0 := by
    have hb := h.base (decI w); rw [decI_word_self w hw32] at hb
    rw [hname, Std.HashMap.mem_iff_isSome_getElem?]
    cases e : I.base.idx[(decI w : NIdx)]? with
    | none => rw [e] at hb; by_cases b0 : (baseRow m w).1 = 0 <;> simp_all
    | some y => rw [e] at hb; by_cases b0 : (baseRow m w).1 = 0 <;> simp_all
  refine ⟨fun n => ?_, fun n => ?_, fun i hi => ?_, ?_, ?_⟩
  · simp only [Std.HashMap.getElem?_insertIfNew, hname', hmem, hbr, hP]
    by_cases e : n.word.toUInt64 = w
    · by_cases b0 : (baseRow m w).1 = 0
      · obtain ⟨t1, t2, t3⟩ := hset b0
        have : m1 = baseSet m w (rdW (m.arr64 CTL) 128 + 1) q := by rw [← hm1, ite_eq_left b0]
        rw [this, e, baseRow_baseSet_self t1 t2 t3]
        have hne : rdW (m.arr64 CTL) 128 + 1 ≠ 0 := fun z => by rw [z] at hnx1; simp at hnx1
        simp [b0, hne, hnx1, hci]
      · have : m1 = m := by rw [← hm1, ite_eq_right b0]
        rw [this, e]; simp only [b0, ne_eq, not_false_eq_true, not_true_eq_false, and_false,
          decide_true, ite_false]
        have := h.base n; rw [e, ite_eq_right b0] at this; exact this
    · have hb1 : baseRow m1 n.word.toUInt64 = baseRow m n.word.toUInt64 := by
        rw [← hm1]; split
        · rename_i b0; obtain ⟨t1, t2, -⟩ := hset b0
          exact baseRow_baseSet_other hw32 (L.Arena.idx_word_lt32 n) t1 t2 e
        · rfl
      simp only [e, decide_false, Bool.false_eq_true, false_and, ite_false, hb1]
      exact h.base n
  · simp only [hbt, hP]; exact h.btbl n
  · rw [a2 _ (by decide) (by decide)]; exact h.firsts i hi
  · rw [a2 _ (by decide) (by decide)]; exact h.firstsSize
  · simp only [Mem.arr64_set64_same, rdW_set!, a1 (CTL : TieredArray) (by decide)]
    simp only [show (128 : Word).toNat = 128 from rfl, hc, and_self, ite_true]; exact hnx1

/-- **One step of `insertTables`** (`idx_tables`' loop body): the table record at `q` (its
structure `w`) of record position `r`: its base table row written if it has none. -/
theorem IndexR.insertTable {m : Mem} {I : IStreamIndex} (h : IndexR m I) {q : Word}
    {tb : IProjTable} (htb : decTbl (erecP m) q.toNat = some tb) {w : Word}
    (hw : erecP m (q.toNat + ProjTbl.structName.toNat) = some w) {r : Word} (hr : r.toNat + 1 < 2 ^ 64)
    (hset : (baseTbl m w).1 = 0 → rowTag w ≤ 2 ∧ rowTier w = 0 ∧
      rowIx w + 1 < (m.arr64 (tixArr (rowTag w))).size) :
    IndexR (if (baseTbl m w).1 = 0 then baseTblSet m w (r + 1) q else m)
      { I with base := { I.base with tbls := I.base.tbls.insertIfNew tb.structName (r.toNat, tb) } } := by
  obtain ⟨w', hw', hw32, hname⟩ := decTbl_name htb
  rw [hw] at hw'; cases hw'
  have hr1 : (r + 1).toNat = r.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  generalize hm1 : (if (baseTbl m w).1 = 0 then baseTblSet m w (r + 1) q else m) = m1
  have a1 : ∀ b : TieredArray, b.arr ≠ 129 ∧ b.arr ≠ 130 ∧ b.arr ≠ 131 → m1.arr64 b = m.arr64 b := by
    intro b hb; rw [← hm1]; split
    · exact baseTblSet_arr_of (tix_ne hb)
    · rfl
  have hctl : ∀ x : Word, rdW (m1.arr64 CTL) x = rdW (m.arr64 CTL) x := fun x => by
    rw [a1 (CTL : TieredArray) (by decide)]
  have hP : erecP m1 = erecP m :=
    erecP_congr' (a1 _ (by decide)) (a1 _ (by decide)) (hctl 129) (hctl 130)
  have hbr : ∀ x : Word, baseRow m1 x = baseRow m x := by
    intro x; have := eixArr_arr (rowTag x)
    simp only [baseRow, a1 (eixArr (rowTag x) : TieredArray) (by omega)]
  have hname' : ∀ n : NIdx, (tb.structName == n) = decide (n.word.toUInt64 = w) := by
    intro n; rw [hname, nidx_beq, decI_word_self w hw32]
  have hmem : tb.structName ∈ I.base.tbls ↔ (baseTbl m w).1 ≠ 0 := by
    have hb := h.btbl (decI w); rw [decI_word_self w hw32] at hb
    rw [hname, Std.HashMap.mem_iff_isSome_getElem?]
    cases e : I.base.tbls[(decI w : NIdx)]? with
    | none => rw [e] at hb; by_cases b0 : (baseTbl m w).1 = 0 <;> simp_all
    | some y => rw [e] at hb; by_cases b0 : (baseTbl m w).1 = 0 <;> simp_all
  refine ⟨fun n => ?_, fun n => ?_, fun i hi => ?_, ?_, ?_⟩
  · simp only [hbr, hP]; exact h.base n
  · simp only [Std.HashMap.getElem?_insertIfNew, hname', hmem, hP]
    by_cases e : n.word.toUInt64 = w
    · by_cases b0 : (baseTbl m w).1 = 0
      · obtain ⟨t1, t2, t3⟩ := hset b0
        have : m1 = baseTblSet m w (r + 1) q := by rw [← hm1, ite_eq_left b0]
        rw [this, e, baseTbl_baseTblSet_self t1 t2 t3]
        have hne : r + 1 ≠ 0 := fun z => by rw [z] at hr1; simp at hr1
        simp [b0, hne, hr1, htb]
      · have : m1 = m := by rw [← hm1, ite_eq_right b0]
        rw [this, e]; simp only [b0, ne_eq, not_false_eq_true, not_true_eq_false, and_false,
          decide_true, ite_false]
        have := h.btbl n; rw [e, ite_eq_right b0] at this; exact this
    · have hb1 : baseTbl m1 n.word.toUInt64 = baseTbl m n.word.toUInt64 := by
        rw [← hm1]; split
        · rename_i b0; obtain ⟨t1, t2, -⟩ := hset b0
          exact baseTbl_baseTblSet_other hw32 (L.Arena.idx_word_lt32 n) t1 t2 e
        · rfl
      simp only [e, decide_false, Bool.false_eq_true, false_and, ite_false, hb1]
      exact h.btbl n
  · rw [a1 _ (by decide)]; exact h.firsts i hi
  · rw [a1 _ (by decide)]; exact h.firstsSize
  · rw [hctl]; exact h.next

/-- **A record's first counter** (`idx_add`'s `FIRSTS[k] := CTL[128]`, `k` the number of records
so far): `firsts` gains the next counter. -/
theorem IndexR.pushFirst {m : Mem} {I : IStreamIndex} (h : IndexR m I)
    (hk : I.firsts.size < (m.arr64 FIRSTS).size) (hk64 : I.firsts.size < 2 ^ 64) :
    IndexR (m.set64 FIRSTS (UInt64.ofNat I.firsts.size) (rdW (m.arr64 CTL) 128))
      { I with firsts := I.firsts.push I.next } := by
  have a1 : ∀ b : TieredArray, b ≠ FIRSTS → (m.set64 FIRSTS (UInt64.ofNat I.firsts.size)
      (rdW (m.arr64 CTL) 128)).arr64 b = m.arr64 b := fun b hb => Mem.arr64_set64_ne _ _ _ _ _ hb
  have hctl : ∀ x : Word, rdW ((m.set64 FIRSTS (UInt64.ofNat I.firsts.size)
      (rdW (m.arr64 CTL) 128)).arr64 CTL) x = rdW (m.arr64 CTL) x := fun x => by
    rw [a1 _ (by decide)]
  have hP : erecP (m.set64 FIRSTS (UInt64.ofNat I.firsts.size) (rdW (m.arr64 CTL) 128)) = erecP m :=
    erecP_congr' (a1 _ (by decide)) (a1 _ (by decide)) (hctl 129) (hctl 130)
  have hbr : ∀ x : Word, baseRow (m.set64 FIRSTS (UInt64.ofNat I.firsts.size)
      (rdW (m.arr64 CTL) 128)) x = baseRow m x := by
    intro x; simp only [baseRow, a1 (eixArr (rowTag x) : TieredArray) (by unfold eixArr; split <;> (try split) <;> decide)]
  have hbt : ∀ x : Word, baseTbl (m.set64 FIRSTS (UInt64.ofNat I.firsts.size)
      (rdW (m.arr64 CTL) 128)) x = baseTbl m x := by
    intro x; simp only [baseTbl, a1 (tixArr (rowTag x) : TieredArray) (by unfold tixArr; split <;> (try split) <;> decide)]
  have hsz : (UInt64.ofNat I.firsts.size).toNat = I.firsts.size := by simp; omega
  refine ⟨fun n => ?_, fun n => ?_, fun i hi => ?_, ?_, ?_⟩
  · simp only [hbr, hP]; exact h.base n
  · simp only [hbt, hP]; exact h.btbl n
  · simp only [Array.size_push] at hi
    have hi64 : (UInt64.ofNat i).toNat = i := by simp; omega
    rw [Mem.arr64_set64_same, rdW_set!, hsz, hi64]
    by_cases e : I.firsts.size = i
    · subst e; simp only [hk, and_self, ite_true, Array.getElem_push_eq]; exact h.next
    · have hi' : i < I.firsts.size := by omega
      rw [ite_eq_right (fun c => e c.1), Array.getElem_push_lt hi']
      exact h.firsts i hi'
  · rw [Mem.size_arr64_set64]; simp; omega
  · rw [hctl]; exact h.next

end rel

end L.Arena
