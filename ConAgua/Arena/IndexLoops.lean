module

public import ConAgua.Arena.IndexRel
public import ConAgua.Arena.CheckerL
import ConAgua.Census.Attr
import ConAgua.Arena.RecSim
import ConAgua.L.For
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import all ConAgua.Arena.CheckerL
import ConAgua.L.WordOff

@[expose] public section

/-!
# The stream index's loops: `idx_consts`, `idx_tables`

`idx_consts(o, n)` is `insertConsts` over the decoded `IW` slice `(o, n)` of constant records, at
the next counter `CTL[128]`; `idx_tables(o, n, r)` is `insertTables` over a slice of table records
at record position `r`. Each loop keeps `IndexR` over the processed prefix (`IndexR.insertConst`,
`IndexR.insertTable`, one iteration each) and writes only the stream index's rows (and
`CTL[128]`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind (IW iwN decPL)

/-! ## The twin's folds, one element at a time -/

theorem insertConsts_snoc (x : IConstantInfo) : ∀ (A : List IConstantInfo)
    (idx : Std.HashMap NIdx (Nat × IConstantInfo)) (c : Nat),
    insertConsts idx c (A ++ [x]) =
      ((insertConsts idx c A).1.insertIfNew x.name ((insertConsts idx c A).2, x),
        (insertConsts idx c A).2 + 1)
  | [], _, _ => rfl
  | _ :: A, _, _ => insertConsts_snoc x A _ _

theorem insertTables_snoc (x : IProjTable) (r : Nat) : ∀ (A : List IProjTable)
    (tb : Std.HashMap NIdx (Nat × IProjTable)),
    insertTables tb r (A ++ [x]) = (insertTables tb r A).insertIfNew x.structName (r, x)
  | [], _ => rfl
  | _ :: A, _ => insertTables_snoc x r A _

/-- The index after the constants `A`. -/
def insC (I : IStreamIndex) (A : List IConstantInfo) : IStreamIndex :=
  { I with base := { I.base with idx := (insertConsts I.base.idx I.next A).1 },
           next := (insertConsts I.base.idx I.next A).2 }

/-- The index after the tables `A` of record position `r`. -/
def insT (I : IStreamIndex) (r : Nat) (A : List IProjTable) : IStreamIndex :=
  { I with base := { I.base with tbls := insertTables I.base.tbls r A } }

theorem insC_nil (I : IStreamIndex) : insC I [] = I := rfl
theorem insT_nil (I : IStreamIndex) (r : Nat) : insT I r [] = I := rfl

/-- One constant into the index (`insertConsts`' step). -/
def insC1 (I : IStreamIndex) (x : IConstantInfo) : IStreamIndex :=
  { I with base := { I.base with idx := I.base.idx.insertIfNew x.name (I.next, x) }, next := I.next + 1 }

/-- One table into the index (`insertTables`' step). -/
def insT1 (I : IStreamIndex) (r : Nat) (x : IProjTable) : IStreamIndex :=
  { I with base := { I.base with tbls := I.base.tbls.insertIfNew x.structName (r, x) } }

theorem insC_snoc (I : IStreamIndex) (A : List IConstantInfo) (x : IConstantInfo) :
    insC I (A ++ [x]) = insC1 (insC I A) x := by
  simp only [insC, insC1, insertConsts_snoc]

theorem insT_snoc (I : IStreamIndex) (r : Nat) (A : List IProjTable) (x : IProjTable) :
    insT I r (A ++ [x]) = insT1 (insT I r A) r x := by
  simp only [insT, insT1, insertTables_snoc]

/-! ## Reading a decoded slice -/

theorem decPL_get' {α : Type} {m : Mem} {f : Nat → Option α} {o l : Nat} {xs : List α}
    (h : decPL m f o l = some xs) (j : Nat) (hj : j < l) :
    ∃ v, iwN m (o + j) = some v ∧ ∃ hx : j < xs.length, f v = some xs[j] := by
  have hlen := L.Ind.decPL_length (m := m) h
  have := L.Ind.mapM_opt_get _ (List.range l) xs h j (by simpa using hj)
  simp only [List.getElem_range] at this
  cases e : iwN m (o + j) with
  | none => rw [e] at this; simp at this
  | some v =>
    rw [e] at this
    exact ⟨v, rfl, by omega, this⟩

theorem take_succ_of {α : Type} (xs : List α) (j : Nat) (hj : j < xs.length) :
    xs.take (j + 1) = xs.take j ++ [xs[j]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl

/-! ## The frame of the index writes -/

/-- The stream index's constant rows. -/
def EixA : List TieredArray := [(EIXA : TieredArray), EIXS, EIXN]
/-- The stream index's table rows. -/
def TixA : List TieredArray := [(TIXA : TieredArray), TIXS, TIXN]

theorem eix_memA (g : Nat) : (eixArr g : TieredArray) ∈ EixA := by
  unfold eixArr; split <;> (try split) <;> decide

theorem tix_memA (g : Nat) : (tixArr g : TieredArray) ∈ TixA := by
  unfold tixArr; split <;> (try split) <;> decide

theorem baseSet_frame (m : Mem) (w c q : Word) : MemFrame EixA [] m (baseSet m w c q) := by
  have hn : (eixArr (rowTag w) : TieredArray) ≠ CTL := by
    unfold eixArr; split <;> (try split) <;> decide
  exact ((MemFrame.set64 m _ hn _ c).trans (MemFrame.set64 _ _ hn _ q)).mono
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro b (rfl | rfl) <;> exact eix_memA _)
    (by simp)

theorem baseTblSet_frame (m : Mem) (w r q : Word) : MemFrame TixA [] m (baseTblSet m w r q) := by
  have hn : (tixArr (rowTag w) : TieredArray) ≠ CTL := by
    unfold tixArr; split <;> (try split) <;> decide
  exact ((MemFrame.set64 m _ hn _ r).trans (MemFrame.set64 _ _ hn _ q)).mono
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro b (rfl | rfl) <;> exact tix_memA _)
    (by simp)

/-- A frame of the index writes keeps the record pool's decodings and the pool `IW`. -/
theorem erecP_of_frameI {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, 129 ≤ b.arr ∧ b.arr ≤ 134) (hC : ∀ x ∈ C, x = 128) :
    erecP m' = erecP m ∧ iwN m' = iwN m ∧ m'.arr64 IW = m.arr64 IW := by
  have ha : ∀ b : TieredArray, (b.arr < 129 ∨ 134 < b.arr) → b ≠ CTL → m'.arr64 b = m.arr64 b :=
    fun b h1 h2 => hf.arr b (fun hm => by have := hA b hm; omega) h2
  have hc : ∀ x : Word, x ≠ 128 → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x :=
    fun x h => hf.ctl x (fun hm => h (hC x hm))
  have hI : m'.arr64 IW = m.arr64 IW := ha IW (by decide) (by decide)
  refine ⟨erecP_congr' (ha _ (by decide) (by decide)) (ha _ (by decide) (by decide))
    (hc 129 (by decide)) (hc 130 (by decide)), ?_, hI⟩
  funext i; simp only [L.Ind.iwN, L.Ind.iwA, hI]

/-! ## `idx_consts` -/

/-- The loop of `idx_consts`. -/
def idxConstsLoop : Stmt :=
  match idxConstsL.body with
  | .seq _ (.seq w _) => w
  | _ => .skip

theorem idxConstsL_eq : idxConstsL =
    { nparams := 2, nlocals := 9,
      body := .seq (.set 2 (.const 0)) (.seq idxConstsLoop (.ret [.const 0])) } := by
  unfold idxConstsLoop; unfold idxConstsL; rfl

/-- The loop's invariant at the `j`-th element: the index over the first `j` constants, the
memory changed only in the index rows and `CTL[128]`. -/
structure IcInv (m₀ : Mem) (I : IStreamIndex) (cs : List IConstantInfo) (j : Nat) (m : Mem) : Prop where
  idx : IndexR m (insC I (cs.take j))
  frame : MemFrame EixA [128] m₀ m
  /-- The next counter stays below `2^32` (`idx_consts` aborts from `2^32 - 2` on). -/
  nlt : (insC I (cs.take j)).next < 2 ^ 32

/-- One iteration's memory step keeps the invariant. -/
theorem IcInv.step {m₀ m : Mem} {I : IStreamIndex} {cs : List IConstantInfo} {j : Nat} {o : Word}
    (h : IcInv m₀ I cs j m) (hL : decPL m₀ (fun q => decCI (erecP m₀) q) o.toNat cs.length = some cs)
    (hj : j < cs.length) (hc : 128 < (m₀.arr64 CTL).size) (hsz : (m₀.arr64 IW).size < 2 ^ 64)
    (hnx : (rdW (m.arr64 CTL) 128).toNat < 4294967294)
    (hset : (baseRow m (erecRd m (rdW (m.arr64 IW) (o + UInt64.ofNat j) + (CI.cv + CV.name)))).1 = 0 →
      rowTag (erecRd m (rdW (m.arr64 IW) (o + UInt64.ofNat j) + (CI.cv + CV.name))) ≤ 2 ∧
      rowTier (erecRd m (rdW (m.arr64 IW) (o + UInt64.ofNat j) + (CI.cv + CV.name))) = 0 ∧
      rowIx (erecRd m (rdW (m.arr64 IW) (o + UInt64.ofNat j) + (CI.cv + CV.name))) + 1 <
        (m.arr64 (eixArr (rowTag (erecRd m (rdW (m.arr64 IW) (o + UInt64.ofNat j) + (CI.cv + CV.name)))))).size) :
    IcInv m₀ I cs (j + 1)
      ((if (baseRow m (erecRd m (rdW (m.arr64 IW) (o + UInt64.ofNat j) + (CI.cv + CV.name)))).1 = 0 then
          baseSet m (erecRd m (rdW (m.arr64 IW) (o + UInt64.ofNat j) + (CI.cv + CV.name))) (rdW (m.arr64 CTL) 128 + 1)
            (rdW (m.arr64 IW) (o + UInt64.ofNat j))
        else m).set64 CTL 128 (rdW (m.arr64 CTL) 128 + 1)) := by
  obtain ⟨hP, hiw, hIW⟩ := erecP_of_frameI h.frame
    (by simp only [EixA, List.mem_cons, List.not_mem_nil, or_false]; rintro b (rfl | rfl | rfl) <;> decide)
    (by simp)
  obtain ⟨v, hv, hx, hci⟩ := decPL_get' hL j hj
  rw [← hiw] at hv
  have hsz : (m.arr64 IW).size < 2 ^ 64 := by rw [hIW]; exact hsz
  obtain ⟨hq, hv64⟩ := L.Ind.iwN_rdW_at hv hsz
  generalize hqd : rdW (m.arr64 IW) (o + UInt64.ofNat j) = q at hq hset ⊢
  have hvq : q.toNat = v := by subst hq; simp; omega
  rw [← hP, ← hvq] at hci
  obtain ⟨w, hw, -, -⟩ := decCI_name hci
  have hw1 : erecP m (q + (CI.cv + CV.name)).toNat = some w := by
    rw [off_add_toNat CI.cv_name_toNat (erecP_lt64 hw)]; exact hw
  have hrd : erecRd m (q + (CI.cv + CV.name)) = w := erecRd_of hw1
  rw [hrd] at hset ⊢
  have hn := h.idx.next
  have hnx' : (insC I (cs.take j)).next < 2 ^ 32 - 2 := by rw [← hn]; omega
  have hst := IndexR.insertConst h.idx hci hw hnx' hset (by rw [h.frame.size CTL]; exact hc)
  refine ⟨?_, ?_, ?_⟩
  · rw [take_succ_of cs j hx, insC_snoc]; exact hst
  · have hf1 : MemFrame EixA [] m (if (baseRow m w).1 = 0 then
        baseSet m w (rdW (m.arr64 CTL) 128 + 1) q else m) := by
      split
      · exact baseSet_frame _ _ _ _
      · exact MemFrame.refl _ _ _
    exact (h.frame.trans (hf1.mono (fun _ h => h) (by simp))).trans
      ((MemFrame.setCtl _ 128 _).mono (by simp) (by simp))
  · rw [take_succ_of cs j hx, insC_snoc]
    simp only [insC1]
    omega

/-- The loop's step, closed: from the invariant at `j` and one iteration's memory, the invariant
at `j + 1`. -/
theorem icLoop_close {m₀ m m' : Mem} {I : IStreamIndex} {cs : List IConstantInfo} {o l : Word}
    (hL : decPL m₀ (fun q => decCI (erecP m₀) q) o.toNat cs.length = some cs) (hl : cs.length = l.toNat)
    (hc : 128 < (m₀.arr64 CTL).size) (hsz : (m₀.arr64 IW).size < 2 ^ 64) {j : Word} (hj : j < l)
    (hI : IcInv m₀ I cs j.toNat m) (hnx : ¬ 4294967294 ≤ rdW (m.arr64 CTL) 128)
    (hm' : m' = if (baseRow m (erecRd m (rdW (m.arr64 IW) (o + j) + (CI.cv + CV.name)))).1 = 0 then
        baseSet m (erecRd m (rdW (m.arr64 IW) (o + j) + (CI.cv + CV.name))) (rdW (m.arr64 CTL) 128 + 1)
          (rdW (m.arr64 IW) (o + j)) else m)
    (hset : (baseRow m (erecRd m (rdW (m.arr64 IW) (o + j) + (CI.cv + CV.name)))).1 = 0 →
      rowTag (erecRd m (rdW (m.arr64 IW) (o + j) + (CI.cv + CV.name))) ≤ 2 ∧
      rowTier (erecRd m (rdW (m.arr64 IW) (o + j) + (CI.cv + CV.name))) = 0 ∧
      rowIx (erecRd m (rdW (m.arr64 IW) (o + j) + (CI.cv + CV.name))) + 1 <
        (m.arr64 (eixArr (rowTag (erecRd m (rdW (m.arr64 IW) (o + j) + (CI.cv + CV.name)))))).size) :
    (j + 1).toNat ≤ l.toNat ∧
      IcInv m₀ I cs (j + 1).toNat (m'.set64 CTL 128 (rdW (m.arr64 CTL) 128 + 1)) := by
  have hj' : j.toNat < l.toNat := hj
  have hs := L.toNat_add_one_of_word_lt _ _ hj
  have hnx' : (rdW (m.arr64 CTL) 128).toNat < 4294967294 := by
    have : ¬ (4294967294 : Word).toNat ≤ (rdW (m.arr64 CTL) 128).toNat := hnx
    simp at this; omega
  have hoj : o + UInt64.ofNat j.toNat = o + j := by simp
  have := IcInv.step hI hL (by omega) hc hsz hnx' (by rw [hoj]; exact hset)
  rw [hoj, ← hm'] at this
  exact ⟨by omega, by rw [hs]; exact this⟩

/-! ## `idx_tables` -/

/-- The loop of `idx_tables`. -/
def idxTablesLoop : Stmt :=
  match idxTablesL.body with
  | .seq _ (.seq w _) => w
  | _ => .skip

theorem idxTablesL_eq : idxTablesL =
    { nparams := 3, nlocals := 9,
      body := .seq (.set 3 (.const 0)) (.seq idxTablesLoop (.ret [.const 0])) } := by
  unfold idxTablesLoop; unfold idxTablesL; rfl

/-- The loop's invariant at the `j`-th element: the index over the first `j` tables. -/
structure ItInv (m₀ : Mem) (I : IStreamIndex) (r : Nat) (ts : List IProjTable) (j : Nat) (m : Mem) :
    Prop where
  idx : IndexR m (insT I r (ts.take j))
  frame : MemFrame TixA [] m₀ m

theorem itLoop_close {m₀ m m' : Mem} {I : IStreamIndex} {ts : List IProjTable} {o l r : Word}
    (hL : decPL m₀ (fun q => decTbl (erecP m₀) q) o.toNat ts.length = some ts) (hl : ts.length = l.toNat)
    (hsz : (m₀.arr64 IW).size < 2 ^ 64) (hr : r.toNat + 1 < 2 ^ 64) {j : Word} (hj : j < l)
    (hI : ItInv m₀ I r.toNat ts j.toNat m)
    (hm' : m' = if (baseTbl m (erecRd m (rdW (m.arr64 IW) (o + j) + ProjTbl.structName))).1 = 0 then
        baseTblSet m (erecRd m (rdW (m.arr64 IW) (o + j) + ProjTbl.structName)) (r + 1) (rdW (m.arr64 IW) (o + j)) else m)
    (hset : (baseTbl m (erecRd m (rdW (m.arr64 IW) (o + j) + ProjTbl.structName))).1 = 0 →
      rowTag (erecRd m (rdW (m.arr64 IW) (o + j) + ProjTbl.structName)) ≤ 2 ∧
      rowTier (erecRd m (rdW (m.arr64 IW) (o + j) + ProjTbl.structName)) = 0 ∧
      rowIx (erecRd m (rdW (m.arr64 IW) (o + j) + ProjTbl.structName)) + 1 <
        (m.arr64 (tixArr (rowTag (erecRd m (rdW (m.arr64 IW) (o + j) + ProjTbl.structName))))).size) :
    (j + 1).toNat ≤ l.toNat ∧ ItInv m₀ I r.toNat ts (j + 1).toNat m' := by
  have hj' : j.toNat < l.toNat := hj
  have hs := L.toNat_add_one_of_word_lt _ _ hj
  obtain ⟨hP, hiw, hIW⟩ := erecP_of_frameI hI.frame
    (by simp only [TixA, List.mem_cons, List.not_mem_nil, or_false]; rintro b (rfl | rfl | rfl) <;> decide)
    (by simp)
  obtain ⟨v, hv, hx, htb⟩ := decPL_get' hL j.toNat (by omega)
  rw [← hiw] at hv
  have hsz' : (m.arr64 IW).size < 2 ^ 64 := by rw [hIW]; exact hsz
  obtain ⟨hq, hv64⟩ := L.Ind.iwN_rdW_at hv hsz'
  have hoj : o + UInt64.ofNat j.toNat = o + j := by simp
  rw [hoj] at hq
  generalize hqd : rdW (m.arr64 IW) (o + j) = q at hq hset hm'
  have hvq : q.toNat = v := by subst hq; simp; omega
  rw [← hP, ← hvq] at htb
  obtain ⟨w, hw, -, -⟩ := decTbl_name htb
  have hw1 : erecP m (q + ProjTbl.structName).toNat = some w := by
    have := erecP_lt64 hw
    rw [UInt64.toNat_add]
    rw [Nat.mod_eq_of_lt (by omega)]; exact hw
  have hrd : erecRd m (q + ProjTbl.structName) = w := erecRd_of hw1
  rw [hrd] at hset hm'
  have hst := IndexR.insertTable hI.idx htb hw hr hset
  refine ⟨by omega, ?_, ?_⟩
  · rw [hs, take_succ_of ts j.toNat hx, insT_snoc, hm']; exact hst
  · have hf1 : MemFrame TixA [] m m' := by
      rw [hm']; split
      · exact baseTblSet_frame _ _ _ _
      · exact MemFrame.refl _ _ _
    exact hI.frame.trans hf1

section loops
variable (p : Prog)

theorem idxConstsLoop_spec (hg : p.lookup "base_row_get" = some baseRowGetL)
    (hs : p.lookup "base_row_set" = some baseRowSetL) {m₀ : Mem} {I : IStreamIndex}
    {cs : List IConstantInfo} {o l : Word}
    (hL : decPL m₀ (fun q => decCI (erecP m₀) q) o.toNat cs.length = some cs) (hl : cs.length = l.toNat)
    (hc : 128 < (m₀.arr64 CTL).size) (hsz : (m₀.arr64 IW).size < 2 ^ 64) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ (s.loc 0 = o ∧ s.loc 1 = l ∧ s.loc 2 = 0 ∧ IcInv m₀ I cs 0 s.mem)⦄
    exec p k idxConstsLoop
    ⦃fun r s' => r = .normal ∧ IcInv m₀ I cs cs.length s'.mem; ⊤⦄ :=
  L.Triple.forUp_pre rfl (fun s => s.loc 0 = o ∧ s.loc 1 = l ∧ (s.loc 2).toNat ≤ l.toNat ∧
      IcInv m₀ I cs (s.loc 2).toNat s.mem)
    (fun ⟨h0, h1, h2, h3⟩ => ⟨h0, h1, by rw [h2]; simp, by rw [h2]; exact h3⟩)
    (fun s ⟨h0, h1, h2, h3⟩ hlt => by
      have : (s.loc 2).toNat = l.toNat := by
        rw [h1] at hlt; have : ¬ (s.loc 2).toNat < l.toNat := hlt; omega
      exact ⟨rfl, by rw [hl, ← this]; exact h3⟩)
    (fun k' s₁ => by
      vcgen [step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs,
        baseRowGet_spec p hg k', baseRowSet_spec p hs k', st64]
      all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons,
        St.setLocs_nil, Cmp.eval, BinOp.eval, rd64_rdWC, beq_iff_eq, LoopPost_normal] at *
      all_goals subst_vars
      all_goals simp (config := { decide := true }) only [ite_true, ite_false, List.headD_cons, List.tail_cons,
        decide_eq_true_eq, LocEq] at *
      case vc1 =>
        rename_i s2 s1 s _ hinv hm1 hnx hloc1 hc0 hset
        obtain ⟨⟨h0, h1, -, hI⟩, hlt⟩ := hinv
        obtain ⟨hmem, hloc2, ht⟩ := hset
        have e1 := congrFun hloc1; have e2 := congrFun hloc2
        simp only [St.setLoc_loc] at e1 e2
        simp only [e1, e2, ite_true, hm1] at ht hmem ⊢
        rw [h1] at hlt
        subst h0 h1
        refine ⟨by simp, by simp, ?_⟩
        refine icLoop_close hL hl hc hsz hlt hI hnx ?_ (fun _ => ?_)
        · simp (config := { decide := true }) only [erecRd, ite_true, ite_false,
            hc0]; exact hmem
        · simp (config := { decide := true }) only [erecRd,
            ite_false]; exact ht
      case vc2 =>
        rename_i s1 s _ hinv hm hnx hloc hc0
        obtain ⟨⟨h0, h1, -, hI⟩, hlt⟩ := hinv
        have e1 := congrFun hloc
        simp only [St.setLoc_loc] at e1
        simp only [e1, ite_true, hm] at ⊢
        rw [h1] at hlt
        subst h0 h1
        refine ⟨by simp, by simp, ?_⟩
        refine icLoop_close hL hl hc hsz hlt hI hnx ?_ (fun h => absurd h ?_)
        · simp (config := { decide := true }) only [erecRd, ite_false,
            hc0]
        · simpa (config := { decide := true }) only [erecRd, e1, St.setLoc_loc, ite_true,
            ite_false] using hc0) k

theorem idxConstsLoop_step_spec (hg : p.lookup "base_row_get" = some baseRowGetL)
    (hs : p.lookup "base_row_set" = some baseRowSetL) {m₀ : Mem} {I : IStreamIndex}
    {cs : List IConstantInfo} {o l : Word}
    (hL : decPL m₀ (fun q => decCI (erecP m₀) q) o.toNat cs.length = some cs) (hl : cs.length = l.toNat)
    (hc : 128 < (m₀.arr64 CTL).size) (hsz : (m₀.arr64 IW).size < 2 ^ 64) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ (s.loc 0 = o ∧ s.loc 1 = l ∧ s.loc 2 = 0 ∧ IcInv m₀ I cs 0 s.mem)⦄
    step p (exec p k) idxConstsLoop
    ⦃fun r s' => r = .normal ∧ IcInv m₀ I cs cs.length s'.mem; ⊤⦄ :=
  Triple.step_exec (idxConstsLoop_spec p hg hs hL hl hc hsz (k + 1) s₀)

/-- **`idx_consts(o, l)` is `insertConsts`** over the constant records the `IW` slice `(o, l)`
decodes to: `IndexR` at the index with them inserted from the next counter, only the stream
index's constant rows and `CTL[128]` written. -/
@[refines ConRon.Arena.insertConsts]
theorem idxConsts_spec (hp : p.lookup "idx_consts" = some idxConstsL)
    (hg : p.lookup "base_row_get" = some baseRowGetL)
    (hs : p.lookup "base_row_set" = some baseRowSetL) (n : Nat) (s₀ : St) {I : IStreamIndex}
    {cs : List IConstantInfo} (o l : Word) (hI : IndexR s₀.mem I)
    (hL : decPL s₀.mem (fun q => decCI (erecP s₀.mem) q) o.toNat l.toNat = some cs)
    (hc : 128 < (s₀.mem.arr64 CTL).size) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64)
    (hn : I.next < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "idx_consts" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [0] ∧ IndexR s'.mem (insC I cs) ∧
      MemFrame EixA [128] s₀.mem s'.mem ∧ (insC I cs).next < 2 ^ 32; ⊤⦄ := by
  have hl : cs.length = l.toNat := L.Ind.decPL_length (m := s₀.mem) hL
  rw [← hl] at hL
  have hI0 : IcInv s₀.mem I cs 0 s₀.mem :=
    ⟨by simpa [insC_nil] using hI, MemFrame.refl _ _ _, by simpa [insC_nil] using hn⟩
  rw [invoke_eq _ hp]
  simp only [callFn, idxConstsL_eq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalArgs, setLoc, idxConstsLoop_step_spec p hg hs (I := I) hL hl hc hsz n]
    all_goals try simp only [St.setLoc_loc, L.St.setLoc_mem, Locals.init_cons_zero, Locals.init_cons_succ,
      Sig.retVal, LocEq, ite_true] at *
    all_goals first
      | decide
      | rfl
      | exact hI0
      | (rename_i h; simpa [List.take_length] using h.idx)
      | (rename_i h; exact h.frame)
      | (rename_i h; have := h.nlt; rwa [List.take_length] at this)

theorem idxTablesLoop_spec (hg : p.lookup "tbl_base_get" = some tblBaseGetL)
    (hs : p.lookup "tbl_base_set" = some tblBaseSetL) {m₀ : Mem} {I : IStreamIndex}
    {ts : List IProjTable} {o l r : Word}
    (hL : decPL m₀ (fun q => decTbl (erecP m₀) q) o.toNat ts.length = some ts) (hl : ts.length = l.toNat)
    (hsz : (m₀.arr64 IW).size < 2 ^ 64) (hr : r.toNat + 1 < 2 ^ 64) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ (s.loc 0 = o ∧ s.loc 1 = l ∧ s.loc 2 = r ∧ s.loc 3 = 0 ∧
      ItInv m₀ I r.toNat ts 0 s.mem)⦄
    exec p k idxTablesLoop
    ⦃fun r' s' => r' = .normal ∧ ItInv m₀ I r.toNat ts ts.length s'.mem; ⊤⦄ :=
  L.Triple.forUp_pre rfl (fun s => s.loc 0 = o ∧ s.loc 1 = l ∧ s.loc 2 = r ∧ (s.loc 3).toNat ≤ l.toNat ∧
      ItInv m₀ I r.toNat ts (s.loc 3).toNat s.mem)
    (fun ⟨h0, h1, h2, h3, h4⟩ => ⟨h0, h1, h2, by rw [h3]; simp, by rw [h3]; exact h4⟩)
    (fun s ⟨_, h1, _, h3, h4⟩ hlt => by
      have : (s.loc 3).toNat = l.toNat := by
        rw [h1] at hlt; have : ¬ (s.loc 3).toNat < l.toNat := hlt; omega
      exact ⟨rfl, by rw [hl, ← this]; exact h4⟩)
    (fun k' s₁ => by
      vcgen [step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs,
        tblBaseGet_spec p hg k', tblBaseSet_spec p hs k', st64]
      all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons,
        St.setLocs_nil, Cmp.eval, BinOp.eval, rd64_rdWC, beq_iff_eq, LoopPost_normal] at *
      all_goals subst_vars
      all_goals simp (config := { decide := true }) only [ite_true, ite_false, List.headD_cons, List.tail_cons, LocEq] at *
      case vc1 =>
        rename_i s2 s1 s hinv hm1 hloc1 hc0 hset
        obtain ⟨⟨h0, h1, h2, -, hI⟩, hlt⟩ := hinv
        obtain ⟨hmem, hloc2, ht⟩ := hset
        have e1 := congrFun hloc1; have e2 := congrFun hloc2
        simp only [St.setLoc_loc] at e1 e2
        simp only [e1, e2, ite_true, hm1] at ht hmem ⊢
        rw [h1] at hlt
        subst h0 h1 h2
        refine ⟨by simp, by simp, by simp, ?_⟩
        refine itLoop_close hL hl hsz hr hlt hI ?_ (fun _ => ?_)
        · simp (config := { decide := true }) only [erecRd, ite_true, ite_false,
            hc0]; exact hmem
        · simp (config := { decide := true }) only [erecRd,
            ite_false]; exact ht
      case vc2 =>
        rename_i s1 s hinv hm hloc hc0
        obtain ⟨⟨h0, h1, h2, -, hI⟩, hlt⟩ := hinv
        have e1 := congrFun hloc
        simp only [St.setLoc_loc] at e1
        simp only [e1, hm] at ⊢
        rw [h1] at hlt
        subst h0 h1 h2
        refine ⟨by simp, by simp, by simp, ?_⟩
        refine itLoop_close hL hl hsz hr hlt hI ?_ (fun h => absurd h ?_)
        · simp (config := { decide := true }) only [erecRd, ite_false,
            hc0]
        · simpa (config := { decide := true }) only [erecRd, e1, St.setLoc_loc, ite_true,
            ite_false] using hc0) k

theorem idxTablesLoop_step_spec (hg : p.lookup "tbl_base_get" = some tblBaseGetL)
    (hs : p.lookup "tbl_base_set" = some tblBaseSetL) {m₀ : Mem} {I : IStreamIndex}
    {ts : List IProjTable} {o l r : Word}
    (hL : decPL m₀ (fun q => decTbl (erecP m₀) q) o.toNat ts.length = some ts) (hl : ts.length = l.toNat)
    (hsz : (m₀.arr64 IW).size < 2 ^ 64) (hr : r.toNat + 1 < 2 ^ 64) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ (s.loc 0 = o ∧ s.loc 1 = l ∧ s.loc 2 = r ∧ s.loc 3 = 0 ∧
      ItInv m₀ I r.toNat ts 0 s.mem)⦄
    step p (exec p k) idxTablesLoop
    ⦃fun r' s' => r' = .normal ∧ ItInv m₀ I r.toNat ts ts.length s'.mem; ⊤⦄ :=
  Triple.step_exec (idxTablesLoop_spec p hg hs hL hl hsz hr (k + 1) s₀)

/-- **`idx_tables(o, l, r)` is `insertTables`** over the table records the `IW` slice `(o, l)`
decodes to, at record position `r`: `IndexR` at the index with them inserted, only the stream
index's table rows written. -/
@[refines ConRon.Arena.insertTables]
theorem idxTables_spec (hp : p.lookup "idx_tables" = some idxTablesL)
    (hg : p.lookup "tbl_base_get" = some tblBaseGetL)
    (hs : p.lookup "tbl_base_set" = some tblBaseSetL) (n : Nat) (s₀ : St) {I : IStreamIndex}
    {ts : List IProjTable} (o l r : Word) (hI : IndexR s₀.mem I)
    (hL : decPL s₀.mem (fun q => decTbl (erecP s₀.mem) q) o.toNat l.toNat = some ts)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hr : r.toNat + 1 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "idx_tables" [o, l, r]
    ⦃fun r' s' => LocEq s' s₀ ∧ r' = [0] ∧ IndexR s'.mem (insT I r.toNat ts) ∧
      MemFrame TixA [] s₀.mem s'.mem; ⊤⦄ := by
  have hl : ts.length = l.toNat := L.Ind.decPL_length (m := s₀.mem) hL
  rw [← hl] at hL
  have hI0 : ItInv s₀.mem I r.toNat ts 0 s₀.mem := ⟨by simpa [insT_nil] using hI, MemFrame.refl _ _ _⟩
  rw [invoke_eq _ hp]
  simp only [callFn, idxTablesL_eq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalArgs, setLoc, idxTablesLoop_step_spec p hg hs (I := I) hL hl hsz hr n]
    all_goals simp only [St.setLoc_loc, L.St.setLoc_mem, Locals.init_cons_zero, Locals.init_cons_succ,
      Sig.retVal, LocEq, ite_true] at *
    all_goals first
      | decide
      | rfl
      | exact hI0
      | (rename_i h; simpa [List.take_length] using h.idx)
      | (rename_i h; exact h.frame)

end loops

end L.Arena
