module

public import ConAgua.Arena.BasisL
public import ConAgua.Rom.CIReadSpec
public import ConAgua.Front.StateDR
public import ConAgua.Arena.StageTLift
public import ConRon.Bridge.Checker.Basis
public import ConAgua.Arena.QuotRulesT
public import ConAgua.Arena.LeafFns
public import ConAgua.Arena.IndPartsSpec.PartsConsPL
import ConAgua.Arena.QuotRecW
import ConAgua.Arena.IndCopy2
import ConAgua.Arena.RecCheckSpec.ErToIwWStage
import ConAgua.Arena.IndSumSpec.SoaW
import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.RecGenSpec.StabDecCRDecB
import ConAgua.Arena.IndTwin
import ConAgua.Arena.IndRealAbs
import ConAgua.Arena.DeclAndPinIndRef
import ConAgua.Arena.DeclAndPinIndDec
import ConAgua.Arena.InferLeaves
import ConAgua.Arena.IlpRd
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Inv
import all ConAgua.Arena.IndIface

@[expose] public section

/-!
# The pinned basis blocks' refinements: the statements (lane `ronsync2`, stage 3)

The entry points of `BasisL.lean` that the stream index's `decl_constants` (`IndDeclConsts.lean`)
and the declaration arms call, in the ROM readers' style (`L.Rom.RomRef`: from `StageR` and the
arguments' decodings, the twin's run, `KeepPost` after it):

* `basis_name_hit(o, l)` refines `basisNameHit block` (`BasisNameHitRef`; the result `(hit,
  kind)` as `decHit`);
* `basis_at_block(k, o, l)` refines `BasisKind.atBlock (basisOfW k) block` (`BasisAtBlockRef`; an
  `IW` slice of constant records, `decRBlk`);
* `quot_at(k.slot, q)` refines `quotAt k cv` (`QuotAtRef`; a constant record, `decRCI`).

The block is an `EREC` slice of record pointers (`ind_block_to_erec`'s post: `BlockAt`). The
quotient readers read `rom_basis_decls(4)`, whose refinement wants `Quot`'s `sortZ` names under
`dn` (`L.Rom.RomQuotRef`): `quot_at`'s pre has them.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena L.Rom

/-- **A block at an `EREC` slice** of constant-record pointers `(o, l)`, below the record pool's
top (`ind_block_to_erec`'s post). -/
def BlockAt (o l : Word) (block : List IConstantInfo) (m : Mem) : Prop :=
  L.Front.decCIsR (erecP m) o.toNat l.toNat = some block ∧ o.toNat + l.toNat ≤ erTop m

/-- `basis_name_hit`'s result `Option BasisKind` as `(hit, kind)`: the kind a word below `4`
(`basisOfW`). -/
def decHit (_m : Mem) (r : List Word) : Option ConLeche.BasisKind → Prop
  | none => r.headD 0 = 0
  | some k => r.headD 0 = 1 ∧ (r.tail.headD 0).toNat < 4 ∧ basisOfW (r.tail.headD 0).toNat = k

section specs
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- **`basis_name_hit(o, l)` refines `basisNameHit block`.** -/
def BasisNameHitRef : Prop := ∀ (o l : Word) (block : List IConstantInfo),
  RomRef p "basis_name_hit" [o, l]
    (fun m a => StageT dn vis fe m a ∧ ConRon.Bridge.StateOK a ∧ ConRon.Bridge.ReadOK a ∧
      BlockAt o l block m ∧ ∃ bs, Frontend.denoteCIList a.store block = some bs)
    (ConRon.Arena.basisNameHit block) (KeepPostT dn vis fe decHit)

/-- **`basis_at_block(k, o, l)` refines `BasisKind.atBlock (basisOfW k) block`**, for the four
block kinds `basis_name_hit` returns; the result slice lies below the pool's top (`at_block_go`
returns `(0, 0)` or an `sl_cons` slice), also when it is empty. -/
def BasisAtBlockRef : Prop := ∀ (k o l : Word) (block : List IConstantInfo), k.toNat < 4 →
  RomRef p "basis_at_block" [k, o, l]
    (fun m a => StageT dn vis fe m a ∧ ConRon.Bridge.StateOK a ∧ ConRon.Bridge.ReadOK a ∧
      BlockAt o l block m ∧ ∃ bs, Frontend.denoteCIList a.store block = some bs)
    (ConRon.Arena.BasisKind.atBlock (basisOfW k.toNat) block)
    (fun m m' a r x => KeepPostT dn vis fe (decRBlk dn) m m' a r x ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m')

/-- **`quot_at(k.slot, q)` refines `quotAt k cv`** (`q` an `EREC` constant value), from a
well-formed twin state that names `Quot`'s `sortZ` names through `dn`. -/
def QuotAtRef : Prop := ∀ (k : ConLeche.QuotKind) (q : Word) (cv : IConstantVal),
  RomRef p "quot_at" [UInt64.ofNat k.slot, q]
    (fun m a => StageT dn vis fe m a ∧ ConRon.Bridge.StateOK a ∧ ConRon.Bridge.ReadOK a ∧
      NamesDn dn a quotNames ∧ decCV (erecP m) q.toNat = some cv ∧
      ∃ c, Frontend.denoteCV a.store cv = some c)
    (ConRon.Arena.quotAt k cv) (KeepPostT dn vis fe (decRCI dn))

/-- The three, at every stage. -/
structure BasisRefs : Prop where
  nameHit : ∀ dn vis fe, BasisNameHitRef p dn vis fe
  atBlock : ∀ dn vis fe, BasisAtBlockRef p dn vis fe
  quotAt : ∀ dn vis fe, QuotAtRef p dn vis fe

end specs

/-- **The program `BasisL.lean`'s entry points run in**: its functions, the ROM readers'
refinements (`RomRefs`), the pin-at-names machinery's program facts (`RulesProg`: `ci_at_lps`,
`er_to_iw`, `sl_cons`, …) and the leaves' write set (`rom_basis_decls` is a leaf). Consumers take
`BasisRefs`, so this bundle may grow. -/
structure BasisLProg (p : Prog) : Prop where
  fns : ProgHas p basisFns
  rom : RomRefs p
  rules : RulesProg p
  leaf : LeafClosed p
  qp : p.lookup "quot_pin" = some quotPin
  nh : p.lookup "basis_name_hit" = some basisNameHit
  nhg : p.lookup "basis_name_hit_go" = some basisNameHitGo
  bne : p.lookup "block_names_eq" = some blockNamesEq
  abg : p.lookup "at_block_go" = some atBlockGo
  bab : p.lookup "basis_at_block" = some basisAtBlock

/-! ## The proofs -/

/-- The decoder of a slice of constant-record pointers (`basisDec`'s, as a `PSlR` decoder). -/
abbrev ciF : Mem → Nat → Option IConstantInfo := fun m q => decCI (erA m) q

theorem ciF_mono : ∀ q, OMono (fun m => ciF m q) := fun _ => ⟨fun _ _ _ he h => he.2.decCI h⟩

theorem decB_ciF {m : Mem} {q : Nat} {x : IConstantInfo} :
    DecB (fun m => ciF m q) m x ↔ decCI (erecP m) q = some x := by
  show decCI (erA (truncM m)) q = some x ↔ _
  rw [truncM_erA]; rfl

/-- **`er_to_iw` over any `EREC` slice whose words exist**: the copy at the old `IW` top. -/
theorem erToIwW_ptrs {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : erToIwW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hrd : ∀ j < l.toNat, ∃ v, erecP m (o.toNat + j) = some v) :
    r = [rdW (m.arr64 CTL) 200, l] ∧
    (∀ j < l.toNat, iwA m' ((rdW (m.arr64 CTL) 200).toNat + j) = erecP m (o.toNat + j)) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ m'.arr64 EREC = m.arr64 EREC ∧
    (rdW (m.arr64 CTL) 200).toNat + l.toNat = iwTop m' ∧ iwTop m' ≤ (m'.arr64 IW).size := by
  have hol : o.toNat + l.toNat ≤ 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos l.toNat with h0 | hpos
    · have := o.toNat_lt; omega
    · obtain ⟨v, hv⟩ := hrd (l.toNat - 1) (by omega)
      have : o.toNat + (l.toNat - 1) < 2 ^ 64 := by
        rcases Nat.lt_or_ge (o.toNat + (l.toNat - 1)) (2 ^ 64) with h' | h'
        · exact h'
        · unfold erecP at hv; rw [if_neg (by omega)] at hv; cases hv
      omega
  simp only [erToIwW] at h
  cases hal : allocW m l with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  rcases hcp : erCopyW (n - 1) m1 q o l with _ | m2 <;> simp only [hcp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq hm1
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hIW := allocMem_IW m l
  have hR : ∀ a, erRd (allocMem m l) a = erRd m a := fun a => by
    simp only [allocMem, erRd]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by rw [tierA_EREC]; split <;> decide)]
  have hEE : (allocMem m l).arr64 EREC = m.arr64 EREC := by
    simp only [allocMem]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  obtain ⟨hA, hS, hG⟩ := erCopyW_get (n - 1) _ _ _ _ _ hcp hol
    (by rw [hIW]; exact hroom) (by rw [hIW]; exact hsz)
  rw [hIW] at hS hG
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m l).trans (copy_frame hA (by rw [hS, hIW]))
  have htop : rdW (m2.arr64 CTL) 200 = q + l := by
    rw [hA CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + l).toNat = q.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  refine ⟨rfl, ?_, ?_, hfr, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨v, hv⟩ := hrd j hj
    simp only [iwA, aread_apply, hG]
    rw [ite_eq_left (by omega), hR, show q.toNat + j - q.toNat = j by omega]
    have e : (UInt64.ofNat (o.toNat + j)).toNat = o.toNat + j := by simp; omega
    have hv' : erecP m (UInt64.ofNat (o.toNat + j)).toNat = some v := by rw [e]; exact hv
    rw [(erRd_of_erecP hv').1, hv]
  · refine iwGrow_of_frame hfr (N := l) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hG, ite_eq_right (by omega)]
  · rw [hA EREC (by decide), hEE]
  · simp only [iwTop, htop, hsum]
  · simp only [iwTop, htop, hsum, hS]; omega

/-- A slice of constant records over a reader stays decoded as the reader grows. -/
theorem decCIsR_ext {a b : Nat → Option Word} (he : ArrExt a b) {o l : Nat}
    {xs : List IConstantInfo} (h : L.Front.decCIsR a o l = some xs) :
    L.Front.decCIsR b o l = some xs := by
  refine mapM_imp _ _ h fun j _ y hy => ?_
  simp only [bind, Option.bind_eq_some_iff] at hy ⊢
  obtain ⟨v, hv, hy⟩ := hy
  exact ⟨v, he.nat? hv, he.decCI hy⟩

/-- **`er_to_iw` of a block's `EREC` pointer slice** under `StageR`: the `IW` copy decodes, below
the tops, to the block. -/
theorem erToIwW_blkR {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {o l : Word}
    {r : List Word} {block : List IConstantInfo}
    (h : erToIwW n m o l = some (r, m')) (hS : StageR vis fe m a)
    (hd : L.Front.decCIsR (erecP m) o.toNat l.toNat = some block) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ r = [r.headD 0, l] ∧
      PSlR ciF block (r.headD 0) l m' := by
  have hrd : ∀ j < l.toNat, ∃ v, erecP m (o.toNat + j) = some v := by
    intro j hj
    have := L.Ind.mapM_opt_get _ (List.range l.toNat) block hd j (by simpa using hj)
    simp only [List.getElem_range] at this
    cases e : erecP m (o.toNat + j) with
    | none => simp [nat?, e] at this
    | some v => exact ⟨v, rfl⟩
  obtain ⟨hr, hw, hg, hf, -, ht, hroom⟩ := erToIwW_ptrs h hS.iw.iwSize hS.iw.ctl hrd
  have hEr : erecP m' = erecP m := erecP_frame hf (by decide) (by decide) (by decide) (by decide)
  subst hr
  refine ⟨⟨CheckR.frame_iw hf hS.check, hS.iw.of_iw hf hroom⟩, hg, hf, rfl, ?_, by simp; omega⟩
  show decPL (truncM m') (fun q => decCI (erA (truncM m')) q) _ _ = some block
  simp only [List.headD_cons]
  rw [decPL_truncM_of (f := fun q => decCI (erecP m') q) (fun j hj => by omega)
    (fun _ _ _ _ => by rw [truncM_erA]; rfl)]
  rw [← hd]
  unfold decPL L.Front.decCIsR
  refine mapM_congr_range _ fun j hj => ?_
  have hj' := List.mem_range.mp hj
  simp only [iwN, nat?, hw j hj', hEr]

/-- A block the ROM reader returns (nonempty) is a pointer slice below the tops. -/
theorem romBlk_pslr {dn : NIdx → Option ConLeche.Name} {m : Mem} {r : List Word}
    {blk : List IConstantInfo} (hD : decRBlk dn m r blk) (hl : blk.length ≠ 0) :
    PSlR ciF blk (r.headD 0) (r.tail.headD 0) m :=
  ⟨hD.1, (decRBlk_canon hD hl).2⟩

theorem basisDecls_len {k : Nat} (hk : k < 4) :
    (ConLeche.BasisKind.decls (basisOfW k)).length ≠ 0 := by
  match k, hk with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide

/-! ### `block_names_eq` -/

/-- **`block_names_eq` compares the two slices' names** (pure). -/
theorem blockNamesEqW_ok : ∀ (n : Nat) (m m' : Mem) (ao al bo bl : Word) (A B : List IConstantInfo)
    (r : List Word), (m.arr64 IW).size < 2 ^ 64 → PSlR ciF A ao al m → PSlR ciF B bo bl m →
    blockNamesEqW n m ao al bo bl = some (r, m') →
    m' = m ∧ r = [r.headD 0] ∧ (r.headD 0 ≠ 0 ↔ blockNames A = blockNames B) := by
  intro n
  induction n with
  | zero => intro m m' ao al bo bl A B r _ _ _ h; simp [blockNamesEqW] at h
  | succ n ih =>
  intro m m' ao al bo bl A B r hsz hA hB h
  have hlA := L.Ind.decPL_length (truncM m) hA.dec
  have hlB := L.Ind.decPL_length (truncM m) hB.dec
  simp only [blockNamesEqW] at h
  by_cases h1 : al ≠ bl
  · rw [if_pos h1] at h; cases h
    have hne : blockNames A ≠ blockNames B := fun he => h1 (UInt64.toNat_inj.mp (by
      have := congrArg List.length he; simp only [blockNames, List.length_map] at this; omega))
    exact ⟨rfl, rfl, by simpa using hne⟩
  rw [if_neg h1] at h
  have h1' : al = bl := by simpa using h1
  subst h1'
  by_cases h2 : al = 0
  · rw [if_pos h2] at h; cases h
    subst h2
    have hA0 : A = [] := List.eq_nil_of_length_eq_zero (by rw [hlA]; rfl)
    have hB0 : B = [] := List.eq_nil_of_length_eq_zero (by rw [hlB]; rfl)
    subst hA0 hB0
    exact ⟨rfl, rfl, by simp⟩
  rw [if_neg h2] at h
  obtain ⟨x, A', rfl, hx, hA'⟩ := hA.uncons h2 hsz
  obtain ⟨y, B', rfl, hy, hB'⟩ := hB.uncons h2 hsz
  rw [decB_ciF] at hx hy
  obtain ⟨wx, hwx, hwx32, hnx⟩ := decCI_name hx
  obtain ⟨wy, hwy, hwy32, hny⟩ := decCI_name hy
  have ex : erRdT m (rdW (m.arr64 IW) ao + 1) = wx := (erRdOK m).off hwx (by simp)
  have ey : erRdT m (rdW (m.arr64 IW) bo + 1) = wy := (erRdOK m).off hwy (by simp)
  by_cases h3 : wx ≠ wy
  · rw [if_pos (by simpa only [erRdT, ex, ey] using h3)] at h; cases h
    refine ⟨rfl, rfl, by
      simp only [List.headD_cons, ne_eq, not_true_eq_false, false_iff, blockNames, List.map_cons,
        List.cons.injEq, not_and]
      intro he; exact absurd (decI_inj hwx32 hwy32 (hnx ▸ hny ▸ he)) h3⟩
  rw [if_neg (by simpa only [erRdT, ex, ey] using h3)] at h
  have h3' : wx = wy := by simpa using h3
  cases hrec : blockNamesEqW n m (ao + 1) (al - 1) (bo + 1) (al - 1) with
  | none => rw [hrec] at h; simp [blockNamesEqW.k_block_names_eq] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [hrec] at h; simp only [blockNamesEqW.k_block_names_eq, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨rfl, -, hiff⟩ := ih m m2 _ _ _ _ A' B' r2 hsz hA' hB' hrec
  refine ⟨rfl, rfl, ?_⟩
  simp only [List.headD_cons, blockNames, List.map_cons, List.cons.injEq, hnx, hny, h3', true_and]
  simpa only [blockNames] using hiff

/-! ### `basis_name_hit` -/

/-- The kinds `basis_name_hit_go(·, ·, k)` tries. -/
def kindsFrom (k : Nat) : List ConLeche.BasisKind :=
  [ConLeche.BasisKind.eqK, .natK, .emptyK, .falseK].drop k

theorem kindsFrom_succ {k : Nat} (hk : k < 4) : kindsFrom k = basisOfW k :: kindsFrom (k + 1) := by
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

theorem decHit_two {m : Mem} {r : List Word} {x : Option ConLeche.BasisKind} (h : decHit m r x) :
    decHit m [r.headD 0, r.tail.headD 0] x := by
  cases x <;> simpa [decHit] using h

section go
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem basisNameHitGoW_ok (hB : BasisLProg p) (block : List IConstantInfo) (io il : Word) :
    ∀ (n : Nat) (k : Word) (m m' : Mem) (a : AState) (r : List Word),
    k.toNat ≤ 4 → StageT dn vis fe m a → ConRon.Bridge.StateOK a → PSlR ciF block io il m →
    basisNameHitGoW p n m io il k = some (r, m') →
    ∃ x a', (ConRon.Arena.basisNameHitGo block (kindsFrom k.toNat)).run a = .ok (x, a') ∧
      StageT dn vis fe m' a' ∧ IWGrow m m' ∧ decHit m' r x := by
  intro n
  induction n with
  | zero => intro k m m' a r _ _ _ _ h; simp [basisNameHitGoW] at h
  | succ n ih =>
  intro k m m' a r hk hT hok hsl h
  simp only [basisNameHitGoW] at h
  by_cases h4 : 4 ≤ k
  · rw [if_pos h4] at h; cases h
    have : k.toNat = 4 := by have := UInt64.le_iff_toNat_le.mp h4; simp at this; omega
    refine ⟨none, a, ?_, hT, IWGrow.refl m, rfl⟩
    rw [this]; rfl
  rw [if_neg h4] at h
  have hk4 : k.toNat < 4 := by
    have : ¬ (4 : Word).toNat ≤ k.toNat := fun h' => h4 (UInt64.le_iff_toNat_le.mpr h'); simp at this; omega
  cases h1 : callW p n "rom_basis_decls" [k] m with
  | none => rw [h1] at h; simp [basisNameHitGoW.k_rom_basis_decls] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at h; simp only [basisNameHitGoW.k_rom_basis_decls] at h
  obtain ⟨blk, a1, hrun1, hS1, hg1, hD1⟩ := hB.rom.basis dn vis fe k hk4 n m a r1 m1 hT.stage h1
  obtain ⟨hs1, hden1⟩ := ConRon.Bridge.BasisKind.decls_run hok hrun1
  have hf1 : MemFrame leafA leafC m m1 :=
    (run_memFrame hB.leaf (leaf_mem _ rfl) (run_of_callW h1)).1
  have hT1 := hT.of_leafI hS1 hs1 hf1
  have hlen : blk.length ≠ 0 := by
    rw [denoteCIList_length _ _ hden1]; exact basisDecls_len hk4
  have hP1 := romBlk_pslr hD1 hlen
  have hsl1 := hsl.grow ciF_mono hg1
  cases h2 : callW p n "block_names_eq" [r1.headD 0, r1.tail.headD 0, io, il] m1 with
  | none => rw [h2] at h; simp [basisNameHitGoW.k_block_names_eq] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2] at h
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (blockNamesEq_specW p hB.bne n _ (r1.headD 0) (r1.tail.headD 0) io il) h2
  obtain ⟨rfl, hr2, hiff⟩ := blockNamesEqW_ok n m1 _ _ _ _ _ blk block r2 hT1.stage.iw.iwSize hP1 hsl1 hW2
  have hks := kindsFrom_succ hk4
  by_cases he : blockNames blk = blockNames block
  · rw [basisNameHitGoW.k_block_names_eq, if_pos (hiff.mpr he)] at h; cases h
    refine ⟨some (basisOfW k.toNat), a1, ?_, hT1, hg1, by simp [decHit, hk4]⟩
    rw [hks]
    simp only [ConRon.Arena.basisNameHitGo, StateT.run_bind]
    rw [show StateT.run (BasisKind.decls (basisOfW k.toNat)) a = .ok (blk, a1) from hrun1, exb]
    dsimp only; rw [if_pos (by simp [he])]; rfl
  · rw [basisNameHitGoW.k_block_names_eq, if_neg (fun h0 => he (hiff.mp h0))] at h
    cases h3 : basisNameHitGoW p n s2.mem io il (k + 1) with
    | none => rw [h3] at h; simp [basisNameHitGoW.k_basis_name_hit_go] at h
    | some x3 =>
    obtain ⟨r3, m3⟩ := x3
    rw [h3] at h; simp only [basisNameHitGoW.k_basis_name_hit_go, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    obtain ⟨x, a', hrun, hT', hg', hd'⟩ :=
      ih (k + 1) _ m3 a1 r3 (by omega) hT1 hs1.ok hsl1 h3
    refine ⟨x, a', ?_, hT', hg1.trans hg', decHit_two hd'⟩
    rw [hks]
    simp only [ConRon.Arena.basisNameHitGo, StateT.run_bind]
    rw [show StateT.run (BasisKind.decls (basisOfW k.toNat)) a = .ok (blk, a1) from hrun1, exb]
    rw [hk1] at hrun
    dsimp only; rw [if_neg (by simpa using he)]; exact hrun

/-! ### `at_block_go` -/

theorem atBlockGoW_ok (hB : BasisLProg p) :
    ∀ (n : Nat) (m m' : Mem) (a : AState) (po pl co cl : Word) (pins cs : List IConstantInfo)
    (r : List Word), StageT dn vis fe m a → ConRon.Bridge.StateOK a → ConRon.Bridge.ReadOK a →
    PSlR ciF pins po pl m → PSlR ciF cs co cl m →
    (∃ bs, Frontend.denoteCIList a.store pins = some bs) →
    (∃ bs, Frontend.denoteCIList a.store cs = some bs) →
    atBlockGoW p n m po pl co cl = some (r, m') →
    ∃ xs a', (ConRon.Arena.atBlockGo pins cs).run a = .ok (xs, a') ∧ StageT dn vis fe m' a' ∧
      IWGrow m m' ∧ ConRon.Bridge.StateOK a' ∧ ConRon.Bridge.ReadOK a' ∧
      PSlR ciF xs (r.headD 0) (r.tail.headD 0) m' := by
  intro n
  induction n with
  | zero => intro m m' a po pl co cl pins cs r _ _ _ _ _ _ _ h; simp [atBlockGoW] at h
  | succ n ih =>
  intro m m' a po pl co cl pins cs r hT hok hr hP hC hdP hdC h
  have hsz := hT.stage.iw.iwSize
  simp only [atBlockGoW] at h
  by_cases h0 : pl = 0 ∨ cl = 0
  · rw [if_pos h0] at h; cases h
    have hnil : ConRon.Arena.atBlockGo pins cs = pure [] := by
      rcases h0 with rfl | rfl
      · have : pins = [] := List.eq_nil_of_length_eq_zero (by
          rw [L.Ind.decPL_length (truncM m) hP.dec]; rfl)
        subst this; rfl
      · have : cs = [] := List.eq_nil_of_length_eq_zero (by
          rw [L.Ind.decPL_length (truncM m) hC.dec]; rfl)
        subst this; cases pins <;> rfl
    refine ⟨[], a, by rw [hnil]; rfl, hT, IWGrow.refl m, hok, hr, PSlR.nil _ _⟩
  rw [if_neg h0] at h
  have hpl : pl ≠ 0 := fun e => h0 (Or.inl e)
  have hcl : cl ≠ 0 := fun e => h0 (Or.inr e)
  obtain ⟨pin, pins', rfl, hpin, hP'⟩ := hP.uncons hpl hsz
  obtain ⟨c, cs', rfl, hc, hC'⟩ := hC.uncons hcl hsz
  rw [decB_ciF] at hpin hc
  obtain ⟨dp, dps, hdp, hdps, -⟩ := ConRon.Bridge.denoteCIList_cons hdP.choose_spec
  obtain ⟨dc, dcs, hdc, hdcs, -⟩ := ConRon.Bridge.denoteCIList_cons hdC.choose_spec
  -- the record's names
  have hcv := decCI_cvA (q := rdW (m.arr64 IW) co) hc
  obtain ⟨w0, hw0⟩ := decCV_def hcv 3 (by omega)
  have hlt := erecP_lt64 hw0
  have hq1 : (rdW (m.arr64 IW) co + 1).toNat = (rdW (m.arr64 IW) co).toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  rw [← hq1] at hcv
  obtain ⟨hsl, -⟩ := decCV_rdq (erRdOK m) hcv
  rw [word_add11, word_add12] at hsl
  have hps := (ConRon.Bridge.denoteCV_inv (ConRon.Bridge.denoteCI_toConstantVal hdc)).2.1
  cases h1 : callW p n "ci_at_lps" [rdW (m.arr64 IW) po, erRdT m (rdW (m.arr64 IW) co + 2),
      erRdT m (rdW (m.arr64 IW) co + 3)] m with
  | none => rw [h1] at h; simp [atBlockGoW.k_ci_at_lps] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at h; simp only [atBlockGoW.k_ci_at_lps] at h
  obtain ⟨x, a1, hrun1, hT1, hg1, hx1⟩ :=
    (ciAtLpsSim_of hB.rules.toCiProg (rulesAtSim_of hB.rules)).ci n vis fe m a _ _ _ pin
      c.toConstantVal.levelParams _ dp hT hok hr hpin hdp hsl hps r1 m1 h1
  obtain ⟨hst1, -⟩ := ConRon.Bridge.IConstantInfo.atLps_run hok hr hdp hps hrun1
  cases h2 : atBlockGoW p n m1 (po + 1) (pl - 1) (co + 1) (cl - 1) with
  | none => rw [h2] at h; simp [atBlockGoW.k_at_block_go] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2] at h; simp only [atBlockGoW.k_at_block_go] at h
  obtain ⟨xs, a2, hrun2, hT2, hg2, hok2, hr2, hX2⟩ :=
    ih m1 m2 a1 _ _ _ _ pins' cs' r2 hT1 hst1.ok hst1.read (hP'.grow ciF_mono hg1)
      (hC'.grow ciF_mono hg1) ⟨_, ConRon.Bridge.denoteCIList_mono hst1.ext _ _ hdps⟩
      ⟨_, ConRon.Bridge.denoteCIList_mono hst1.ext _ _ hdcs⟩ h2
  cases h3 : callW p n "sl_cons" [r1.headD 0, r2.headD 0, r2.tail.headD 0] m2 with
  | none => rw [h3] at h; simp [atBlockGoW.k_sl_cons] at h
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3] at h; simp only [atBlockGoW.k_sl_cons, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (slCons_specW p hB.rules.iwAlloc hB.rules.iwCopy hB.rules.slCons n _ _ _ _) h3
  obtain ⟨hS3, hg3, hX3, -⟩ := consW_pslr ciF_mono hW3 hT2.stage hX2
    (decB_ciF.mpr (ArrExt.decCI hg2.ext hx1))
  refine ⟨x :: xs, a2, ?_, StageT.of_iw hT2 hS3 (consW_iwFrame hW3), hg1.trans (hg2.trans hg3),
    hok2, hr2, by simpa using hX3⟩
  simp only [ConRon.Arena.atBlockGo, StateT.run_bind, hrun1, exb, hrun2]
  rfl

end go

/-- **The basis entry points refine the twin.** -/
theorem basisRefs_of {p : Prog} (hB : BasisLProg p) : BasisRefs p := by
  refine ⟨fun dn vis fe => ?_, fun dn vis fe => ?_, fun dn vis fe => ?_⟩
  · -- `basis_name_hit`
    rintro o l block n m a r m' ⟨hT, hok, -, hblk, -⟩ h
    obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (basisNameHit_specW p hB.nh n _ o l) h
    cases n with
    | zero => simp [basisNameHitW] at hW
    | succ n =>
    simp only [basisNameHitW] at hW
    cases h1 : callW p n "er_to_iw" [o, l] m with
    | none => rw [h1] at hW; simp [basisNameHitW.k_er_to_iw] at hW
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1] at hW; simp only [basisNameHitW.k_er_to_iw] at hW
    obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (erToIw_specW p hB.rules.iwAlloc hB.rules.erCopy hB.rules.erToIw n _ o l) h1
    obtain ⟨hS1, hg1, hf1, hr1, hsl⟩ := erToIwW_blkR hW1 hT.stage hblk.1
    have hT1 := StageT.of_iw hT hS1 hf1
    cases h2 : callW p n "basis_name_hit_go" [r1.headD 0, r1.tail.headD 0, 0] s1.mem with
    | none => rw [h2] at hW; simp [basisNameHitW.k_basis_name_hit_go] at hW
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
      (basisNameHitGo_specW p hB.nhg n _ _ _ 0) h2
    rw [h2] at hW; simp only [basisNameHitW.k_basis_name_hit_go, Option.some.injEq,
      Prod.mk.injEq] at hW
    obtain ⟨rfl, hm⟩ := hW
    rw [← hm]
    rw [hr1] at hW2
    obtain ⟨x, a', hrun, hT', hg', hd'⟩ :=
      basisNameHitGoW_ok hB block _ l n 0 _ _ a r2 (by decide) hT1 hok hsl hW2
    exact ⟨x, a', hrun, hT', hg1.trans hg', decHit_two hd'⟩
  · -- `basis_at_block`
    rintro k o l block hk n m a r m' ⟨hT, hok, hr, hblk, hden⟩ h
    obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (basisAtBlock_specW p hB.bab n _ k o l) h
    cases n with
    | zero => simp [basisAtBlockW] at hW
    | succ n =>
    simp only [basisAtBlockW] at hW
    cases h1 : callW p n "rom_basis_decls" [k] m with
    | none => rw [h1] at hW; simp [basisAtBlockW.k_rom_basis_decls] at hW
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1] at hW; simp only [basisAtBlockW.k_rom_basis_decls] at hW
    obtain ⟨blk, a1, hrun1, hS1, hg1, hD1⟩ := hB.rom.basis dn vis fe k hk n m a r1 m1 hT.stage h1
    obtain ⟨hs1, hden1⟩ := ConRon.Bridge.BasisKind.decls_run hok hrun1
    have hf1 : MemFrame leafA leafC m m1 :=
      (run_memFrame hB.leaf (leaf_mem _ rfl) (run_of_callW h1)).1
    have hT1 := hT.of_leafI hS1 hs1 hf1
    have hP1 := romBlk_pslr hD1 (by rw [denoteCIList_length _ _ hden1]; exact basisDecls_len hk)
    have hr1 := (ConRon.Bridge.RStep.of_istep hs1 hr)
    cases h2 : callW p n "er_to_iw" [o, l] m1 with
    | none => rw [h2] at hW; simp [basisAtBlockW.k_er_to_iw] at hW
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    rw [h2] at hW; simp only [basisAtBlockW.k_er_to_iw] at hW
    obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (erToIw_specW p hB.rules.iwAlloc hB.rules.erCopy hB.rules.erToIw n _ o l) h2
    obtain ⟨hS2, hg2, hf2, hr2, hsl⟩ := erToIwW_blkR hW2 hT1.stage (decCIsR_ext hg1.ext hblk.1)
    have hT2 := StageT.of_iw hT1 hS2 hf2
    cases h3 : callW p n "at_block_go" [r1.headD 0, r1.tail.headD 0, r2.headD 0, r2.tail.headD 0]
        s2.mem with
    | none => rw [h3] at hW; simp [basisAtBlockW.k_at_block_go] at hW
    | some x3 =>
    obtain ⟨r3, m3⟩ := x3
    obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
      (atBlockGo_specW p hB.abg n _ _ _ _ _) h3
    rw [h3] at hW; simp only [basisAtBlockW.k_at_block_go, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, hm⟩ := hW
    rw [← hm]
    rw [hr2] at hW3
    obtain ⟨bs, hbs⟩ := hden
    obtain ⟨xs, a', hrun, hT', hg', -, -, hX⟩ :=
      atBlockGoW_ok hB n _ _ a1 _ _ _ _ blk block r3 hT2 hr1.ok hr1.read (hP1.grow ciF_mono hg2) hsl
        ⟨_, hden1⟩ ⟨_, ConRon.Bridge.denoteCIList_mono hr1.ext _ _ hbs⟩ hW3
    refine ⟨xs, a', ?_, ⟨hT', hg1.trans (hg2.trans hg'), ⟨hX.dec, rfl⟩⟩, hX.bound⟩
    simp only [ConRon.Arena.BasisKind.atBlock, StateT.run_bind]
    rw [show StateT.run (BasisKind.decls (basisOfW k.toNat)) a = .ok (blk, a1) from hrun1]
    exact hrun
  · -- `quot_at`
    rintro k q cv n m a r m' ⟨hT, hok, hr, hnd, hq, c, hc⟩ h
    have hqd : QuotDn dn := by
      obtain ⟨x, hx1, -⟩ := hnd (.str .anonymous "u") (by simp [L.Rom.quotNames]); exact ⟨x, hx1⟩
    obtain ⟨ci, a', hrun, hT', hg', hd'⟩ :=
      quotAt_sim hB.rules.toQuotAtProg (quotPinSim_of hB.qp (hB.rom.quot dn) hB.leaf hqd)
        (ciAtLpsSim_of hB.rules.toCiProg (rulesAtSim_of hB.rules)) n k hT hok hr hq hc r m' h
    exact ⟨ci, a', hrun, hT', hg', by show decCI (erA (truncM m')) _ = some ci; rw [truncM_erA]; exact hd'⟩

end L.Ind
