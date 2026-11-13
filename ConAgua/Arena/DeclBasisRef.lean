module

public import ConAgua.Arena.StageTLift
public import ConRon.Bridge.Checker.Basis
public import ConAgua.Arena.QuotRulesT
public import ConAgua.Arena.ErToIwBlk
import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.DeclAndPinIndRef
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Inv
import all ConAgua.Arena.IndIface
import ConAgua.Arena.RecLayout.CIDec

@[expose] public section

/-!
# The pinned basis blocks' refinements: the statements (lane `ronsync2`, stage 3)

The entry points of `BasisL.lean` that the reserved names' check (`basis_names_ok`) and the
quotient arm call, in the ROM readers' style (`L.Rom.RomRef`: from `StageR` and the
arguments' decodings, the twin's run, `KeepPost` after it):

* `basis_name_hit(o, l)` refines `basisNameHit block` (`BasisNameHitRef`; the result `(hit,
  kind)` as `decHit`);
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
  L.Front.decCIsR (erecP m) o.toNat l.toNat = some block ∧ o.toNat + l.toNat < 2 ^ 64

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

/-- **`quot_at(k.slot, q)` refines `quotAt k cv`** (`q` an `EREC` constant value), from a
well-formed twin state that names `Quot`'s `sortZ` names through `dn`. -/
def QuotAtRef : Prop := ∀ (k : ConLeche.QuotKind) (q : Word) (cv : IConstantVal),
  RomRef p "quot_at" [UInt64.ofNat k.slot, q]
    (fun m a => StageT dn vis fe m a ∧ ConRon.Bridge.StateOK a ∧ ConRon.Bridge.ReadOK a ∧
      NamesDn dn a quotNames ∧ decCV (erecP m) q.toNat = some cv ∧
      ∃ c, Frontend.denoteCV a.store cv = some c)
    (ConRon.Arena.quotAt k cv) (KeepPostT dn vis fe (decRCI dn))

/-- The two, at every stage. -/
structure BasisRefs : Prop where
  nameHit : ∀ dn vis fe, BasisNameHitRef p dn vis fe
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

/-! ## The proofs -/

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
  · rw [ite_eq_left h1] at h; cases h
    have hne : blockNames A ≠ blockNames B := fun he => h1 (UInt64.toNat_inj.mp (by
      have := congrArg List.length he; simp only [blockNames, List.length_map] at this; omega))
    exact ⟨rfl, rfl, by simpa using hne⟩
  rw [ite_eq_right h1] at h
  have h1' : al = bl := by simpa using h1
  subst h1'
  by_cases h2 : al = 0
  · rw [ite_eq_left h2] at h; cases h
    subst h2
    have hA0 : A = [] := List.eq_nil_of_length_eq_zero (by rw [hlA]; rfl)
    have hB0 : B = [] := List.eq_nil_of_length_eq_zero (by rw [hlB]; rfl)
    subst hA0 hB0
    exact ⟨rfl, rfl, by simp⟩
  rw [ite_eq_right h2] at h
  obtain ⟨x, A', rfl, hx, hA'⟩ := hA.uncons h2 hsz
  obtain ⟨y, B', rfl, hy, hB'⟩ := hB.uncons h2 hsz
  rw [decB_ciF] at hx hy
  obtain ⟨wx, hwx, hwx32, hnx⟩ := decCI_name hx
  obtain ⟨wy, hwy, hwy32, hny⟩ := decCI_name hy
  have ex : erRd m (rdW (m.arr64 IW) ao + (CI.cv + CV.name)) = wx :=
    (erRdOK m).at _ CI.cv_name_toNat hwx
  have ey : erRd m (rdW (m.arr64 IW) bo + (CI.cv + CV.name)) = wy :=
    (erRdOK m).at _ CI.cv_name_toNat hwy
  by_cases h3 : wx ≠ wy
  · rw [ite_eq_left (by simpa only [L.Ind.erRd_foldN, ex, ey] using h3)] at h; cases h
    refine ⟨rfl, rfl, by
      simp only [List.headD_cons, ne_eq, not_true_eq_false, false_iff, blockNames, List.map_cons,
        List.cons.injEq, not_and]
      intro he; exact absurd (decI_inj hwx32 hwy32 (hnx ▸ hny ▸ he)) h3⟩
  rw [ite_eq_right (by simpa only [L.Ind.erRd_foldN, ex, ey] using h3)] at h
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
  · rw [ite_eq_left h4] at h; cases h
    have : k.toNat = 4 := by have := UInt64.le_iff_toNat_le.mp h4; simp at this; omega
    refine ⟨none, a, ?_, hT, IWGrow.refl m, rfl⟩
    rw [this]; rfl
  rw [ite_eq_right h4] at h
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
  · rw [basisNameHitGoW.k_block_names_eq, ite_eq_left (hiff.mpr he)] at h; cases h
    refine ⟨some (basisOfW k.toNat), a1, ?_, hT1, hg1, by simp [decHit, hk4]⟩
    rw [hks]
    simp only [ConRon.Arena.basisNameHitGo, StateT.run_bind]
    rw [show StateT.run (BasisKind.decls (basisOfW k.toNat)) a = .ok (blk, a1) from hrun1, L.Arena.except_ok_bind]
    dsimp only; rw [ite_eq_left (by simp [he])]; rfl
  · rw [basisNameHitGoW.k_block_names_eq, ite_eq_right (fun h0 => he (hiff.mp h0))] at h
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
    rw [show StateT.run (BasisKind.decls (basisOfW k.toNat)) a = .ok (blk, a1) from hrun1, L.Arena.except_ok_bind]
    rw [hk1] at hrun
    dsimp only; rw [ite_eq_right (by simpa using he)]; exact hrun

end go

/-- **The basis entry points refine the twin.** -/
theorem basisRefs_of {p : Prog} (hB : BasisLProg p) : BasisRefs p := by
  refine ⟨fun dn vis fe => ?_, fun dn vis fe => ?_⟩
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
  · -- `quot_at`
    rintro k q cv n m a r m' ⟨hT, hok, hr, hnd, hq, c, hc⟩ h
    have hqd : QuotDn dn := by
      obtain ⟨x, hx1, -⟩ := hnd (.str .anonymous "u") (by simp [L.Rom.quotNames]); exact ⟨x, hx1⟩
    obtain ⟨ci, a', hrun, hT', hg', hd'⟩ :=
      quotAt_sim hB.rules.toQuotAtProg (quotPinSim_of hB.qp (hB.rom.quot dn) hB.leaf hqd)
        (ciAtLpsSim_of hB.rules.toCiProg (rulesAtSim_of hB.rules)) n k hT hok hr hq hc r m' h
    exact ⟨ci, a', hrun, hT', hg', by show decCI (erA (truncM m')) _ = some ci; rw [truncM_erA]; exact hd'⟩

end L.Ind
