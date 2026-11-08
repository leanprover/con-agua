module

import ConAgua.Arena.IndPartsSpec.PartsPSlCons
public import ConAgua.Arena.IndPartsSpec.SetEqW
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all Init.Data.List.Control
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndPartsSpec.BsW
import ConAgua.Arena.IndPartsSpec.RecTW
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.RecClassSpec.CloseLams
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndParts
import all ConAgua.Arena.IndPos

@[expose] public section

/-!
# BlockRecNameSetOk: `ConRon.Arena.blockGroups`, `ConRon.Arena.blockRecNameSetOk`, `ConRon.Arena.ctorMember`

The refinement theorems `ctorMember_refines`, `blockGroups_refines`, `blockRecNameSetOk_refines` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem partsDrop3 (r : List Word) : (r.drop 3).headD 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

/-- `memberIdxAt?`'s index lies in the names. -/
theorem partsMemberIdx_lt {names : List NIdx} {lvls : LsIdx} {e : EIdx} {a a' : AState} {i : Nat}
    (h : (ConRon.Arena.memberIdxAt? names lvls e).run a = .ok (some i, a')) : i < names.length := by
  unfold ConRon.Arena.memberIdxAt? at h
  split at h
  · simp only [StateT.run_bind] at h
    cases hv : (viewConst e).run a with
    | error x => rw [hv] at h; cases h
    | ok p =>
      obtain ⟨x, a1⟩ := p
      rw [hv] at h
      rcases x with _ | ⟨nn, us⟩
      · revert h; simp [StateT.run, failDanglingE, bind, Except.bind]
        intro h; revert h; unfold fail
        simp [throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind]
      · revert h; simp only [except_ok_bind]
        split
        · simp [StateT.run, pure, StateT.pure, Except.pure]
          intro h _; rw [List.findIdx?_eq_some_iff_getElem] at h; exact h.1
        · simp [StateT.run, pure, StateT.pure, Except.pure]
  · revert h; simp [StateT.run, pure, StateT.pure, Except.pure]

/-- **`ctor_member`'s model refines `ctorMember?`**: the constructor `[cv, nF]` decoded below the
tops at `c`, the member names a handle slice below the top. -/
theorem ctmW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) {m : Mem}
    {a : AState} {no nl lvls nP c : Word} {cv : IConstantVal} {nF : Nat} {names : List NIdx}
    (hS : StageR vis fe m a) (hc : DecB (fun m => decCN m c.toNat) m (cv, nF))
    (hnm : DecB (fun m => decHL m no.toNat nl.toNat) m names) (hnb : no.toNat + nl.toNat ≤ iwTop m)
    (hlv : H lvls) :
    Sim (ctmW (n + 1) m no nl lvls nP c) (ConRon.Arena.ctorMember? names (decI lvls) nP.toNat (cv, nF)) a
      (fun r o m' a' => MemIdxOut r o ∧ (∀ i, o = some i → i < names.length) ∧
        StageR vis fe m' a' ∧ IWGrow m m') := by
  sorry

/-! ## `block_groups_one`: the `filterM` -/

theorem partsFilterAuxM {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} (p : α → m Bool) :
    ∀ (l acc : List α), List.filterAuxM p l acc = (fun r => r ++ acc) <$> List.filterAuxM p l []
  | [], acc => by simp [List.filterAuxM]
  | x :: l, acc => by
    simp only [List.filterAuxM, map_bind]
    congr 1; funext b
    rw [partsFilterAuxM p l, partsFilterAuxM p l (cond b [x] []), Functor.map_map]
    cases b <;> simp

theorem partsFilterM_cons {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} (p : α → m Bool)
    (a : α) (l : List α) :
    List.filterM p (a :: l) = (do
      let b ← p a
      let r ← List.filterM p l
      pure (if b then a :: r else r)) := by
  simp only [List.filterM, List.filterAuxM, bind_assoc]
  congr 1; funext b
  rw [partsFilterAuxM p l, bind_map_left]
  congr 1; funext r
  cases b <;> simp

theorem bgoK3_some (m2 : Mem) (r2 : List Word) : bgoK3 (some (r2, m2)) =
    some ([r2.headD 0, r2.tail.headD 0], m2) := rfl
attribute [ind_grind] bgoK3_some

/-- **`block_groups_one` is its model `bgoW`** (generated). -/
l_model bgo_spec (p : Prog) (hP : IndPartsProg p) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hm : p.lookup "member_idx_at" = some memberIdxAt)
    (hc : p.lookup "ctor_member" = some ctorMember)
    (hp : p.lookup "block_groups_one" = some blockGroupsOne)
  fns [hp ↦ bgoW]
  specs [ctorMember_specK p hv hf hm hc hP.strip hP.ad n, slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [ind_grind] finish [rdW_eq] gen 20

/-- `blockGroups`' filter predicate for member `mm`. -/
def bgPred (names : List NIdx) (lvls : LsIdx) (nP mm : Nat) (c : IConstantVal × Nat) : AM Bool := do
  match ← ConRon.Arena.ctorMember? names lvls nP c with
  | some t => pure (t == mm)
  | none => pure false

/-- `ctorMember?`'s answer compared with member `mm`. -/
def optEq (o : Option Nat) (mm : Nat) : Bool := match o with
  | some t => t == mm
  | none => false

theorem partsFilter_step (names : List NIdx) (lvls : LsIdx) (nP mm : Nat) (c0 : IConstantVal × Nat)
    (cs : List (IConstantVal × Nat)) :
    (c0 :: cs).filterM (bgPred names lvls nP mm) =
      ConRon.Arena.ctorMember? names lvls nP c0 >>= fun x =>
        cs.filterM (bgPred names lvls nP mm) >>= fun r =>
          pure (if optEq x mm then c0 :: r else r) := by
  rw [partsFilterM_cons]; simp only [bgPred, bind_assoc]
  congr 1; funext x; cases x <;> simp [optEq]

/-- **`block_groups_one`'s model refines the twin's `filterM`** (one member's group). -/
theorem bgoW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {no nl lvls nP mm : Word}
    {names : List NIdx} (hlv : H lvls) (n : Nat) :
    ∀ (m : Mem) (a : AState) (co cl : Word) (cs : List (IConstantVal × Nat)),
    StageR vis fe m a → PSlR decCN cs co cl m →
    DecB (fun m => decHL m no.toNat nl.toNat) m names → no.toNat + nl.toNat ≤ iwTop m →
    Sim (bgoW n m no nl lvls nP co cl mm) (cs.filterM (bgPred names (decI lvls) nP.toNat mm.toNat)) a
      (fun r gs m' a' => PSlR decCN gs (r.headD 0) (r.tail.headD 0) m' ∧ StageR vis fe m' a' ∧
        IWGrow m m') := by
  sorry

/-! ## `block_groups_go`, `block_groups` -/

/-- A group header `[off, len]` of a constructor slice. -/
def decGH (m : Mem) (p : Nat) : Option (List (IConstantVal × Nat)) := decAt m (decPL m (decCN m)) p

theorem decGH_mono (p : Nat) : OMono (fun m => decGH m p) :=
  OMono.decAt (fun o l => OMono.decPL decCN_mono o l) p

/-- A cons onto a slice, then the slice (the shared tail of the hand `IndParts` models). -/
def bggK3 (n : Nat) (h0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => bgoK3 (consW n m3 h0 (r3.headD 0) (r3.tail.headD 0))

theorem bggK3_some (n : Nat) (m2 : Mem) (h0 : Word) (r1 : List Word) : bggK3 n h0 (some (r1, m2)) =
    bgoK3 (consW n m2 h0 (r1.headD 0) (r1.tail.headD 0)) := by simp [bggK3]
attribute [ind_grind] bggK3_some

/-- **`block_groups_go` is its model `bggW`** (generated). -/
l_model bgg_spec (p : Prog) (hP : IndPartsProg p) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hm : p.lookup "member_idx_at" = some memberIdxAt)
    (hc : p.lookup "ctor_member" = some ctorMember)
    (ho : p.lookup "block_groups_one" = some blockGroupsOne) (h2 : p.lookup "rec2" = some rec2)
    (hp : p.lookup "block_groups_go" = some blockGroupsGo)
  fns [hp ↦ bggW]
  specs [bgo_spec p hP hv hf hm hc ho n, posRec2_specW p hP.alloc h2 n,
    slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [ind_grind] finish [rdW_eq] gen 20

/-- A fresh group header over a constructor slice decoded below the tops. -/
theorem partsGH {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {g0 g1 h0 : Word} {gs : List (IConstantVal × Nat)}
    (h : posRecW m [g0, g1] = some (h0, m')) (hS : StageR vis fe m a) (hg : PSlR decCN gs g0 g1 m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ DecB (fun m => decGH m h0.toNat) m' gs := by
  sorry

/-- **`block_groups_go`'s model refines the twin's `mapM` over members `mm, …, k - 1`.** -/
theorem bggW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {no nl lvls nP co cl k : Word}
    {names : List NIdx} {cs : List (IConstantVal × Nat)} (hlv : H lvls) (n : Nat) :
    ∀ (m : Mem) (a : AState) (mm : Word),
    StageR vis fe m a → PSlR decCN cs co cl m →
    DecB (fun m => decHL m no.toNat nl.toNat) m names → no.toNat + nl.toNat ≤ iwTop m →
    Sim (bggW n m no nl lvls nP co cl mm k)
      ((List.range' mm.toNat (k.toNat - mm.toNat)).mapM
        (fun j => cs.filterM (bgPred names (decI lvls) nP.toNat j))) a
      (fun r gss m' a' => PSlR decGH gss (r.headD 0) (r.tail.headD 0) m' ∧ StageR vis fe m' a' ∧
        IWGrow m m') := by
  sorry

/-- **The model of `block_groups`.** -/
def bgW (n : Nat) (m : Mem) (no nl lvls nP k co cl : Word) : Option (List Word × Mem) :=
  if k = 1 then
    (match posRecW m [co, cl] with
     | none => none
     | some (h0, m1) => bgoK3 (consW n m1 h0 0 0))
  else bgoK3 (bggW n m no nl lvls nP co cl 0 k)

theorem bg_spec (p : Prog) (hP : IndPartsProg p) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hm : p.lookup "member_idx_at" = some memberIdxAt)
    (hc : p.lookup "ctor_member" = some ctorMember)
    (ho : p.lookup "block_groups_one" = some blockGroupsOne) (h2 : p.lookup "rec2" = some rec2)
    (hg : p.lookup "block_groups_go" = some blockGroupsGo)
    (hp : p.lookup "block_groups" = some blockGroups) (n : Nat) (s₀ : St) (no nl lvls nP k co cl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_groups" [no, nl, lvls, nP, k, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ bgW n s₀.mem no nl lvls nP k co cl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockGroups]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      bgg_spec p hP hv hf hm hc ho h2 hg n, posRec2_specW p hP.alloc h2 n,
      slCons_specW p hP.alloc hP.copy hP.cons n] <;>
    finish (gen := 20) [bgW]

/-- **`block_groups`' model refines `blockGroups`.** -/
theorem bgW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {no nl lvls nP k co cl : Word}
    {names : List NIdx} {cs : List (IConstantVal × Nat)} (hlv : H lvls) (n : Nat) {m : Mem} {a : AState}
    (hS : StageR vis fe m a) (hcs : PSlR decCN cs co cl m)
    (hnm : DecB (fun m => decHL m no.toNat nl.toNat) m names) (hnb : no.toNat + nl.toNat ≤ iwTop m) :
    Sim (bgW n m no nl lvls nP k co cl) (ConRon.Arena.blockGroups names (decI lvls) nP.toNat k.toNat cs) a
      (fun r gss m' a' => PSlR decGH gss (r.headD 0) (r.tail.headD 0) m' ∧ StageR vis fe m' a' ∧
        IWGrow m m') := by
  sorry

/-- **`ctor_member` refines `ctorMember?`** (through the stub `get_app_fn_f`; L
aborts when `nP + nF` wraps, a capacity). -/
@[refines ConRon.Arena.ctorMember?]
theorem ctorMember_refines (p : Prog) (hP : IndPartsProg2 p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (no nl lvls nP c : Word)
    (cv : IConstantVal) (nF : Nat) (names : List NIdx) (hS : StageR vis fe s₀.mem a₀)
    (hc : DecB (fun m => decCN m c.toNat) s₀.mem (cv, nF))
    (hnm : DecB (fun m => decHL m no.toNat nl.toNat) s₀.mem names)
    (hnb : no.toNat + nl.toNat ≤ iwTop s₀.mem) (hlv : H lvls) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ctor_member" [no, nl, lvls, nP, c]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.ctorMember? names (decI lvls) nP.toNat (cv, nF)) a₀ ∧
      MemIdxOut r (AM.res (ConRon.Arena.ctorMember? names (decI lvls) nP.toNat (cv, nF)) a₀) ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.ctorMember? names (decI lvls) nP.toNat (cv, nF)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  sorry

/-- **`block_groups` refines `blockGroups`**: the constructors `[cv, nF]` an `IW` slice decoded
below the tops, the member names a handle slice below the top; the result a slice of group headers
`[off, len]` (`decGH`). -/
@[refines ConRon.Arena.blockGroups]
theorem blockGroups_refines (p : Prog) (hP : IndPartsProg2 p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (no nl lvls nP k co cl : Word)
    (cs : List (IConstantVal × Nat)) (names : List NIdx) (hS : StageR vis fe s₀.mem a₀)
    (hcs : PSlR decCN cs co cl s₀.mem)
    (hnm : DecB (fun m => decHL m no.toNat nl.toNat) s₀.mem names)
    (hnb : no.toNat + nl.toNat ≤ iwTop s₀.mem) (hlv : H lvls) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_groups" [no, nl, lvls, nP, k, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.blockGroups names (decI lvls) nP.toNat k.toNat cs) a₀ ∧
      PSlR decGH (AM.res (ConRon.Arena.blockGroups names (decI lvls) nP.toNat k.toNat cs) a₀)
        (r.headD 0) (r.tail.headD 0) s'.mem ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.blockGroups names (decI lvls) nP.toNat k.toNat cs) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  sorry

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem slSetEq_spec (p : Prog) (hc : p.lookup "sl_contains" = some slContains)
    (ha : p.lookup "sl_all_in" = some slAllIn) (hp : p.lookup "sl_set_eq" = some slSetEq) (n : Nat)
    (s₀ : St) (o1 l1 o2 l2 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "sl_set_eq" [o1, l1, o2, l2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ setEqW n s₀.mem o1 l1 o2 l2 = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, slSetEq]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, slAllIn_spec p hc ha n] <;>
    finish (gen := 20) [setEqW]

/-! ## `block_rec_want`, `block_rec_got` -/

mutual
/-- **The model of `block_rec_want`.** -/
def brwW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, mo, ml =>
    if ml = 0 then some ([0, 0], m)
    else brwK1 n mo ml (nrF m [rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) mo))])
/-- After `name_rec`. -/
def brwK1 (n : Nat) (mo ml : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => bggK3 n (r1.headD 0) (brwW n m1 (mo + 1) (ml - 1))
end

/-- **The model of `block_rec_got`.** -/
def brgW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, ro, rl =>
    if rl = 0 then some ([0, 0], m)
    else brgK n (rdW (m.arr64 IW) ro) (brgW n m (ro + 1) (rl - 1))
where
  /-- After the recursive call. -/
  brgK (n : Nat) (rc : Word) : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (r, m1) => bgoK3 (consW n m1 (rdW (m1.arr64 EREC) (rdW (m1.arr64 IW) rc)) (r.headD 0) (r.tail.headD 0))

section arms
variable (n : Nat) (m m1 : Mem) (mo ml ro rl rc : Word) (r1 : List Word)
theorem brwW_nil (h : ml = 0) : brwW (n + 1) m mo ml = some ([0, 0], m) := by simp [brwW, h]
theorem brwW_cons (h : ml ≠ 0) : brwW (n + 1) m mo ml = brwK1 n mo ml
    (nrF m [rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) mo))]) := by
  simp [brwW, h]
theorem brwK1_some : brwK1 n mo ml (some (r1, m1)) = bggK3 n (r1.headD 0) (brwW n m1 (mo + 1) (ml - 1)) := by
  simp [brwK1]
theorem brgW_nil (h : rl = 0) : brgW (n + 1) m ro rl = some ([0, 0], m) := by simp [brgW, h]
theorem brgW_cons (h : rl ≠ 0) : brgW (n + 1) m ro rl =
    brgW.brgK n (rdW (m.arr64 IW) ro) (brgW n m (ro + 1) (rl - 1)) := by simp [brgW, h]
theorem brgK_some : brgW.brgK n rc (some (r1, m1)) =
    bgoK3 (consW n m1 (rdW (m1.arr64 EREC) (rdW (m1.arr64 IW) rc)) (r1.headD 0) (r1.tail.headD 0)) := rfl
end arms
attribute [ind_grind] brwW_nil brwW_cons brwK1_some brgW_nil brgW_cons brgK_some

section spec
variable (p : Prog) (hP : IndPartsProg p)
include hP

theorem brw_spec (hp : p.lookup "block_rec_want" = some blockRecWant) (n : Nat) :
    ∀ (s₀ : St) (mo ml : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_rec_want" [mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ brwW n s₀.mem mo ml = some (r, s'.mem); ⊤⦄ := by
  sorry

theorem brg_spec (hp : p.lookup "block_rec_got" = some blockRecGot) (n : Nat) :
    ∀ (s₀ : St) (ro rl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_rec_got" [ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ brgW n s₀.mem ro rl = some (r, s'.mem); ⊤⦄ := by
  sorry

end spec

/-- **`block_rec_got`'s model**: the recursors' names. -/
theorem brgW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (ro rl : Word) (recs : List RecShape) (r : List Word),
    brgW n m ro rl = some (r, m') → StageR vis fe m a → PSlR decRS recs ro rl m →
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (recs.map (·.cvR.name)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  sorry

/-- **`block_rec_want`'s model refines the twin's `mapM` of `name_rec`.** -/
theorem brwW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m : Mem) (a : AState) (mo ml : Word) (ms : List MemberShape),
    StageR vis fe m a →
    DecB (fun m => decPL m (decMS m) mo.toNat ml.toNat) m ms ∧ (ml = 0 ∨ mo.toNat + ml.toNat ≤ iwTop m) →
    Sim (brwW n m mo ml) (ms.mapM fun ms => internNNode (.str ms.cvT.name "rec")) a
      (fun r xs m' a' => decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR vis fe m' a' ∧ IWGrow m m') := by
  sorry

theorem partsAll_decI (ws vs : List Word) (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hvs : ∀ w ∈ vs, w.toNat < 2 ^ 32) :
    (ws.map (decI : Word → NIdx)).all (fun n => (vs.map (decI : Word → NIdx)).contains n) =
      ws.all (fun w => vs.contains w) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.all_cons]
    rw [ih (fun w' h' => hws w' (List.mem_cons_of_mem _ h')),
      contains_map_decI w (hws w (List.mem_cons_self ..)) vs hvs]

/-- **The model of `block_rec_name_set_ok`** (at exec fuel `n + 2`). -/
def brnW (n : Nat) (m : Mem) (mo ml ro rl : Word) : Option (List Word × Mem) :=
  match brwW (n + 1) m mo ml with
  | none => none
  | some (r1, m1) =>
    match brgW (n + 1) m1 ro rl with
    | none => none
    | some (r2, m2) =>
      match setEqW n m2 (r2.headD 0) (r2.tail.headD 0) (r1.headD 0) (r1.tail.headD 0) with
      | none => none
      | some b => some ([b], m2)

theorem brn_spec (p : Prog) (hP : IndPartsProg p) (hw : p.lookup "block_rec_want" = some blockRecWant)
    (hg : p.lookup "block_rec_got" = some blockRecGot) (hc : p.lookup "sl_contains" = some slContains)
    (ha : p.lookup "sl_all_in" = some slAllIn) (hs : p.lookup "sl_set_eq" = some slSetEq)
    (hp : p.lookup "block_rec_name_set_ok" = some blockRecNameSetOk) (n : Nat) (s₀ : St)
    (mo ml ro rl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "block_rec_name_set_ok" [mo, ml, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ brnW n s₀.mem mo ml ro rl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockRecNameSetOk]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, brw_spec p hP hw (n + 1),
      brg_spec p hP hg (n + 1), slSetEq_spec p hc ha hs n] <;>
    finish (gen := 20) [brnW]

/-- **`block_rec_name_set_ok` refines `blockRecNameSetOk`** (through the stub `name_rec`): the
members and recursors slices of records decoded below the tops (the members' below the top unless
empty: an empty slice's offset is whatever its record holds). -/
@[refines ConRon.Arena.blockRecNameSetOk]
theorem blockRecNameSetOk_refines (p : Prog) (hP : IndPartsProg3 p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mo ml ro rl : Word)
    (ms : List MemberShape) (recs : List RecShape) (hS : StageR vis fe s₀.mem a₀)
    (hms : DecB (fun m => decPL m (decMS m) mo.toNat ml.toNat) s₀.mem ms ∧
      (ml = 0 ∨ mo.toNat + ml.toNat ≤ iwTop s₀.mem))
    (hrs : PSlR decRS recs ro rl s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "block_rec_name_set_ok" [mo, ml, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.blockRecNameSetOk ms recs) a₀ ∧
      r = [if AM.res (ConRon.Arena.blockRecNameSetOk ms recs) a₀ then 1 else 0] ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.blockRecNameSetOk ms recs) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  sorry

end L.Ind

end

end
