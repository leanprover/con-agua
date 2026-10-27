import ConAgua.Arena.IndPartsSpec.IndPartsProg5
import ConAgua.Arena.IndPartsSpec.PartsSliceCopy

/-!
# Bf

`bpf_spec`, `bpr_spec`, `bpc_spec`, `bpo_spec`, `bsl_spec`, `bsn_spec` and the lemmas only they use.
-/

section

set_option linter.unusedSectionVars false

/-!
# Refinements of `IndParts`, part 13 (lane `indproofs2`, helper `parts`): `blockShape?`'s pins

The reserved-name and level-parameter pins (`block_shape_pins_formers`/`_recs`/`_ctors`/`_ok`,
pure in the twin: one `Bool`), and the eliminator (`block_shape_large`). Shared pieces: a constant's
level parameters copied by `er_to_iw` (`partsLpsCopy`), `reserved_contains` against the twin's
`reservedBasisNames` (`partsResCont`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section spec
variable (p : Prog) (hP : IndPartsProg4 p) (hrf : p.lookup "reserved_from" = some reservedFrom)
  (hrc : p.lookup "reserved_contains" = some reservedContains) (hec : p.lookup "er_copy" = some erCopy)
  (het : p.lookup "er_to_iw" = some erToIw) (hseq : p.lookup "sl_eq" = some slEq)
include hP hrf hrc

include hec het hseq in
theorem bpf_spec (hp : p.lookup "block_shape_pins_formers" = some blockShapePinsFormers) (n : Nat) :
    ∀ (s₀ : St) (cto ctl lo ll : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_pins_formers" [cto, ctl, lo, ll]
    ⦃fun r s' => LocEq s' s₀ ∧ bpfW n s₀.mem cto ctl lo ll = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ cto ctl lo ll; rw [invoke_eq _ hp]; simp only [callFn, blockShapePinsFormers]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ cto ctl lo ll
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapePinsFormers]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, resCont_spec p hrf hrc n,
        erToIw_specW p hP.alloc hec het n, slEq_spec p hseq n, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem bpr_spec (hp : p.lookup "block_shape_pins_recs" = some blockShapePinsRecs) (n : Nat) :
    ∀ (s₀ : St) (ro rl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_pins_recs" [ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ bprW n s₀.mem ro rl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ ro rl; rw [invoke_eq _ hp]; simp only [callFn, blockShapePinsRecs]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ro rl
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapePinsRecs]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, resCont_spec p hrf hrc n, ih] <;>
      finish (gen := 20) [rdW_eq]

include hec het hseq in
theorem bpc_spec (hp : p.lookup "block_shape_pins_ctors" = some blockShapePinsCtors) (n : Nat) :
    ∀ (s₀ : St) (nP cso csl lo ll : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_pins_ctors" [nP, cso, csl, lo, ll]
    ⦃fun r s' => LocEq s' s₀ ∧ bpcW n s₀.mem nP cso csl lo ll = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ nP cso csl lo ll; rw [invoke_eq _ hp]; simp only [callFn, blockShapePinsCtors]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ nP cso csl lo ll
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapePinsCtors]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, resCont_spec p hrf hrc n,
        erToIw_specW p hP.alloc hec het n, slEq_spec p hseq n, ih] <;>
      finish (gen := 20) [rdW_eq]

end spec

theorem bpo_spec (p : Prog) (hP : IndPartsProg4 p) (hrf : p.lookup "reserved_from" = some reservedFrom)
    (hrc : p.lookup "reserved_contains" = some reservedContains) (hec : p.lookup "er_copy" = some erCopy)
    (het : p.lookup "er_to_iw" = some erToIw) (hseq : p.lookup "sl_eq" = some slEq)
    (hf : p.lookup "block_shape_pins_formers" = some blockShapePinsFormers)
    (hr : p.lookup "block_shape_pins_recs" = some blockShapePinsRecs)
    (hc : p.lookup "block_shape_pins_ctors" = some blockShapePinsCtors)
    (hp : p.lookup "block_shape_pins_ok" = some blockShapePinsOk) (n : Nat) (s₀ : St)
    (nP cto ctl lo ll ro rl cso csl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_shape_pins_ok" [nP, cto, ctl, lo, ll, ro, rl, cso, csl]
    ⦃fun r s' => LocEq s' s₀ ∧ bpoW n s₀.mem nP cto ctl lo ll ro rl cso csl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapePinsOk]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, bpf_spec p hP hrf hrc hec het hseq hf n,
      bpr_spec p hP hrf hrc hr n, bpc_spec p hP hrf hrc hec het hseq hc n] <;>
    finish (gen := 20) [bpoW]

theorem bsl_spec (p : Prog) (hP : IndPartsProg4 p) (hec : p.lookup "er_copy" = some erCopy)
    (het : p.lookup "er_to_iw" = some erToIw) (hseq : p.lookup "sl_eq" = some slEq)
    (hp : p.lookup "block_shape_large" = some blockShapeLarge) (n : Nat) (s₀ : St) (cvR0 lo ll : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_shape_large" [cvR0, lo, ll]
    ⦃fun r s' => LocEq s' s₀ ∧ bslW n s₀.mem cvR0 lo ll = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeLarge]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, erToIw_specW p hP.alloc hec het n,
      slEq_spec p hseq n, slContains_spec p hP.contains n] <;>
    finish (gen := 20) [bslW, rdW_eq]

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

/-! ## The `vcgen` specs -/

section spec
variable (p : Prog) (hP : IndPartsProg4 p)
include hP

theorem bsn_spec (hp : p.lookup "block_shape_names_of" = some blockShapeNamesOf) (n : Nat) :
    ∀ (s₀ : St) (cto ctl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_names_of" [cto, ctl]
    ⦃fun r s' => LocEq s' s₀ ∧ bsnW n s₀.mem cto ctl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ cto ctl; rw [invoke_eq _ hp]; simp only [callFn, blockShapeNamesOf]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ cto ctl
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapeNamesOf]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        slCons_specW p hP.alloc hP.copy hP.cons n, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem bct_spec (hp : p.lookup "block_shape_ctors_of" = some blockShapeCtorsOf) (n : Nat) :
    ∀ (s₀ : St) (cso csl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_ctors_of" [cso, csl]
    ⦃fun r s' => LocEq s' s₀ ∧ bctW n s₀.mem cso csl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ cso csl; rw [invoke_eq _ hp]; simp only [callFn, blockShapeCtorsOf]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ cso csl
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapeCtorsOf]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        posRec2_specW p hP.alloc hP.rec2 n, slCons_specW p hP.alloc hP.copy hP.cons n, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem bmo_spec (h4 : p.lookup "rec4" = some rec4)
    (hp : p.lookup "block_shape_members_of" = some blockShapeMembersOf) (n : Nat) :
    ∀ (s₀ : St) (cto ctl io go : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_members_of" [cto, ctl, io, go]
    ⦃fun r s' => LocEq s' s₀ ∧ bmoW n s₀.mem cto ctl io go = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ cto ctl io go; rw [invoke_eq _ hp]; simp only [callFn, blockShapeMembersOf]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ cto ctl io go
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapeMembersOf]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        posRec4_specW p hP.alloc h4 n, slCons_specW p hP.alloc hP.copy hP.cons n, ih] <;>
      finish (gen := 20) [rdW_eq]

end spec

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

theorem bso_spec (p : Prog) (hv : p.lookup "e_view" = some eView) (hpw : p.lookup "pin_word" = some pinWordL)
    (hg : p.lookup "sl_getd" = some slGetD)
    (hp : p.lookup "block_shape_result_sort" = some blockShapeResultSort) (hst : StripProg p)
    (n : Nat) (s₀ : St) (nP io il ty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_shape_result_sort" [nP, io, il, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ bsoW s₀.mem nP io il ty = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeResultSort]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, slGetD_specW p hg n,
      stripPis_specF p hst n, eViewSpec4 p hv n, pinWord_specV p hpw n] <;>
    finish (gen := 20) [bsoW, bsoK1, bsoK2]

section arms
variable (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (m : Mem) (r : List Word)
  (no nl io lo ll s ip mo ml : Word) (q : Word)
theorem bbK12_some : bbK12 n nPd cto ctl cso csl rso rsl cvT0 cvR0 lo ll s ip mo ml (some (r, m)) =
    bbK13' mo ml (r.headD 0) (r.tail.headD 0) nPd s ip (bslW n m cvR0 lo ll) := rfl
theorem bbK13'_some (ro2 rl2 : Word) : bbK13' mo ml ro2 rl2 nPd s ip (some (r, m)) =
    bgoK3 (bsealW m mo ml ro2 rl2 nPd s ip (r.headD 0) (r.tail.headD 0)) := rfl
theorem bbK10_some : bbK10 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip (some (r, m)) =
    bbK11 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl lo ll s ip (bmoW (n + 1) m cto ctl io (r.headD 0)) := rfl
theorem bbK9_some (cof cl2 : Word) :
    bbK9 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip cof cl2 (some (r, m)) =
    bbK10 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip
      (bgW n m no nl (r.headD 0) nPd ctl cof cl2) := rfl
end arms
attribute [ind_grind] bbK13'_some bbK12_some bbK10_some bbK9_some

section arms
variable (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 : Word) (m : Mem) (r : List Word)
  (no nl io il lo ll s z : Word)
theorem btK3_some : btK3 c n nPd cto ctl cso csl rso rsl no nl io lo ll s (some (r, m)) =
    bgoK3 (bfW n m nPd cto ctl cso csl rso rsl no nl io lo ll s (if r.headD 0 = 2 then 1 else 0)) := rfl
theorem btK1_some : btK1 c n nPd cto ctl cso csl rso rsl no nl io lo ll (some (r, m)) =
    btK2 c n nPd cto ctl cso csl rso rsl no nl io lo ll (r.headD 0) m (pinWordV m 53) := rfl
theorem bbH2_fail (h : r.headD 0 = 0) : bbH2 c n nPd cto ctl cso csl rso rsl cvT0 no nl (some (r, m)) =
    some ([0, 0], m) := by simp only [bbH2]; exact ite_eq_left h
theorem bbH2_ok (h : ¬ r.headD 0 = 0) : bbH2 c n nPd cto ctl cso csl rso rsl cvT0 no nl (some (r, m)) =
    bbH3 c n nPd cto ctl cso csl rso rsl no nl (r.tail.headD 0) (r.tail.tail.headD 0)
      (erToIwW (n + 3) m (rdW (m.arr64 EREC) (cvT0 + 1)) (rdW (m.arr64 EREC) (cvT0 + 2))) := by
  simp only [bbH2]; exact ite_eq_right h
end arms
attribute [ind_grind] btK3_some btK1_some bbH2_fail bbH2_ok

set_option maxHeartbeats 20000000 in
theorem bf_spec (p : Prog) (hP : IndPartsProg5 p) (n : Nat) (s₀ : St)
    (nPd cto ctl cso csl rso rsl no nl io lo ll s ip : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 2)) "block_shape_fin"
      [nPd, cto, ctl, cso, csl, rso, rsl, no, nl, io, lo, ll, s, ip]
    ⦃fun r s' => LocEq s' s₀ ∧ bfW n s₀.mem nPd cto ctl cso csl rso rsl no nl io lo ll s ip = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.fin]
  simp only [callFn, blockShapeFin]
  sym (gen := 24) (instances := 30000) only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      bct_spec p hP.toIndPartsProg4 hP.ctorsOf (n + 1),
      plW_spec p hP.alloc hP.copy hP.cons hP.slGet hP.paramFind hP.paramPush hP.internParam hP.plGo hP.pl hP.il (n + 1),
      bg_spec p hP.toIndPartsProg hP.view hP.find hP.midx hP.cmem hP.gone hP.rec2 hP.ggo hP.groups n,
      bmo_spec p hP.toIndPartsProg4 hP.rec4 hP.membersOf (n + 1),
      brs_spec p hP.toIndPartsProg4 hP.rec6 hP.rhssOf hP.recsOf (n + 1),
      bsl_spec p hP.toIndPartsProg4 hP.erCopy hP.erToIw hP.slEq hP.large n,
      bseal_spec p hP.na hP.alloc hP.pack hP.sealF (n + 1)] <;>
    finish (gen := 20) [bfW, rdW_eq, bbK8_some, bbK9_some, bbK10_some, bbK11_some, bbK12_some,
      bbK13'_some, bgoK3_some]

set_option maxHeartbeats 20000000 in
theorem bt_spec (p : Prog) (hP : IndPartsProg5 p) (c : CallM) (hc : CallSpec p c) (n : Nat) (s₀ : St)
    (nPd cto ctl cso csl rso rsl no nl io il lo ll : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 3)) "block_shape_tail"
      [nPd, cto, ctl, cso, csl, rso, rsl, no, nl, io, il, lo, ll]
    ⦃fun r s' => LocEq s' s₀ ∧ btW c n s₀.mem nPd cto ctl cso csl rso rsl no nl io il lo ll = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.tail]
  simp only [callFn, blockShapeTail]
  sym (gen := 24) (instances := 30000) only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      bso_spec p hP.view hP.pinWord hP.slGetD hP.sort hP.strip (n + 1), pinWord_specV p hP.pinWord (n + 2),
      hc (n + 2) "lvl_eq_c", bf_spec p hP n] <;>
    finish (gen := 20) [btW, rdW_eq, btK1_some, btK2_some, btK3_some, bgoK3_some]

set_option maxHeartbeats 20000000 in
theorem bb_spec (p : Prog) (hP : IndPartsProg5 p) (c : CallM) (hc : CallSpec p c) (n : Nat) (s₀ : St) (nPd cto ctl cso csl rso rsl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 4)) "block_shape_build" [nPd, cto, ctl, cso, csl, rso, rsl]
    ⦃fun r s' => LocEq s' s₀ ∧ bbW c n s₀.mem nPd cto ctl cso csl rso rsl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.build]
  simp only [callFn, blockShapeBuild]
  sym (gen := 24) (instances := 30000) only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      bsn_spec p hP.toIndPartsProg4 hP.namesOf (n + 3), bmc_spec p hP.toIndPartsProg4 (n + 2),
      erToIw_specW p hP.alloc hP.erCopy hP.erToIw (n + 3),
      bpo_spec p hP.toIndPartsProg4 hP.resFrom hP.resCont hP.erCopy hP.erToIw hP.slEq hP.pinsF hP.pinsR
        hP.pinsC hP.pinsOk (n + 2), bt_spec p hP c hc n] <;>
    finish (gen := 20) [bbW, rdW_eq, bbH1_some, bbH2_fail, bbH2_ok, bbH3_some, bbH4_fail, bbH4_ok, bgoK3_some]

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

theorem bsh_spec (p : Prog) (hP : IndPartsProg5 p) (c : CallM) (hc : CallSpec p c) (n : Nat) (s₀ : St) (nPd off l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 5)) "block_shape" [nPd, off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ bshW c n s₀.mem nPd off l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.shape]
  simp only [callFn, blockShape]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      bs_spec p hP.alloc hP.copy hP.cons hP.rec5 hP.rec3 hP.rec6 hP.recs hP.ctors hP.split (n + 4),
      bb_spec p hP c hc n] <;>
    finish (gen := 20) [bshW, rdW_eq, bgoK3_some]

end L.Ind

end

end
