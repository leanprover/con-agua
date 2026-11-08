module

public import ConAgua.Front.FrontPreOK1
public import ConAgua.Front.IndApplyRefine9
import ConAgua.Front.IndFieldsLink3
import ConAgua.Front.IndInstallRefine5
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Checker.NoVerdictTree
import ConAgua.Front.ApplyDeclRefine
import ConAgua.Front.IndApplyRefine
import ConAgua.Front.IndInstallRefine3
import ConAgua.Front.IndInstallRefine4
public import ConAgua.Front.IndApplySpec2
public import ConAgua.Front.IndFieldsSpec
import all ConAgua.Front.IndApply

@[expose] public section

/-!
# The frontend's records, word by word, II: an inductive line (lane `pipeline`)

`apply_ind`'s unified model and refinement (`applyInd_ref`): a successful `apply_ind` (on
con-leche's `ok` path of the block's scan) is the twin's `.ind` arm and appends one record of kind
`6` whose block offset is the old top of `DLP` plus one, changing neither the old records nor the
pool up to its old top (`DGrow`); its failure is the line's verdict. `installW_grow` is the first part of
`installW_twin`'s proof (`IndInstallRefine5.lean`, up to the record's push): the frames come out of
the twin's install loop (`instGo_twin`), so the twin's hypotheses stay.
-/

set_option experimental.vcgen true

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open Std.WP
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec CVRec RuleRec DeclRec scanIndDecl)


namespace L.Front.Ind

/-- **`install_ind_d` appends one inductive record.** -/
theorem installW_grow {b : ByteArray} {n : Nat} {m m' : Mem} (a : AState) {st : StateD}
    (hD : StateDR m st)
    {to tn co cn ro rn oo np : Word} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} {ordered : List IndCtorRec}
    (hF : IndFR b m to tn co cn ro rn tys cts rcs) (hIFR : topN m IFR < 2 ^ 62)
    (hIFL : topN m IFL < 2 ^ 62) (hord : ordered.length = cts.length)
    (hoo : oo.toNat + cts.length < 2 ^ 63)
    (hptr : ∀ p (hp : p < ordered.length), ∃ k, ∃ _ : k < cts.length,
      wd m IFL (oo.toNat + p) = co + 10 * UInt64.ofNat k ∧ ordered[p] = cts[k])
    (h : installW n b.data m to tn oo cn ro rn np = some m') : DGrow m m' := by
  sorry

theorem DGrow.ofDK {m m₁ m' : Mem} (hk : DK m m₁) (hg : DGrow m₁ m') : DGrow m m' := by
  have hc : dcnt m₁ = dcnt m := by simp only [dcnt, hk.1]
  have ht : dtop m₁ = dtop m := by simp only [dtop, hk.2]
  refine ⟨fun j h1 h2 => ?_, fun j h1 h2 => ?_, fun x h1 h2 => hg.new x (by omega) h2⟩
  · rw [hg.decl j h1 (by omega), hk.1]
  · rw [hg.dlp j h1 (by omega), hk.2]

/-! ## `apply_ind`: one model and one refinement -/

/-- **`apply_ind`'s unified model**: `ind_fields` and `install_ind_d` (outside the verdict closure)
lifted, `validate_ind_d` through its run (the install needs the input bytes kept, `Keep`, which
comes from the run). -/
l_model applyInd_specE (p : Prog) (hf : p.lookup "apply_ind" = some applyInd)
  fns [hf ↦ applyIndE] specs [callW_spec p n "ind_fields", callW_spec p n "install_ind_d"]
  grind [arena_grind] unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `validateIndD`'s verdict is the `.ind` line's. -/
theorem claimR_of_validate {st : StateD} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} {a : AState} {e : Err}
    (h : VerdictClaimL (ConRon.Arena.Frontend.validateIndD st tys cts rcs) a e) :
    VerdictClaimR (applyRecord st (.decl (.ind tys cts rcs))) a e := by
  intro hk
  have hrun : (applyRecord st (.decl (.ind tys cts rcs))).run a =
      (processLineCoreD st (.ind tys cts rcs)).run a := rfl
  rcases h hk with ⟨ce, hce, hc⟩ | ⟨v, a', hv, hc⟩
  · refine .inl ⟨ce, ?_, hc⟩
    rw [hrun]; unfold processLineCoreD
    simp only [StateT.run_bind, show (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = _ from hce]
    rfl
  · refine .inr ⟨v, a', ?_, hc⟩
    rw [hrun]; unfold processLineCoreD
    simp only [StateT.run_bind, show (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = _ from hv]
    rfl

/-- What `apply_ind`'s error arms assume: the no-verdict closure (the lifted callees,
`validate_ind_d`'s spec) and the twin's name reads (`validate_ref`'s `XV`). -/
structure ApplyIndG (p : Prog) (st : StateD) (a : AState) : Prop where
  nv : closedNV p _root_.L.Checker.nvFns = true
  xv : XV st a

/-- What a successful `apply_ind` from `m` gives at `m'`: the twin's `.ind` arm accepts (the state
`a` unchanged) at a related state, the arena kept, the mode kept, one record appended. -/
structure ApplyIndPost (st : StateD) (a : AState) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) (m m' : Mem) : Prop where
  twin : ∃ st', (processLineCoreD st (.ind tys cts rcs)).run a = .ok (.inl st', a) ∧ StateDR m' st'
  arena : ArenaD m' a
  mode : ModeOK m → ModeOK m'
  grow : DGrow m m'

/-- **`apply_ind` refines the `.ind` arm of `processLineCoreD`, both outcomes**: on con-leche's
`ok` path of the block's scan (`scanIndDecl`), `ind_fields` gives the three lists
(`indFields_link`), `validate_ind_d` the twin's `validateIndD` (`validate_ref`: its verdict
`.inr (ordered, nPd)`, or its record verdict, the line's), `install_ind_d` its `installIndD`
(`installW_twin`, `installW_grow`). -/
@[refines_part ConRon.Arena.Frontend.processLineCoreD "inductive"]
theorem applyInd_ref {p : Prog} (hAL : IndApplyLookups p) (hFI : IndFieldLookups p)
    (hII : IndInstallLookups p) {b : ByteArray} (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) {m : Mem} {a : AState} {st : StateD} (hm : m.arr8 IN = b.data)
    (hA : ArenaD m a) (hD : StateDR m st) (hok : ConRon.Bridge.StateOK a) {v : USize}
    {tys : List IndTypeRec} {cts : List IndCtorRec} {rcs : List IndRecRec} {e : USize}
    (hscan : scanIndDecl b v = .ok (.ind tys cts rcs) e) :
    RefC (ApplyIndG p st a) (applyIndE p n m v.toUInt64) (fun x => ApplyIndPost st a tys cts rcs m x.2)
      (VerdictClaimR (applyRecord st (.decl (.ind tys cts rcs))) a) := by
  sorry

end L.Front.Ind
