import ConAgua.Arena.IndT.Sum2
import ConAgua.Verdict.IndBE
import ConAgua.Arena.IndT.Install7
import ConAgua.Verdict.IndBTbl

/-!
# Part B's claims in the shapes `check_ind_decl`'s claim takes (lane `verdicts-b`, helper `fin`)

`cid_claim3` (IndA8.lean) takes the `indB` callees' claims as the generated statements of
IndBE.lean (`err_stmt`: every fuel `F ≤ 2 ^ 62`, the error of a `callE`), `CheckStructProjTableRE`
(Arena/IndRealSctC.lean, under `StageR`); part B proved them as `CoreSpecE`s (`ct_ref`, …). The bridges below restate
them, discharging the fuels part B's statements leave out (`0`, `1`: the calls run out of fuel).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- `check_constant_val`'s claim in the shape part B takes (`CcvE`), from `ccvE_okT`. -/
theorem ccvE_of {p : Prog} (hq : KnotStageProg p) (hp : ValProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p) (hUL : UceLookups p) :
    CcvE p :=
  fun _n hn _s₀ _a₀ _q _cv hS hqd hqb hlps hCr =>
    CoreSpecE.of_runs fun _e hc => ccvE_okT hq hp hap hkp hnv hcE hUL hn hc hS hqd hqb hlps hCr

theorem checkStructProjTableRE_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) :
    CheckStructProjTableRE p :=
  fun hT hApd F _hF {_dn _vis _fe} m a _T _C _lo _ll _nP _nF _rs _go _gl _cvCaw _lps _guards _cvCa hS hTH hCH hrs hnP
      hlps hlpsb hg hgb hcv hA hst hks _TP hTP _ctyP hcty _e hc =>
    CoreSpecE.of_callE (checkStructProjTable_claim (s₀ := ⟨m, Locals.init []⟩) hT hApd hnv F a hS hTH
      hCH hrs hnP hlps hlpsb hg hgb hcv hA hst hks hTP hcty) hc

/-- `check_sum_tele`'s claim in the generated shape (`CheckSumTeleE`): `ct_ref`'s error half. -/
theorem checkSumTeleE_of {p : Prog} (hG : CtsG p) : CheckSumTeleE p :=
  fun hkp {_dn vis _fe _env} henv hV hApd hCrk h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
      h19 h20 hI1 hAb hcst hst s₀ a₀ cv n cvTa0 cvv cvTa hC hcv hcvb hcvs hta htab htas hA {_cvP _cvTaP} hcvP
      hcvTaP hws hfe F hF _e hc =>
    RefE.run_err (ctE_spec p hV ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, hI1⟩, h9, h10, h11, h12, h13, h14, h15,
        h16, h17, h18, h19, h20, hAb⟩, hst, hcst⟩ F s₀ vis cv n cvTa0) hG.nv hG
      (ct_ref hkp henv hApd hCrk ⟨h1, h2, h3, h4, h5, h6, h7, h8, hI1⟩ F hF s₀.mem a₀ cv n cvTa0 cvv cvTa hC
        hcv hcvb hcvs hta htab htas hA hcvP hcvTaP hws hfe) hc

theorem checkSumCtorsE_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hcE : CoreStubsE p) (hCcv : CcvE p) : CheckSumCtorsE p :=
  fun hkp {_dn _vis _fe _env} henv hV hOpf hLC hLT hApd hCrk P s₀ a₀ vis0 T lo ll nP nIdx rs isP lg cvTaw cO cL lps cvTa cs
      hC hT hrs hlps hlpsb hcv hcs hA {_env₀ _TP _lpsP _rsP _cvTaP _csP} hTP hlpsP hrsP hcvP hws hcsP hie hfe F hF _e hc =>
    RefE.run_err (sctsE_spec p P F s₀ vis0 _ T lo ll nP nIdx rs isP lg cvTaw cO cL) hnv ⟨⟨hnv, hcE⟩, hCcv⟩
      (scts_ref hkp henv hV hOpf hLC hLT hApd hCrk P vis0 T lo ll nP nIdx rs isP lg cvTaw lps cvTa hT hrs hws F hF
        s₀.mem a₀ cO cL cs _ hC hlps hlpsb hcv hcs hA hTP hlpsP hrsP hcvP hcsP hie hfe) hc

theorem checkStructFieldSortsIE_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hcE : CoreStubsE p) : CheckStructFieldSortsIE p := by
  intro hkp _ _ _ _ henv hLC hLT hg hpw het hsc hcfs hgo hia hcsf hftd s₀ a₀ isProp large s nP fo fl io il
    nW fvs idxArgs hC hA hfv hfvb hix hixb hs _ hsP hnW _ hfvsP hws F hF e hc
  cases F with
  | zero =>
    obtain ⟨e', h0, hk⟩ := callE_zero p _ _ s₀.mem
    rw [h0] at hc; cases hc
    exact ErrClaim.of_cls0 hk
  | succ F =>
    exact CoreSpecE.of_callE (checkStructFieldSortsI_claim hkp henv hLC hLT hnv hcE hg hpw het hsc hcfs
      hgo hia hcsf hftd F (by omega) s₀ a₀ isProp large s nP fo fl io il nW fvs idxArgs hC hA hfv hfvb
      hix hixb hs hsP hnW hfvsP hws) hc

end L.Ind
