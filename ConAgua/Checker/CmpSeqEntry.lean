module

public import ConAgua.Arena.JustifyIface
public import ConAgua.Arena.CoreCaches
public import ConAgua.Arena.CheckerL
public import ConAgua.Arena.Globals

@[expose] public section

/-!
# The sequential compared run's job phases in place (lane compare2, design (i), the sJ variant)

After mode `6` (`check_c3(0)`: the challenge's index state `sI`, the header only) the region holds
the challenge's view: its stream index rows `EIX*`/`TIX*`, `FIRSTS`, `DECL`, `DLP`, the index's
words `CTL[128]`, `CTL[162‥173]` and the flag `CTL[224] = 1`; the solution's rows `SIX*`/`STX*`
and its stashed `SDECL`, `SFIRSTS`, `SDLP`, `SCTL` (`cmp_sstash`). Both phases' jobs run there,
in place, on the one store:

* mode `8`, `check_bs()`: the **bank switch to the solution's view** by small copies (never the
  store): the challenge's index rows (`2 · count` words per name kind), records, firsts and
  declaration pool (each the larger of the two extents) and its index words go to the `C*` stash
  arrays, the extents to `CCTL`; the solution's are copied in (`SIX*` → `EIX*`, `STX*` → `TIX*`,
  `SDECL`, `SFIRSTS`, `SDLP`; `CTL[128]` := the solution's counter `CTL[225]`, `CTL[162‥173]` :=
  `SCTL`'s, the flag `CTL[224] := 0`); then the solution's jobs `PLO‥PHI - 1` as `check_b`.
* mode `9`, `check_bc()`: the **switch back**: the challenge's view restored from the stash at the
  extents mode `8` used; then the challenge's jobs as `check_b`, on the worker state the
  solution's jobs left (the twin's `TwinComparesAccepts`).

The jobs never store to the stream index's rows, `FIRSTS`, the solution's rows or those `CTL`
words (`Checker/CmpSeqW.lean`), nor to the stash arrays, so the restore is exact.
-/

namespace L.Checker

open L L.Arena L.Front

/-- `cq_swap_rows(c, d, s, ca)`: the challenge's rows of one name kind kept (`d` → `c`) and the
solution's copied in (`s` → `d`), `2 · CTL[ca]` words each; returns the extent. -/
-- con-ron: none — the compared run's phase boundary (con-ron keeps the solution's index in its own driver state)
@[no_expose] def cqSwapRowsG (c d s : ArrId) (ca : Word) : FunDecl := lfn () locals (n) {
  n := CTL.u64[⟪ca⟫];
  if 4611686018427387904 <= n { abort };
  n := 2 * n;
  copy!(c.u64, 0, d.u64, 0, n);
  copy!(d.u64, 0, s.u64, 0, n);
  return n
}

/-- `cq_back_rows(c, d, n)`: the challenge's rows restored (`c` → `d`, `n` words). -/
-- con-ron: none — the compared run's phase boundary (con-ron keeps the solution's index in its own driver state)
@[no_expose] def cqBackG (c d : ArrId) : FunDecl := lfn (n) locals () {
  copy!(d.u64, 0, c.u64, 0, n);
  return 0
}

/-- `cq_bank_s()`: the challenge's rows, records, firsts and declaration pool kept in the `C*`
stash arrays and the solution's copied in, the extents in `CCTL[0‥8]`. -/
-- con-ron: none — the compared run's phase boundary (con-ron keeps two driver states)
@[no_expose] def cqBankSL : FunDecl := lfn () locals (n, a, b) {
  n := call cq_swap_eixa(); CCTL.u64[0] := n; n := call cq_swap_tixa(); CCTL.u64[1] := n;
  n := call cq_swap_eixs(); CCTL.u64[2] := n; n := call cq_swap_tixs(); CCTL.u64[3] := n;
  n := call cq_swap_eixn(); CCTL.u64[4] := n; n := call cq_swap_tixn(); CCTL.u64[5] := n;
  a := DECL.u64[0];
  b := SDECL.u64[0];
  if a < b { a := b };
  if 576460752303423488 <= a { abort };
  n := 1 + 8 * a;
  CCTL.u64[6] := n;
  copy!(CDECL.u64, 0, DECL.u64, 0, n);
  copy!(DECL.u64, 0, SDECL.u64, 0, n);
  CCTL.u64[7] := a;
  copy!(CFIRSTS.u64, 0, FIRSTS.u64, 0, a);
  copy!(FIRSTS.u64, 0, SFIRSTS.u64, 0, a);
  a := DLP.u64[0];
  b := SDLP.u64[0];
  if a < b { a := b };
  if 576460752303423488 <= a { abort };
  n := 1 + a;
  CCTL.u64[8] := n;
  copy!(CDLP.u64, 0, DLP.u64, 0, n);
  copy!(DLP.u64, 0, SDLP.u64, 0, n);
  return 0
}

/-- `cq_ctl_s()`: the challenge's index words kept in `CCTL[16‥29]`, the solution's in `CTL`
(the counter `CTL[225]`, `SCTL[162‥173]`, the flag `0`). -/
-- con-ron: none — the compared run's phase boundary (con-ron keeps two driver states)
@[no_expose] def cqCtlSL : FunDecl := lfn () locals () {
  CCTL.u64[16] := CTL.u64[128];
  CTL.u64[128] := CTL.u64[225];
  CCTL.u64[17] := CTL.u64[162]; CTL.u64[162] := SCTL.u64[162];
  CCTL.u64[18] := CTL.u64[163]; CTL.u64[163] := SCTL.u64[163];
  CCTL.u64[19] := CTL.u64[164]; CTL.u64[164] := SCTL.u64[164];
  CCTL.u64[20] := CTL.u64[165]; CTL.u64[165] := SCTL.u64[165];
  CCTL.u64[21] := CTL.u64[166]; CTL.u64[166] := SCTL.u64[166];
  CCTL.u64[22] := CTL.u64[167]; CTL.u64[167] := SCTL.u64[167];
  CCTL.u64[23] := CTL.u64[168]; CTL.u64[168] := SCTL.u64[168];
  CCTL.u64[24] := CTL.u64[169]; CTL.u64[169] := SCTL.u64[169];
  CCTL.u64[25] := CTL.u64[170]; CTL.u64[170] := SCTL.u64[170];
  CCTL.u64[26] := CTL.u64[171]; CTL.u64[171] := SCTL.u64[171];
  CCTL.u64[27] := CTL.u64[172]; CTL.u64[172] := SCTL.u64[172];
  CCTL.u64[28] := CTL.u64[173]; CTL.u64[173] := SCTL.u64[173];
  CCTL.u64[29] := CTL.u64[224];
  CTL.u64[224] := 0;
  return 0
}

/-- `check_bs()`: the bank switch to the solution's view, then its jobs `PLO‥PHI - 1`. -/
-- con-ron: none — the compared run's phase boundary (con-ron keeps two driver states) and the worker's jobs (`check_b`)
@[no_expose] def checkBSL : FunDecl := lfn () locals (z) {
  z := call cq_bank_s();
  z := call cq_ctl_s();
  z := call flush_caches();
  if DECL.u64[0] < PHI { abort };
  if PHI < PLO { abort };
  z := call check_jobs(PLO, PHI);
  return 71757147230292
}

/-- `cq_bank_c()`: the challenge's rows, records, firsts and declaration pool restored from the
stash at the extents `cq_bank_s` used. -/
-- con-ron: none — the compared run's phase boundary (con-ron keeps two driver states)
@[no_expose] def cqBankCL : FunDecl := lfn () locals (z, n) {
  z := call cq_back_eixa(CCTL.u64[0]); z := call cq_back_tixa(CCTL.u64[1]);
  z := call cq_back_eixs(CCTL.u64[2]); z := call cq_back_tixs(CCTL.u64[3]);
  z := call cq_back_eixn(CCTL.u64[4]); z := call cq_back_tixn(CCTL.u64[5]);
  n := CCTL.u64[6];
  copy!(DECL.u64, 0, CDECL.u64, 0, n);
  n := CCTL.u64[7];
  copy!(FIRSTS.u64, 0, CFIRSTS.u64, 0, n);
  n := CCTL.u64[8];
  copy!(DLP.u64, 0, CDLP.u64, 0, n);
  return 0
}

/-- `cq_ctl_c()`: the challenge's index words restored from `CCTL[16‥29]`. -/
-- con-ron: none — the compared run's phase boundary (con-ron keeps two driver states)
@[no_expose] def cqCtlCL : FunDecl := lfn () locals () {
  CTL.u64[128] := CCTL.u64[16];
  CTL.u64[162] := CCTL.u64[17];
  CTL.u64[163] := CCTL.u64[18];
  CTL.u64[164] := CCTL.u64[19];
  CTL.u64[165] := CCTL.u64[20];
  CTL.u64[166] := CCTL.u64[21];
  CTL.u64[167] := CCTL.u64[22];
  CTL.u64[168] := CCTL.u64[23];
  CTL.u64[169] := CCTL.u64[24];
  CTL.u64[170] := CCTL.u64[25];
  CTL.u64[171] := CCTL.u64[26];
  CTL.u64[172] := CCTL.u64[27];
  CTL.u64[173] := CCTL.u64[28];
  CTL.u64[224] := CCTL.u64[29];
  return 0
}

/-- `check_bc()`: the challenge's view restored from the stash, then its jobs `PLO‥PHI - 1`. -/
-- con-ron: none — the compared run's phase boundary (con-ron keeps two driver states) and the worker's jobs (`check_b`)
@[no_expose] def checkBCL : FunDecl := lfn () locals (z) {
  z := call cq_bank_c();
  z := call cq_ctl_c();
  z := call flush_caches();
  if DECL.u64[0] < PHI { abort };
  if PHI < PLO { abort };
  z := call check_jobs(PLO, PHI);
  return 71757147230292
}

/-- The sequential compared run's job phases. -/
def cmpSeqProg : Prog :=
  [("check_bs", checkBSL), ("check_bc", checkBCL), ("cq_bank_s", cqBankSL), ("cq_ctl_s", cqCtlSL),
   ("cq_bank_c", cqBankCL), ("cq_ctl_c", cqCtlCL),
   ("cq_swap_eixa", cqSwapRowsG CEIXA EIXA SIXA 34), ("cq_swap_tixa", cqSwapRowsG CTIXA TIXA STXA 34),
   ("cq_swap_eixs", cqSwapRowsG CEIXS EIXS SIXS 36), ("cq_swap_tixs", cqSwapRowsG CTIXS TIXS STXS 36),
   ("cq_swap_eixn", cqSwapRowsG CEIXN EIXN SIXN 38), ("cq_swap_tixn", cqSwapRowsG CTIXN TIXN STXN 38),
   ("cq_back_eixa", cqBackG CEIXA EIXA), ("cq_back_tixa", cqBackG CTIXA TIXA),
   ("cq_back_eixs", cqBackG CEIXS EIXS), ("cq_back_tixs", cqBackG CTIXS TIXS),
   ("cq_back_eixn", cqBackG CEIXN EIXN), ("cq_back_tixn", cqBackG CTIXN TIXN)]

example : nanonCS.ca = 34 ∧ nstrCS.ca = 36 ∧ nnumCS.ca = 38 := ⟨rfl, rfl, rfl⟩

end L.Checker
