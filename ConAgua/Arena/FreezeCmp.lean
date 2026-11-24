module

public import ConAgua.Arena.Freeze
meta import ConAgua.Arena.Freeze

@[expose] public section

/-!
# The compared run's frozen buffer: one image set, two headers (lane compare, design (i))

Mode `7` (`check_c3(1)`, `Checker/CompareEntry.lean`) ends, at the challenge's index state, with
`par_compact(1, hdrW)`: **header C** at `OUT[hdrW‥)` (the challenge's phase, as the flat header:
offsets relative to it) and the images of every frozen array after it. Then `cmp_hdr_s(lc)`
(`lc` header C's buffer length) writes **header S** at `OUT[0‥hdrW)` for the solution's phase,
over the same images:

* the store arrays, the pool, the columns, `PINS`, `EREC`: header C's entries (the offsets moved
  by `hdrW`, header S sitting `hdrW` words before header C);
* `EIX*`/`TIX*` (the stream index the jobs read): the images of the solution's rows `SIX*`/`STX*`;
  the solution's rows themselves `(·, 0)` (the solution's jobs run with no solution);
* `CTLF`, `FIRSTS`, `DECL`, `DLP`: four more images after header C's buffer: the seed (`CTL[0‥256)`
  with the solution's words patched: `128` := the solution's index counter `CTL[225]`,
  `162‥173` := `SCTL`'s, `224` := `0`), and the solution's stashed `SFIRSTS`, `SDECL`, `SDLP`
  (`cmp_sstash`);
* word `1` the whole buffer's length, `2` the solution's records `SDECL[0]`, `3` `CTL[225]`, `5`
  header C's offset `hdrW` (a flat buffer has `0`).
-/

namespace L.Arena

open L

/-- How header S's entry `i` is made from header C's: `same j` (entry `j`'s offset and length),
`zero j` (entry `j`'s offset, length `0`), `extra` (an image of its own). -/
inductive HsE where
  | same (j : Nat)
  | zero (j : Nat)
  | extra
  deriving DecidableEq, Repr

/-- The index of frozen id `a` in `frozen`. -/
def fzIdx (a : ArrId) : Nat := frozen.findIdx (·.1 == a)

/-- **Header S's entries** from header C's. -/
def hsE (i : Nat) : HsE :=
  match frozen[i]? with
  | none => .extra
  | some (a, _) =>
    if a = CTLF ∨ a = FIRSTS ∨ a = L.Front.DECL ∨ a = L.Front.DLP then .extra
    else if a = EIXA then .same (fzIdx SIXA) else if a = EIXS then .same (fzIdx SIXS)
    else if a = EIXN then .same (fzIdx SIXN) else if a = TIXA then .same (fzIdx STXA)
    else if a = TIXS then .same (fzIdx STXS) else if a = TIXN then .same (fzIdx STXN)
    else if a = SIXA ∨ a = SIXS ∨ a = SIXN ∨ a = STXA ∨ a = STXS ∨ a = STXN ∨ a = MATA ∨ a = MATS ∨
      a = MATN then .zero i
    else .same i

/-- Header C's word `k` (header C at `OUT[hdrW‥)`). -/
def hcW (k : Nat) : Expr := .ld64 OUT (fzC (hdrW + k))

/-- Header S's entry `i`, from header C's. -/
def hsStmt (i : Nat) : Stmt :=
  match hsE i with
  | .same j => .seq (.st64 OUT (fzC (10 + 2 * i)) (.bin .add (hcW (10 + 2 * j)) (fzC hdrW)))
      (.st64 OUT (fzC (11 + 2 * i)) (hcW (11 + 2 * j)))
  | .zero j => .seq (.st64 OUT (fzC (10 + 2 * i)) (.bin .add (hcW (10 + 2 * j)) (fzC hdrW)))
      (.st64 OUT (fzC (11 + 2 * i)) (fzC 0))
  | .extra => .skip

/-- The solution's images of header S (`cmp_hdr_s`'s calls `fzs_i`): (header entry, source, extent). -/
def fzsImgs : List (Nat × Fz) :=
  [(fzIdx FIRSTS, ⟨L.Checker.SFIRSTS, .ld64 L.Checker.SDECL (fzC 0)⟩),
   (fzIdx L.Front.DECL, ⟨L.Checker.SDECL, .bin .add (fzC 1) (.bin .mul (fzC 8) (.ld64 L.Checker.SDECL (fzC 0)))⟩),
   (fzIdx L.Front.DLP, ⟨L.Checker.SDLP, .bin .add (fzC 1) (.ld64 L.Checker.SDLP (fzC 0))⟩)]

/-- The name of the solution's image function for header entry `i`. -/
def fzsName : Nat → FnName
  | 60 => "fzs_60"
  | 61 => "fzs_61"
  | 62 => "fzs_62"
  | i => "fzs_" ++ toString i

/-- con-ron: none — the compared run's phase boundary (con-ron runs the solution's jobs on its own tables)

The solution's image function for header entry `i` (an image of `fzsImgs`). -/
@[no_expose] def fzsF (i : Nat) : FunDecl :=
  match fzsImgs.find? (·.1 == i) with
  | some (_, z) => fzPreG z.src z.e i
  | none => { nparams := 3, nlocals := 3, body := .abort (.const 0) }

/-- The seed's words the solution's phase takes from its own time (`SCTL`). -/
def hsSeedW : List Nat := (List.range 12).map (162 + ·)

/-- con-ron: none — the compared run's phase boundary (con-ron keeps two driver states)

`cmp_hdr_s(lc)`: header S at `OUT[0‥hdrW)` over header C's images (`lc` header C's buffer length),
with the solution's seed, firsts, records and declaration pool as images after header C's buffer;
returns the whole buffer's length. Locals `lc o so`. -/
@[no_expose] def cmpHdrSL : FunDecl :=
  let w (k : Nat) (v : Expr) : Stmt := .st64 OUT (fzC k) v
  let ws (k : Nat) (v : Expr) : Stmt := .st64 OUT (.bin .add (.var 2) (fzC k)) v
  let body : Stmt :=
    .seq (.set 1 (.bin .add (fzC hdrW) (.var 0))) <|
    .seq ((List.range frozen.length).foldr (fun i s => .seq (hsStmt i) s) .skip) <|
    .seq (.set 2 (.var 1)) <|
    .seq (.call [1] (fzName 0) [.var 1, fzC 1, fzC 0]) <|
    .seq ((fzsImgs.map fun x => Stmt.call [1] (fzsName x.1) [.var 1, fzC 1, fzC 0]).foldr .seq .skip) <|
    .seq (ws 128 (fzCtl 225)) <|
    .seq ((hsSeedW.map fun k => ws k (.ld64 L.Checker.SCTL (fzC k))).foldr .seq .skip) <|
    .seq (ws 224 (fzC 0)) <|
    .seq (w 0 (.const fzMagic)) <|
    .seq (w 1 (.var 1)) <|
    .seq (w 2 (.ld64 L.Checker.SDECL (fzC 0))) <|
    .seq (w 3 (fzCtl 225)) <|
    .seq (w 4 (fzC frozen.length)) <|
    .seq (w 5 (fzC hdrW)) <|
    .seq (w 8 (fzC 0)) <|
    .seq (w 9 (fzC hdrW)) <|
    .ret [.var 1]
  { nparams := 1, nlocals := 3, body }

/-- `hdrW` as a word (header C's offset). -/
def hdrWW : Word := 154

#guard hdrWW.toNat = hdrW
#guard fzsImgs.map (·.1) = [60, 61, 62]
#guard (List.range frozen.length).filter (hsE · == .extra) = [0, 60, 61, 62]

end L.Arena
