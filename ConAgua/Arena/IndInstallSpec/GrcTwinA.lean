
/-!
# GrcTwinA

`grcTwinA`, `grcTwinB`, `grcTwinC`, `grcTwinR`, `rcFreeA`, `rcFreeC` and the lemmas only they use.
-/

noncomputable section
set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order
namespace L.Ind
open L.Arena
local notation "V" => ConLeche.CheckMode.verified

-- ==== Tw2.lean

section twin
variable (mode : ConLeche.CheckMode) (fe : IFEnv) (p : BlockShape) (nestedBit : Bool)
    (params : List EIdx) (tbl : List NestCtorNf) (rd : ClassRead) (ms : List TargetMajor)
    (cvTas : List IConstantVal) (block : List IConstantInfo) {β : Type}

/-- The twin's `genRecCheck`, part A: the pins, the stream's recursor types, the guards. -/
def grcTwinA (k : List IConstantVal → AM β) : AM β := do
  ConRon.Arena.targetRecPins p block
  let cvRis ← ConRon.Arena.classStreamRecs mode fe p.recs
  if p.k == 0 then
    ConRon.Arena.fail (.invalid "generated recursor: the block declares no family")
  if p.large then
    let nb := nestedBit || ms.any (·.member.isNone)
    unless ← ConRon.Arena.blockLargeElimAllowed p nb do
      ConRon.Arena.fail (.invalid "generated recursor: large eliminator on a block whose sort may be Prop \
        (official: elim_only_at_universe_zero)")
  k cvRis

/-- Part B: the classes' entries and constructors, the count, the formers, the level. -/
def grcTwinB (k : List TargetMajor → List (List ConRon.Arena.ClassCtor) → List EIdx → LIdx → AM β) :
    AM β := do
  let formerTys := cvTas.map (·.type)
  let ms2 ← ConRon.Arena.classesNfs mode fe p formerTys tbl ms
  let ctors ← ConRon.Arena.classesCtors mode fe p formerTys rd ms2 0 ms2
  unless (rd.slots.filter ConRon.Arena.ClassSlot.isMinor).length == (ctors.map List.length).sum do
    ConRon.Arena.fail (.invalid "generated recursor: the recursors' prefix has a minor premise for no \
      constructor of a class (official: invalid recursor)")
  let formerTysC ← ms2.mapM (ConRon.Arena.classFormerTy fe cvTas)
  let elim ← ConRon.Arena.structElimLevel p.elim p.large
  k ms2 ctors formerTysC elim

/-- Part C: the generator, its prefix, the recursor types. -/
def grcTwinC (cvRis : List IConstantVal) (ms2 : List TargetMajor)
    (ctors : List (List ConRon.Arena.ClassCtor)) (formerTysC : List EIdx) (elim : LIdx)
    (k : ConRon.Arena.ClassGen → List IConstantVal → AM β) : AM β := do
  let g0 : ConRon.Arena.ClassGen := ⟨p.nP, params, ms2, formerTysC, rd.slots, ctors, elim, []⟩
  match ← g0.prefixBinders with
  | none => ConRon.Arena.fail (.internal "generated recursor: recursor prefix")
  | some pre => do
    let g := { g0 with pre := pre }
    let cvGs ← ConRon.Arena.classRecTysOk mode fe g p.k p.recs cvRis rd.recCls
    k g cvGs

/-- The rest: the pushes, the rules, the pops. -/
def grcTwinR (g : ConRon.Arena.ClassGen) (cvGs : List IConstantVal) :
    AM (IFEnv × List (IConstantVal × TargetMajor × List EIdx)) := do
  let visT := fe.visibleBelow
  let (feR, prevs) := ConRon.Arena.classFeR p cvGs rd.recCls fe
  ConRon.Arena.flushCaches
  let out ← ConRon.Arena.classRecsRulesOk mode visT feR g rd.recCls cvGs cvGs rd.recCls
  let fe2 := prevs.foldr (fun (n, prev) acc => acc.popTemp n prev) feR
  ConRon.Arena.flushCaches
  pure (fe2, out)

end twin

/-! ## Memo frames from the program text -/

/-- Every word array below 320 (both tiers) but the recursor check's walk memos. -/
def rcFreeA : List ArrId := (List.range 388).filter (fun b => b ∉ [NOM, DPM, RAM, HBM, RFM, TAM])
/-- Every `CTL` word below 256 but those memos' control words. -/
def rcFreeC : List Word :=
  ((List.range 256).filter (fun c => c ∉ [204, 206, 208, 210, 212, 213, 214, 218, 219])).map Nat.toUInt64

-- ==== S41a2.lean
/-! ## `gen_rec_check`'s model -/

section model
variable (p : Prog) (n : Nat)

/-- After the second flush: `(fe2, out.off, out.len)`. -/
def gckK6 (v oo ol : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([v, oo, ol], m)

end model

-- ==== S41J.lean

/-! ## `check_block_rec` -/

end L.Ind

end
