import ConAgua.Arena.IndInstallSpec41
import ConAgua.Arena.IndInstallSpec28

/-!
# Refinements of `IndInstall`, part 31 (lane `indproofs3`, helper `tail`): `checkBlockTail`, the
relation

`ictlW_sim`: the tail's model refines `checkBlockTail` from the pass's record (`BPassR`), the
stage relation at its environment, the raw block decoded, and the `hb` memo well formed.

**Pending (no census tag yet):** `cons_block_recs_tf` enters as `ConsRecsTFSim p`, the `Sim` fact
the tail needs of it, an argument until helper `indproofs3-rec`'s refinement of `consBlockRecsTF`
lands (then it is that theorem). `check_block_rec` enters through `checkBlockRec_refines`
(`IndInstallSpec41`, through `genRecCheck_refines`).

**Hypotheses beyond the stage relation and the decodings** (each the caller's):
* `HbMemo m` (for the projection tables' `struct_proj_guards`), returned for the memory after;
* `closedA p hbFreeA hbFreeC fs` with the six callees in `fs` (a program fact: `decide +kernel` at
  `checkerProg`), so that the callees with no memo lemma keep the `hb` memo;
* for `check_block_rec` (`genRecCheck_refines`' own): the recursor check's walk memos well formed
  (`RcMR m`, carried to the call by the write set `closedA p rcFreeA rcFreeC fsR` of the callees
  before it, `tailRcCallees`), the shape's recursor slice below the top (`RecsB`), the classes'
  constructors' level-parameter slices in `EREC` (`ClassesLp`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **What the tail needs of `cons_block_recs_tf(vis2, p, 0, out.off, out.len, vis)`**: from the
stage relation at `vis` of `fe`, the shape and the recursor stage's output decoded below the tops,
and the `hb` memo, a returning run is `consBlockRecsTF` at the view `vis2`. (To be discharged by
helper `indproofs3-rec`'s refinement.) -/
def ConsRecsTFSim (p : Prog) : Prop :=
  ∀ (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis vis2 pp : Word) (fe : IFEnv) (m : Mem) (a : AState)
    (bs : BlockShape) (rr : List Word) (outs : List (IConstantVal × TargetMajor × List EIdx)),
    StageR dn vis fe m a → DecB (fun m => decBS m pp.toNat) m bs → decRRS m rr outs → HbMemo m → AbsOK m →
    Sim (callW p n "cons_block_recs_tf" [vis2, pp, 0, rr.headD 0, rr.tail.headD 0, vis] m)
      (ConRon.Arena.consBlockRecsTF vis2.toNat bs 0 outs fe) a
      (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m' ∧ HbMemo m' ∧ AbsOK m')

/-- Replace the model by one that returns whatever it returns. -/
theorem _root_.L.Arena.Sim.of_model {β α : Type} {mo mo' : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} (h : ∀ r m', mo = some (r, m') → mo' = some (r, m'))
    (hs : Sim mo' op a Q) : Sim mo op a Q := fun r m' e => hs r m' (h r m' e)

/-- The lookups of `check_block_tail`. -/
structure TailProg (p : Prog) : Prop where
  idx : IdxProg p
  recp : RecProg p
  hci : p.lookup "ctor_info_rec" = some ctorInfoRecL
  hcs : p.lookup "cons_sum_ctors" = some consSumCtorsL
  hcbc : p.lookup "cons_block_ctors" = some consBlockCtors
  flush : FlushProg p
  nf : p.lookup "nest_field_kind_flat" = some nestFieldKindFlat
  ni : p.lookup "nest_kinds_flat_inner" = some nestKindsFlatInner
  nm : p.lookup "nest_kinds_flat_mid" = some nestKindsFlatMid
  nk : p.lookup "nest_kinds_flat" = some nestKindsFlat
  ng : p.lookup "block_nested_bit_go" = some blockNestedBitGo
  nb : p.lookup "block_nested_bit" = some blockNestedBit
  crec : p.lookup "check_block_rec" = some checkBlockRec
  tailrec : p.lookup "check_block_tail_rec" = some checkBlockTailRec
  grc : GrcProg p
  tabs : TabsProg p
  tail : p.lookup "check_block_tail" = some checkBlockTail

/-- The callees whose program text keeps the recursor check's walk memos: the tail's before
`check_block_rec`, and `gen_rec_check`'s. -/
def tailRcCallees : List FnName :=
  ["check_block_idx_sorts", "cons_block_ctors", "flush_caches", "block_nested_bit", "target_rec_pins",
    "class_stream_recs"]

/-- The tail's callees with no memo lemma. -/
def tailCallees : List FnName :=
  ["check_block_idx_sorts", "cons_block_ctors", "block_nested_bit", "check_block_rec", "cons_block_recs_tf"]

/-- **The pass's record at `q`**: decoded below the tops at `fe` (whose view `vis` is word 0), its
slices and the shape's members below the top. -/
def BPassR (vis : Word) (fe : IFEnv) (m : Mem) (q : Word) (bp : BlockPass) : Prop :=
  DecB (fun m => decBPass fe m q.toNat) m bp ∧ BPassB m q.toNat ∧ rdW (m.arr64 IW) q = vis ∧
    ShapeSrc m (rdW (m.arr64 IW) (q + 3))

theorem tailToNat {q : Word} {k : Nat} (h : q.toNat + k < 2 ^ 64) :
    (q + UInt64.ofNat k).toNat = q.toNat + k := by
  have hs : UInt64.size = 2 ^ 64 := rfl
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega)]; exact Nat.mod_eq_of_lt h

end L.Ind
