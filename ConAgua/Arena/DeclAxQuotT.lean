import ConAgua.Arena.DeclArmT
import ConAgua.Arena.DeclArmAxiom
import ConAgua.Arena.StageC

/-!
# The axiom and quotient arms under `StageT` (lane `loopt3`, helper `loopt3-axq`)

`check_decl_axiom` (`cdaW`, `DeclArmAxiom.lean`) and `check_decl_quot` (`cdqW`,
`DeclArmQuot.lean`) from `StageT`, back to the stage relation and the core's memos (option (a),
replacing the interim contract `stubArm_keepsCoreMemos` for these two arms).

Every call of the two arms but `check_constant_val` is a leaf of the declaration loop (`leafFns`:
`erec_ci`, the ROM block reader, `quot_pin_hit`, `check_basis_decl`, `ci_canon_eq`,
`std_axiom_ok`, `trust_compiler_ok`, `of_reduce_ax_ok`, `env_push`; `pin_at` is pure). So no
`TwinOK` or con-ron `CheckOK` has to be carried past a core call: the arms' `StageR` proofs
(`cdaW_gen`, `cdqW_gen`, with a memory invariant `J`) run with `J := CoreMemos`, kept by the
leaves' frame (`LeafClosed`) and by `erec_ci`'s (`erecCiW_frame`), and given by the one core call,
the constant check, under `StageT` (`checkConstantVal_refinesT`: `TwinOK` at its entry from the
arm's `StageT` across `erec_ci`'s frame). The twin's `StateOK` is needed only at the arm's entry
(the ROM reader, the canonical comparisons), where the loop has it.

The quotient readers' precondition `NamesDn dn a quotNames` (journal `loopt2`, landing 5) comes
from the loop-start fact `QuotDn dn` (`Quot`'s `sortZ` name `u` has a handle under the record
pool's name decoder) and `TwinOK`'s `den.dnN` (that handle reads back to `u` in the twin's name
store); the quotient record's `denoteCV` from the record's denotation (`TwinFold.den`).
-/

open ConRon.Arena


namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)

local notation "V" => ConLeche.CheckMode.verified

/-- **`Quot`'s `sortZ` name has a handle** under the record pool's name decoder `dn` (a fact about
the startup store, state-free; the loop threads it from its start). -/
def QuotDn (dn : NIdx → Option ConLeche.Name) : Prop := ∃ k, dn k = some (.str .anonymous "u")

/-- The quotient readers' precondition from `QuotDn` and the decoder's agreement with the twin's
name store (`TwinMem.dnN`, i.e. `TwinOK.den.dnN`). -/
theorem QuotDn.namesDn {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState}
    (hq : QuotDn dn) (hT : TwinMem dn m a) : L.Rom.NamesDn dn a L.Rom.quotNames := by
  intro x hx
  simp only [L.Rom.quotNames, List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  obtain ⟨k, hk⟩ := hq
  exact ⟨k, hk, hT.dnN k _ hk⟩

/-- `erec_ci` keeps the core's memos. -/
theorem erecCiW_memos {n : Nat} {m m' : Mem} {i ck : Word} {r : List Word}
    (h : erecCiW n m i ck = some (r, m')) (hM : CoreMemos m) : CoreMemos m' :=
  hM.frame (erecCiW_frame h) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩

/-- A leaf call keeps the core's memos. -/
theorem leaf_memos {p : Prog} (hcl : LeafClosed p) {f : FnName} (hf : f ∈ leafFns) {k : Nat}
    {args : List Word} {x y : Mem} {rx : List Word} (hc : callW p k f args x = some (rx, y))
    (hM : CoreMemos x) : CoreMemos y :=
  hM.frame (callW_leafFrame hcl hf hc) leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp

/-- **The axiom arm under `StageT`** (`cdaW_ok`'s, con-ron's `checkDecl_bridge_axiom`'s
decomposition): from `StageT`, the twin state's `StateOK` and `QuotDn`; the arm's run, the stage
relation after it (at the pushed environment, or unchanged for `Quot.sound` and `sorryAx`), and
the core's memos. -/
@[refines_part ConRon.Arena.checkDecl "the axiom arm, under StageT"]
theorem cdaW_okT {p : Prog} (hX : AxProg p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hap : ApdF p) (hkp : CrKeep p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) (hQd : QuotDn dn) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {i : Word}
    {r : List Word} {ds : Array IDeclaration} {pins : List INatOpPinSet} {cv : IConstantVal}
    (h : cdaW p n m i vis = some (r, m')) (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .axiomDecl cv) (hok : ConRon.Bridge.StateOK a) {c : ConLeche.ConstantVal}
    (hcvd : Frontend.denoteCV a.store cv = some c) (hCr : L.Stubs.CrOK m) :
    ∃ fe' a', (checkDecl V pins fe (.axiomDecl cv)).run a = .ok (fe', a') ∧
      StageR dn (r.headD 0) fe' m' a' ∧ CoreMemos m' ∧ IWGrow m m' := by
  obtain ⟨fe', a', h1, h2, h3, h4⟩ := cdaW_gen (pins := pins) hX hdn CoreMemos
    (fun e hx => erecCiW_memos e hx)
    (fun {f} _ _ _ _ _ hf hc hx => leaf_memos hcl (by
      simp only [cdaLeaves, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> exact leaf_mem _ rfl) hc hx)
    (fun {k} {r1} {r3} {m1} {m3} hk e1 hS1 hcv1 hqb e3 => by
      have hf := erecCiW_frame e1
      have hT1 : StageT dn vis fe m1 a :=
        ⟨hS1, hS.twin.frame hf ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩,
          by simp only [pinW, hf.1 PINS (by decide) (by decide)]; exact hS.flag⟩
      obtain ⟨s3, hs3, -, hok3, hS3, hg3, -⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
        (checkConstantVal_refinesT p hX.val hq hap hkp k (by omega) ⟨m1, Locals.init []⟩ a dn fe vis
          (r1.headD 0 + 1) cv hT1 hcv1 (by
            have : (r1.headD 0 + 1).toNat = (r1.headD 0).toNat + 1 :=
              toNat_add_small _ 1 (by omega)
            omega) (denoteCV_lps hcvd) (CrOK.frame hCr hf (by decide) (by decide))) e3
      subst hs3
      exact ⟨hok3, hS3.stage, hg3, hS3.twin.memos⟩)
    h hS.stage hS.twin.memos hD hi hd hok (hQd.namesDn hS.twin.mem)
  exact ⟨fe', a', h1, h2, h4, h3⟩

/-- **The quotient arm under `StageT`** (`cdqW_ok`'s, con-ron's `checkDecl_bridge_quot`'s): from
`StageT`, the twin state's `StateOK`, `QuotDn` and the record's denotation; the arm's run, the
stage relation after it, and the core's memos (every call of the arm is a leaf). -/
@[refines_part ConRon.Arena.checkDecl "the quotient arm, under StageT"]
theorem cdqW_okT {p : Prog} (hQ : QuotProg p) (hcl : LeafClosed p)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) (hQd : QuotDn dn) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {i : Word} {r : List Word}
    {ds : Array IDeclaration} {pins : List INatOpPinSet} {k : ConLeche.QuotKind}
    {cv : IConstantVal} (h : cdqW p n m i vis = some (r, m')) (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .quotDecl k cv) (hok : ConRon.Bridge.StateOK a)
    (hden : ∃ x, Frontend.denoteDecl a.store (.quotDecl k cv) = some x) :
    ∃ fe' a', (checkDecl V pins fe (.quotDecl k cv)).run a = .ok (fe', a') ∧
      StageR dn (r.headD 0) fe' m' a' ∧ CoreMemos m' ∧ IWGrow m m' := by
  have hcvD : ∃ c, Frontend.denoteCV a.store cv = some c := by
    obtain ⟨x, hx⟩ := hden
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
    obtain ⟨c, hc, -⟩ := hx
    exact ⟨c, hc⟩
  obtain ⟨fe', a', h1, h2, h3, h4⟩ := cdqW_gen (pins := pins) hQ hdn CoreMemos
    (fun e hx => erecCiW_memos e hx)
    (fun {f} _ _ _ _ _ hf hc hx => leaf_memos hcl (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;> exact leaf_mem _ rfl) hc hx)
    h hS.stage hS.twin.memos hD hi hd hok (hQd.namesDn hS.twin.mem) hcvD
  exact ⟨fe', a', h1, h2, h4, h3⟩

end L.Arena
