import ConAgua.Front.IndApplyRefine7

/-!
# `validateIndD` from clean facts

`validateIndD_ok`: the twin's validation of an inductive block succeeds with `.inr (ordered, nPd)`
from facts about its pieces (`VFacts`): the lookups' results, the order's per-constructor checks
(`CtorOK`), `kExpected?`'s value, the recursors' checks (`RecOK`). No L here: the facts are
established from the L models in `IndApplyRefine9.lean`.
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)

set_option linter.unusedSimpArgs false

namespace L.Front.Ind

/-- The position of type `i`'s first constructor in the flattened list. -/
def fpos (LS : List (List NIdx)) (i : Nat) : Nat := ((LS.take i).map List.length).sum

/-- **What the validation's pieces return.** -/
structure VFacts (st : StateD) (a : AState) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) (TN : List NIdx) (TT : List EIdx) (LS : List (List NIdx))
    (CN : List NIdx) (fuel nPd : Nat) (ordered : List IndCtorRec) (KE : Option Bool) : Prop where
  safe : (tys.any fun x => x.isUnsafe) = false
  np1 : nPd = (tys.map fun x => x.numParams).head?.getD 0
  np2 : ((tys.map fun x => x.numParams).all fun x => x == nPd) = true
  tn : (tys.mapM fun t : IndTypeRec => st.name t.cv.name).run a = .ok (TN, a)
  tt : (tys.mapM fun t : IndTypeRec => getDeclD st t.cv.type).run a = .ok (TT, a)
  ls : (tys.mapM fun t : IndTypeRec => t.ctors.mapM st.name).run a = .ok (LS, a)
  cn : (cts.mapM fun c : IndCtorRec => st.name c.cv.name).run a = .ok (CN, a)
  nodup : LS.flatten.Nodup
  flen : LS.flatten.length = cts.length
  hfuel : a.store.nodeCount + 1 = fuel
  tnlen : TN.length = tys.length
  ttlen : TT.length = tys.length
  lslen : LS.length = tys.length
  ordlen : ordered.length = cts.length
  order : ∀ i (hi : i < LS.length) c (hc : c < LS[i].length),
    ∃ k, ∃ _ : fpos LS i + c < ordered.length, ordered[fpos LS i + c] = cts[k]! ∧
      CtorOK st a cts CN LS[i][c] c (TN[i]!) nPd fuel k
  kno : ¬ (TT.length = 1 ∧ (LS.map List.length) = [1]) → KE = some false
  kyes : ∀ ty h c, TT = [ty] → LS = [[h]] → ordered = [c] →
    ∃ r v, (ConRon.Arena.Frontend.piResultD fuel ty).run a = .ok (r, a) ∧ (view r).run a = .ok (v, a) ∧
      ((∀ s, v ≠ .sort s) → KE = none) ∧
      ∀ s, v = .sort s → ∃ L, (readLevel s).run a = .ok (L, a) ∧
        KE = some (c.numFields == 0 && ConLeche.Level.isEquiv L .zero == some true)
  recs : ∀ r ∈ (if (tys.any fun x => x.numNested != 0) = true then [] else rcs),
    RecOK st a TN TT nPd tys.length ordered.length KE fuel r

theorem storeFuel_run (a : AState) :
    (ConRon.Arena.Frontend.storeFuel).run a = .ok (a.store.nodeCount + 1, a) := rfl

/-- A read-only `forIn` that yields at every element, from any initial state equal to `S 0`. -/
theorem forIn_yield' {α β : Type} (f : α → β → AM (ForInStep β)) (a : AState) (xs : List α)
    (init : β) (S : Nat → β) (h0 : S 0 = init)
    (h : ∀ i (hi : i < xs.length), (f xs[i] (S i)).run a = .ok (.yield (S (i + 1)), a)) :
    (forIn xs init f).run a = .ok (S xs.length, a) := by
  subst h0; exact forIn_yield f a xs S h

theorem fpos_succ (LS : List (List NIdx)) (i : Nat) (hi : i < LS.length) :
    fpos LS (i + 1) = fpos LS i + LS[i].length := by
  unfold fpos
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]

theorem take_push {α : Type} (l : List α) (p : Nat) (hp : p < l.length) :
    (l.take p).toArray.push l[p] = (l.take (p + 1)).toArray := by
  rw [List.take_succ, List.getElem?_eq_getElem hp]; simp

theorem validateIndD_ok {st : StateD} {a : AState} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} {TN : List NIdx} {TT : List EIdx} {LS : List (List NIdx)} {CN : List NIdx}
    {fuel nPd : Nat} {ordered : List IndCtorRec} {KE : Option Bool}
    (hV : VFacts st a tys cts rcs TN TT LS CN fuel nPd ordered KE) :
    (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = .ok (.inr (ordered, nPd), a) := by
  unfold ConRon.Arena.Frontend.validateIndD
  simp only [hV.safe, Bool.false_eq_true, if_false]
  rw [← hV.np1, if_pos hV.np2]
  rw [run_bind _ _ a _ hV.tn, run_bind _ _ a _ hV.tt, run_bind _ _ a _ hV.ls, run_bind _ _ a _ hV.cn]
  rw [if_pos hV.nodup]
  simp only [hV.flen, beq_self_eq_true, if_true]
  rw [run_bind _ _ a _ (storeFuel_run a), hV.hfuel]
  rw [run_bind _ _ a _ (forIn_yield' _ a _ _ (fun i => ((none : Option (RecordVerdict ⊕ List IndCtorRec × Nat)),
    (ordered.take (fpos LS i)).toArray)) ?h0 ?hstep)]
  case h0 => simp [fpos]
  case hstep =>
    intro i hi
    simp only [List.getElem_zip]
    rw [run_bind _ _ a _ (forIn_yield' _ a _ _ (fun c => ((none : Option (RecordVerdict ⊕ List IndCtorRec × Nat)),
      (ordered.take (fpos LS i + c)).toArray, c)) ?i0 ?istep)]
    case i0 => simp
    case istep =>
      intro c hc
      have hi' : i < LS.length := by simp at hi; omega
      have hiT : i < TN.length := by simp at hi; omega
      obtain ⟨k, hp, hord, hk, hfold, hcidx, hind, cty, hcty, htele⟩ := hV.order i hi' c hc
      have hck : cts[k]! = cts[k] := getElem!_pos cts k hk
      rw [hck] at hord
      have hTNi : TN[i]! = TN[i] := getElem!_pos TN i hiT
      rw [hTNi] at hind
      have hA : cts.toArray[k]? = some cts[k] := by simp [hk]
      have hpush : (ordered.take (fpos LS i + c)).toArray.push cts[k] =
          (ordered.take (fpos LS i + (c + 1))).toArray := by
        rw [← hord, take_push _ _ hp, Nat.add_assoc]
      simp only [hfold, hA]
      cases hci : cts[k].cidx <;> cases hiw : cts[k].induct
      · simp only [run_bind _ _ a _ hcty, run_bind _ _ a _ htele, beq_self_eq_true, if_true, hpush]; rfl
      · simp only [run_bind _ _ a _ (hind _ hiw), beq_self_eq_true, if_true,
          run_bind _ _ a _ hcty, run_bind _ _ a _ htele, hpush]; rfl
      · simp only [hcidx _ hci, beq_self_eq_true, if_true, run_bind _ _ a _ hcty,
          run_bind _ _ a _ htele, hpush]; rfl
      · simp only [hcidx _ hci, run_bind _ _ a _ (hind _ hiw), beq_self_eq_true, if_true,
          run_bind _ _ a _ hcty, run_bind _ _ a _ htele, hpush]; rfl
    have hi' : i < LS.length := by simp at hi; omega
    simp only [fpos_succ LS i hi']
    rfl
  sorry

end L.Front.Ind
