module

public import ConAgua.Front.IndApplyRefine7
public import ConAgua.Front.IndApplyRefine5
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Front.IndApplyRefine

@[expose] public section

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
  recs : ∀ r ∈ (if (tys.any fun x => x.numNested != 0) = true then [] else rcs),
    RecOK st a TN TT nPd tys.length ordered.length KE fuel r

theorem storeFuel_run (a : AState) :
    (ConRon.Arena.Frontend.storeFuel).run a = .ok (a.store.nodeCount + 1, a) := by rfl

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

theorem fpos_full (LS : List (List NIdx)) : fpos LS LS.length = LS.flatten.length := by
  rw [fpos, List.take_length]
  induction LS with
  | nil => rfl
  | cons l L ih =>
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append]
    rw [ih]

theorem fpos_lt (LS : List (List NIdx)) (i c : Nat) (hi : i < LS.length) (hc : c < LS[i].length) :
    fpos LS i + c < LS.flatten.length := by
  induction LS generalizing i with
  | nil => simp at hi
  | cons l L ih =>
    cases i with
    | zero => simp [fpos] at hc ⊢; omega
    | succ i =>
      have := ih i (by simpa using hi) (by simpa using hc)
      simp only [fpos, List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons,
        List.length_append] at this ⊢
      omega

theorem getElem_flatten' (LS : List (List NIdx)) (i c : Nat) (hi : i < LS.length) (hc : c < LS[i].length) :
    LS[i][c] = LS.flatten[fpos LS i + c]'(fpos_lt LS i c hi hc) := by
  induction LS generalizing i with
  | nil => simp at hi
  | cons l L ih =>
    cases i with
    | zero => simp [fpos, List.getElem_append_left (show c < l.length by simpa using hc)]
    | succ i =>
      have h1 := ih i (by simpa using hi) (by simpa using hc)
      simp only [List.getElem_cons_succ] at h1 ⊢
      rw [h1]
      simp only [List.flatten_cons]
      rw [List.getElem_append_right (by simp only [fpos, List.take_succ_cons, List.map_cons, List.sum_cons]; omega)]
      congr 1
      simp only [fpos, List.take_succ_cons, List.map_cons, List.sum_cons]; omega

theorem flat_pos (LS : List (List NIdx)) (p : Nat) (hp : p < LS.flatten.length) :
    ∃ i c, ∃ (hi : i < LS.length), c < LS[i].length ∧ fpos LS i + c = p := by
  induction LS generalizing p with
  | nil => simp at hp
  | cons l L ih =>
    by_cases hpl : p < l.length
    · exact ⟨0, p, by simp, by simpa using hpl, by simp [fpos]⟩
    · obtain ⟨i, c, hi, hc, he⟩ := ih (p - l.length) (by rw [List.flatten_cons, List.length_append] at hp; omega)
      refine ⟨i + 1, c, by simpa using hi, by simpa using hc, ?_⟩
      simp only [fpos, List.take_succ_cons, List.map_cons, List.sum_cons] at he ⊢
      omega

theorem take_push {α : Type} (l : List α) (p : Nat) (hp : p < l.length) :
    (l.take p).toArray.push l[p] = (l.take (p + 1)).toArray := by
  rw [List.take_add_one, List.getElem?_eq_getElem hp]; simp

set_option hygiene false in
/-- The recursor loop of `validateIndD`, once `kExpected?` is `KE`. -/
macro "recs_tac" : tactic => `(tactic| (
  rw [run_bind _ _ a _ (forIn_yield' _ a _ _
    (fun _ => ((none : Option (RecordVerdict ⊕ List IndCtorRec × Nat)), ())) rfl ?rstep)]
  case rstep =>
    intro j hj
    obtain ⟨rn, hrn, h1, h2, h3, hk, v, hv, hin⟩ := hV.recs _ (List.getElem_mem hj)
    rw [run_bind _ _ a _ hrn]
    simp only [h1, h2, h3, beq_self_eq_true, ite_true]
    rcases hK : KE with _ | kE
    all_goals (try simp only [hk _ hK, beq_self_eq_true, ite_true])
    all_goals
      rw [run_bind _ _ a _ hv]
      rcases v with _ | ⟨T, sv⟩ | ⟨T, nv⟩
      · rfl
      · by_cases hsv : sv = "rec"
        · subst hsv
          simp only []
          rw [run_bind _ _ a _ (forIn_yield' _ a _ _
            (fun _ => ((none : Option (RecordVerdict ⊕ List IndCtorRec × Nat)), ())) rfl ?_)]
          · rfl
          · intro j' hj'
            simp only [List.getElem_zip]
            have hj2 := hj'
            rw [List.length_zip] at hj2
            have hj1 : j' < TN.length := by omega
            by_cases hT : TN[j']'hj1 = T
            · obtain ⟨o, ho, hon⟩ := hin T rfl j' (by omega) (by omega) hT
              simp only [hT, beq_self_eq_true, ite_true]
              rw [run_bind _ _ a _ ho]
              cases o with
              | none => rfl
              | some x => simp only [hon x rfl, beq_self_eq_true, ite_true]; rfl
            · simp only [hT, beq_iff_eq, ite_false]
              rfl
        · split
          · rename_i heq
            simp only [NNodeView.str.injEq] at heq
            exact absurd heq.2 hsv
          · rfl
      · rfl
  rfl))

theorem validateIndD_ok {st : StateD} {a : AState} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} {TN : List NIdx} {TT : List EIdx} {LS : List (List NIdx)} {CN : List NIdx}
    {fuel nPd : Nat} {ordered : List IndCtorRec} {KE : Option Bool}
    (hV : VFacts st a tys cts rcs TN TT LS CN fuel nPd ordered KE) :
    (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = .ok (.inr (ordered, nPd), a) := by
  sorry

end L.Front.Ind
