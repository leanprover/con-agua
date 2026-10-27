import ConAgua.Arena.RecSim
import ConAgua.Arena.RecClassSpec.Classes
import ConAgua.Arena.RecGenSpec.Set64

/-!
# Stable decodings (lane `indproofs2`, helper `rec`)

`StabD f m x`: the decoding `f` gives `x` at `m` and at every memory the pool grows to. A record
built below the pool's top decodes stably; a stable decoding stays stable as the pool grows
(`StabD.grow`), so a decoded argument is carried across every callee by `IWGrow` alone.

`SPL dec m o l xs`: the `IW` pointer slice `(o, l)` lies below the top and its pointers decode
stably to `xs` (each by `dec`); `SPL.decPL` gives the `decPL`, `SPL.cons` is `sl_cons` on it.
-/

open ConRon.Arena
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **A stable decoding**: `f` gives `x` at `m` and at every memory `m` grows to. -/
def StabD {α : Type} (f : Mem → Option α) (m : Mem) (x : α) : Prop :=
  ∀ m', IWGrow m m' → f m' = some x

namespace StabD
variable {α : Type} {f : Mem → Option α} {m m' : Mem} {x : α}

theorem get (h : StabD f m x) : f m = some x := h m (IWGrow.refl m)

theorem grow (h : StabD f m x) (hg : IWGrow m m') : StabD f m' x :=
  fun m'' hg' => h m'' (hg.trans hg')

theorem of_eq (h : ∀ m', IWGrow m m' → f m' = f m) (hf : f m = some x) : StabD f m x :=
  fun m' hg => (h m' hg).trans hf

end StabD

theorem iwN_grow {m m' : Mem} (hg : IWGrow m m') {i : Nat} (hi : i < iwTop m) : iwN m' i = iwN m i := by
  simp only [iwN, nat?, iwA]; rw [hg.2.2.1 i hi]

theorem iwH_grow {k : IdxKind} {m m' : Mem} (hg : IWGrow m m') {i : Nat} (hi : i < iwTop m) :
    (iwH m' i : Option (Idx k)) = iwH m i := by
  simp only [iwH, hd?, iwA]; rw [hg.2.2.1 i hi]

/-! ## Stable pointer slices -/

/-- Two lists related elementwise. -/
inductive FA2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : FA2 R [] []
  | cons {a b as bs} : R a b → FA2 R as bs → FA2 R (a :: as) (b :: bs)

theorem FA2.imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {as : List α} {bs : List β}, FA2 R as bs → FA2 S as bs
  | _, _, .nil => .nil
  | _, _, .cons h1 h2 => .cons (h _ _ h1) (FA2.imp h h2)

theorem FA2.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, FA2 R as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h2 => by simp [FA2.length_eq h2]

/-- **A stable pointer slice**: below the top, every pointer decoding stably by `dec`. -/
def SPL {α : Type} (dec : Mem → Nat → Option α) (m : Mem) (o l : Nat) (xs : List α) : Prop :=
  o + l ≤ iwTop m ∧ ∃ ps, decNL m o l = some ps ∧
    FA2 (fun q x => StabD (fun m => dec m q) m x) ps xs

namespace SPL
variable {α : Type} {dec : Mem → Nat → Option α} {m m' : Mem} {o l : Nat} {xs : List α}

theorem nil (o : Nat) (ho : o ≤ iwTop m) : SPL dec m o 0 [] :=
  ⟨by omega, [], by simp [decNL], FA2.nil⟩

theorem grow (h : SPL dec m o l xs) (hg : IWGrow m m') : SPL dec m' o l xs := by
  obtain ⟨hb, ps, hps, hf⟩ := h
  refine ⟨Nat.le_trans hb hg.1, ps, by rw [decNL_grow hg hb]; exact hps, ?_⟩
  exact FA2.imp (fun _ _ hq => hq.grow hg) hf

theorem mapM_of_forall₂ : ∀ {ps : List Nat} {xs : List α},
    FA2 (fun q x => StabD (fun m => dec m q) m x) ps xs → ps.mapM (dec m) = some xs
  | [], [], _ => rfl
  | q :: ps, x :: xs, .cons h1 h2 => by
    simp only [List.mapM_cons, h1.get, mapM_of_forall₂ h2]; rfl

theorem decPL (h : SPL dec m o l xs) : L.Ind.decPL m (dec m) o l = some xs := by
  obtain ⟨-, ps, hps, hf⟩ := h
  rw [decPL_eq_bind, hps]; exact mapM_of_forall₂ hf

theorem length (h : SPL dec m o l xs) : xs.length = l := by
  obtain ⟨-, ps, hps, hf⟩ := h
  rw [← hf.length_eq, decNL_length m hps]

theorem stab (h : SPL dec m o l xs) : StabD (fun m => L.Ind.decPL m (dec m) o l) m xs :=
  fun _ hg => (h.grow hg).decPL

/-- `sl_cons` of a stably decoding pointer onto a stable slice. -/
theorem cons {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {x o l : Word} {r : List Word} {y : α} (h : consW n m x o l = some (r, m'))
    (hS : StageR dn vis fe m a) (hl : SPL dec m o.toNat l.toNat xs)
    (hy : StabD (fun m => dec m x.toNat) m y) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      SPL dec m' (r.headD 0).toNat (r.tail.headD 0).toNat (y :: xs) := by
  obtain ⟨hb, ps, hps, hf⟩ := hl
  obtain ⟨hS', hg, hdn, htop⟩ := consW_stageN h hS hb hps
  refine ⟨hS', hg, by omega, x.toNat :: ps, hdn, FA2.cons (hy.grow hg) ?_⟩
  exact FA2.imp (fun _ _ hq => hq.grow hg) hf

end SPL

/-! ## `sl_snoc` on a list of numbers -/

theorem decNL_snoc (m : Mem) (o l : Nat) :
    decNL m o (l + 1) = (decNL m o l).bind fun xs => (iwN m (o + l)).map fun v => xs ++ [v] := by
  simp only [decNL, List.range_succ, List.mapM_append]
  cases h : (List.range l).mapM (fun j => iwN m (o + j)) with
  | none => simp
  | some xs => cases h2 : iwN m (o + l) <;> simp [h2]

theorem snocW_decN {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} {xs : List Nat}
    (h : snocW n m o l x = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop m)
    (hxs : decNL m o.toNat l.toNat = some xs) :
    r = [rdW (m.arr64 CTL) 200, l + 1] ∧
    decNL m' (rdW (m.arr64 CTL) 200).toNat (l + 1).toNat = some (xs ++ [x.toNat]) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ (l + 1).toNat = l.toNat + 1 ∧
    (rdW (m.arr64 CTL) 200).toNat + (l + 1).toNat = iwTop m' := by
  simp only [snocW] at h
  by_cases h0 : l + 1 = 0
  · simp [h0] at h
  simp only [h0, ite_false] at h
  cases hal : allocW m (l + 1) with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  cases hcp : copyW (n - 1) m1 q o l with
  | none => simp [hcp] at h
  | some m2 =>
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq hm1
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hlm : l.toNat ≠ 2 ^ 64 - 1 := fun e => h0 (by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp [e])
  have hl1 : (l + 1).toNat = l.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; have := l.toNat_lt; omega
  rw [hl1] at hroom
  have hql : (q + l).toNat = q.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hIW := allocMem_IW m (l + 1)
  obtain ⟨hA, hS, hW, hG⟩ := copyW_get (n - 1) _ _ _ _ _ hcp (by simp only [iwTop, hqq] at hsrc; omega)
    (by rw [hIW]; omega) (by rw [hIW]; exact hsz)
  rw [hIW] at hS hG
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m (l + 1)).trans (copy_frame hA (by rw [hS, hIW]) (by first | (rw [hW]) | (rw [hW]; simp [allocMem])))
  have hfr' := hfr.trans (set64IW_frame m2 (q + l) x)
  have hget : ∀ i, ((m2.set64 IW (q + l) x).arr64 IW)[i]? =
      if i = q.toNat + l.toNat then some x
      else if q.toNat ≤ i ∧ i < q.toNat + l.toNat then (m.arr64 IW)[o.toNat + (i - q.toNat)]?
      else (m.arr64 IW)[i]? := by
    intro i
    rw [set64IW_get, hql, hS, hG i]
    by_cases h1 : i = q.toNat + l.toNat
    · rw [ite_eq_left ⟨h1, by omega⟩, ite_eq_left h1]
    · rw [ite_eq_right (by omega), ite_eq_right h1]
  have hCTL : (m2.set64 IW (q + l) x).arr64 CTL = (allocMem m (l + 1)).arr64 CTL := by
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hA CTL (by decide)]
  have htop : rdW ((m2.set64 IW (q + l) x).arr64 CTL) 200 = q + (l + 1) := by
    rw [hCTL, allocMem_top m _ hc, hqq]
  have hsum : (q + (l + 1)).toNat = q.toNat + (l.toNat + 1) := by
    rw [UInt64.toNat_add, hl1]; simp; omega
  refine ⟨rfl, ?_, ?_, hfr', hl1, ?_⟩
  · rw [hl1, decNL_snoc]
    have h1 : decNL (m2.set64 IW (q + l) x) q.toNat l.toNat = some xs := by
      rw [← hxs]; simp only [decNL]
      apply mapM_opt_congr
      intro j hj
      have hj' : j < l.toNat := List.mem_range.mp hj
      simp only [iwN, nat?, iwA, hget]
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      congr 2; omega
    have h2 : iwN (m2.set64 IW (q + l) x) (q.toNat + l.toNat) = some x.toNat := by
      simp [iwN, nat?, iwA, hget]
    rw [h1, h2]; rfl
  · refine iwGrow_of_frame hfr' (N := l + 1) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hget, ite_eq_right (by omega), ite_eq_right (by omega)]
  · simp only [iwTop, htop, hsum]; omega

end L.Ind
