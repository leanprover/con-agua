import ConAgua.Arena.WhnfIota
import ConAgua.Arena.PinsNatOp
import ConAgua.Arena.WhnfCoreRefine

/-!
# ι-reduction: proofs of `WhnfIota.lean`'s specs (primed)

Each theorem here is the `WhnfIota.lean` statement of the same name, primed, with the program
hypotheses made explicit (the lane owner swaps them in).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Decoding rule records -/

theorem decRule_fields (a : Array Word) (q : Nat) (rl : IRecRule) (h : decRule a q = some rl) :
    (∃ w, a[q]? = some w ∧ w.toNat < 2 ^ 32 ∧ rl.ctor = decI w) ∧
    ∃ w, a[q + 9]? = some w ∧ rl.k = (w != 0) := by
  simp only [decRule, hd?, nat?, bool?, Option.bind_eq_bind] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨x, ⟨y, hy, rfl⟩, h⟩ := h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at h
    grind
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at h
    grind
  · simp at h

theorem mapM_option_get {α β : Type} (f : α → Option β) : ∀ (l : List α) (rs : List β),
    l.mapM f = some rs → rs.length = l.length ∧ ∀ j (hj : j < l.length), f l[j] = rs[j]? := by
  intro l
  induction l with
  | nil => intro rs h; simp at h; subst h; simp
  | cons x l ih =>
    intro rs h
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨y, hy, ys, hys, h⟩ := h
    cases h
    obtain ⟨h1, h2⟩ := ih ys hys
    refine ⟨by simp [h1], fun j hj => ?_⟩
    cases j with
    | zero => simp [hy]
    | succ j => simpa using h2 j (by simpa using hj)

theorem decRules_get (a : Array Word) (off cnt : Nat) (rs : List IRecRule)
    (h : decRules a off cnt = some rs) :
    rs.length = cnt ∧ ∀ j, j < cnt → decRule a (off + 11 * j) = rs[j]? := by
  obtain ⟨h1, h2⟩ := mapM_option_get _ _ _ h
  simp at h1
  exact ⟨h1, fun j hj => by have := h2 j (by simpa using hj); simpa [List.getElem_range] using this⟩

/-- The model's index arithmetic does not wrap on a decoded record. -/
theorem rule_idx (a : Array Word) (ro i : Word) (rl : IRecRule)
    (hsz : a.size < 2 ^ 64) (h : decRule a (ro.toNat + 11 * i.toNat) = some rl) :
    (ro + 11 * i).toNat = ro.toNat + 11 * i.toNat ∧ ro.toNat + 11 * i.toNat < a.size := by
  obtain ⟨⟨w, hw, _⟩, _⟩ := decRule_fields a _ rl h
  have hlt : ro.toNat + 11 * i.toNat < a.size := by
    have := (Array.getElem?_eq_some_iff.mp hw).1; exact this
  refine ⟨?_, hlt⟩
  rw [UInt64.toNat_add, UInt64.toNat_mul]
  simp
  omega

/-! ## `find_rule(ro, rc, c)` -/

/-- Model of the `find_rule` scan from index `i` with step bound `K` (`rc - i`). -/
def frW (E : Array Word) (ro rc c : Word) : Nat → Word → Option (List Word)
  | 0, _ => some [0, 0]
  | K + 1, i =>
    if i < rc then
      if h : (ro + 11 * i).toNat < E.size then
        if E[(ro + 11 * i).toNat] = c then some [1, ro + 11 * i] else frW E ro rc c K (i + 1)
      else none
    else some [0, 0]

theorem uint64_succ_toNat (n i : Word) (h : i < n) : (i + 1).toNat = i.toNat + 1 := by
  rw [UInt64.toNat_add]; simp
  have := n.toNat_lt
  have : i.toNat < n.toNat := h
  omega

theorem frW_done (E : Array Word) (ro rc c i : Word) (h : ¬ i < rc) :
    frW E ro rc c (rc.toNat - i.toNat) i = some [0, 0] := by
  cases hK : rc.toNat - i.toNat with
  | zero => rw [frW]
  | succ k => rw [frW]; simp [h]

theorem frW_step (E : Array Word) (ro rc c i : Word) (h : i < rc) :
    frW E ro rc c (rc.toNat - i.toNat) i =
      if h : (ro + 11 * i).toNat < E.size then
        if E[(ro + 11 * i).toNat] = c then some [1, ro + 11 * i]
        else frW E ro rc c (rc.toNat - (i + 1).toNat) (i + 1)
      else none := by
  have h1 := uint64_succ_toNat rc i h
  have : i.toNat < rc.toNat := h
  have hK : rc.toNat - i.toNat = (rc.toNat - (i + 1).toNat) + 1 := by omega
  rw [hK, frW]
  simp [h]

theorem findRuleLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k findRuleLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      frW (s₀.mem.arr64 EREC) (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) ((s₀.loc 1).toNat - (s₀.loc 3).toNat)
        (s₀.loc 3) = some (r.retOr [0, 0]); ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := findRuleLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish [frW_done, frW_step]

theorem findRuleLoop_step_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p k) findRuleLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      frW (s₀.mem.arr64 EREC) (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) ((s₀.loc 1).toNat - (s₀.loc 3).toNat)
        (s₀.loc 3) = some (r.retOr [0, 0]); ⊤⦄ :=
  Triple.step_exec (findRuleLoop_spec p (k + 1) s₀)

theorem findRule_spec (p : Prog) (hp : p.lookup "find_rule" = some findRuleL) (k : Nat)
    (s₀ : St) (ro rc c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p k) "find_rule" [ro, rc, c]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      frW (s₀.mem.arr64 EREC) ro rc c rc.toNat 0 = some r; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, findRuleL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, findRuleLoop_step_spec p k] <;>
      finish

/-- **The scan model computes `findRule`.** -/
theorem frW_rel (E : Array Word) (hsz : E.size < 2 ^ 64) (ro rc c : Word) (hc : HW c)
    (rules : List IRecRule) (hlen : rules.length = rc.toNat)
    (hget : ∀ j, j < rc.toNat → decRule E (ro.toNat + 11 * j) = rules[j]?) :
    ∀ (K : Nat) (i : Word) (L : List Word), rc.toNat - i.toNat = K →
      frW E ro rc c K i = some L →
      findRule (rules.drop i.toNat) (decI c) =
        (if L.headD 0 = 0 then none else decRule E (L.tail.headD 0).toNat) := by
  intro K
  induction K with
  | zero =>
    intro i L hK h
    rw [frW] at h
    cases h
    have : rules.drop i.toNat = [] := List.drop_eq_nil_of_le (by omega)
    simp [this, findRule]
  | succ K ih =>
    intro i L hK h
    have hi : i < rc := by
      have : i.toNat < rc.toNat := by omega
      exact this
    have hi' : i.toNat < rc.toNat := hi
    obtain ⟨rl, hrl⟩ : ∃ rl, rules[i.toNat]? = some rl :=
      ⟨rules[i.toNat], List.getElem?_eq_getElem (by omega)⟩
    have hdr := hget i.toNat hi'
    rw [hrl] at hdr
    obtain ⟨hw, hlt⟩ := rule_idx E ro i rl hsz hdr
    have hdrop : rules.drop i.toNat = rl :: rules.drop (i.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by omega)]
      simp [List.getElem?_eq_some_iff.mp hrl |>.2]
    obtain ⟨⟨w, hwE, hw32, hctor⟩, _⟩ := decRule_fields E _ rl hdr
    have hwE' : E[ro.toNat + 11 * i.toNat] = w := (Array.getElem?_eq_some_iff.mp hwE).2
    rw [frW] at h
    simp only [hi, ite_true, hw, hlt, dite_true] at h
    rw [hdrop, findRule]
    split at h
    · rename_i hEq
      cases h
      have hEq' : w = c := hwE'.symm.trans hEq
      subst hEq'
      simp [hctor, hw, hdr]
    · rename_i hEq
      have hne : ¬ w = c := fun e => hEq (hwE'.trans e)
      have hbeq : (rl.ctor == decI c) = false := by
        rw [hctor, decI_beq _ _ hw32 hc]; simpa using hne
      have h1 : (i + 1).toNat = i.toNat + 1 := uint64_succ_toNat rc i hi
      rw [hbeq]
      simp only [Bool.false_eq_true, ite_false]
      have := ih (i + 1) L (by omega) h
      rwa [h1] at this

/-- **`find_rule` refines `findRule`.** `HW c` (`decI` truncates) and a size bound on the pool
(the index arithmetic `ro + 11 * i` does not wrap) are added to the statement. -/
theorem findRule_refines' (p : Prog) (hp : p.lookup "find_rule" = some findRuleL) (n : Nat)
    (s₀ : St) (ro rc c : Word) (rules : List IRecRule) (hc : HW c)
    (hsz : (s₀.mem.arr64 EREC).size < 2 ^ 64)
    (hr : decRules (s₀.mem.arr64 EREC) ro.toNat rc.toNat = some rules) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "find_rule" [ro, rc, c]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      findRule rules (decI c) = decRuleAt s₀.mem (r.headD 0) (r.tail.headD 0); ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hmem, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (findRule_spec p hp n s₀ ro rc c)
  obtain ⟨hl, hg⟩ := decRules_get _ _ _ _ hr
  have := frW_rel _ hsz ro rc c hc rules hl hg _ 0 r rfl hW
  refine ⟨hmem, hloc, ?_⟩
  simpa [decRuleAt] using this

/-! ## `rec_rule_k(ro, rc)` -/

/-- Model of `rec_rule_k`. -/
def rrkW (E : Array Word) (ro rc : Word) : Option Word :=
  if rc ≠ 1 then some 0
  else if h : (ro + 9).toNat < E.size then some E[(ro + 9).toNat] else none

theorem recRuleK_spec (p : Prog) (hp : p.lookup "rec_rule_k" = some recRuleKL) (k : Nat)
    (s₀ : St) (ro rc : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p k) "rec_rule_k" [ro, rc]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      rrkW (s₀.mem.arr64 EREC) ro rc = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, recRuleKL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;> finish [rrkW]

/-- **`rec_rule_k` refines `recRuleK`.** -/
theorem recRuleK_refines' (p : Prog) (hp : p.lookup "rec_rule_k" = some recRuleKL) (n : Nat)
    (s₀ : St) (ro rc : Word) (rules : List IRecRule)
    (hsz : (s₀.mem.arr64 EREC).size < 2 ^ 64)
    (hr : decRules (s₀.mem.arr64 EREC) ro.toNat rc.toNat = some rules) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rec_rule_k" [ro, rc]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ (r.headD 0 != 0) = recRuleK rules; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hmem, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (recRuleK_spec p hp n s₀ ro rc)
  refine ⟨hmem, hloc, ?_⟩
  obtain ⟨hl, hg⟩ := decRules_get _ _ _ _ hr
  by_cases h1 : rc = 1
  · subst h1
    have hl1 : rules.length = 1 := by simpa using hl
    obtain ⟨rl, rfl⟩ : ∃ rl, rules = [rl] := by
      match rules, hl1 with
      | [x], _ => exact ⟨x, rfl⟩
    have hg0 := hg 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem?_cons_zero] at hg0
    obtain ⟨_, w, hw, hk⟩ := decRule_fields _ _ rl hg0
    have hlt := (Array.getElem?_eq_some_iff.mp hw).1
    have hro : (ro + 9).toNat = ro.toNat + 9 := by
      rw [UInt64.toNat_add]; simp; omega
    have hb : (ro + 9).toNat < (s₀.mem.arr64 EREC).size := by rw [hro]; exact hlt
    simp only [rrkW, ne_eq, not_true_eq_false, ↓reduceIte, hb, ↓reduceDIte, Option.some.injEq] at hW
    have hv : (s₀.mem.arr64 EREC)[ro.toNat + 9] = w := (Array.getElem?_eq_some_iff.mp hw).2
    simp only [recRuleK, hk]
    rw [← hW]
    simp only [hro]
    rw [hv]
  · simp only [rrkW, h1, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq] at hW
    rw [← hW]
    have : rc.toNat ≠ 1 := fun h => h1 (UInt64.toNat_inj.mp (by simpa using h))
    simp only [recRuleK]
    match rules, hl with
    | [], _ => simp
    | [x], hl => simp at hl; omega
    | _ :: _ :: _, _ => simp

/-! ## Pure reads -/

/-- **A run that reads only**: the twin's run leaves the state as it was, and the L run the
memory. -/
theorem CoreRef.of_pure {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} {v : α}
    (hS : CoreS dn m₀ a₀ vis fe M eb) (hrun : T.run a₀ = .ok (v, a₀)) (hm : m = m₀)
    (hv : v = dec r) (hr : ok r) : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  subst hm
  exact ⟨hok, by rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, by rw [hres, hv], hr⟩

/-! ## `is_str_lit(h)` -/

/-- Model of `is_str_lit`. -/
def islW (m : Mem) (h : Word) : Option Word :=
  if h >>> 28 ≠ 8 then some 0
  else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h then none
  else some (if rdW (m.arr64 REC) (idxW h * 8 + tierW h * 4) = 1 then 1 else 0)

theorem isStrLit_spec (p : Prog) (hp : p.lookup "is_str_lit" = some isStrLitL) (k : Nat)
    (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p k) "is_str_lit" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ islW s₀.mem h = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, isStrLitL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;> finish [islW, tierW, idxW]

theorem viewLit_ok (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h 2) :
    ∃ l, a.store.viewLit (decE h) = some l ∧ RecRel m (tierW h) (idxW h) ⟨l⟩ := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h litSch RecRel litH (·.lits) _ hR.lit.2 hv.2
  refine ⟨k.l, ?_, hkr⟩
  simp only [EStore.viewLit, EStore.persGetLit]
  rw [proj_tier m a hR h hh (fun t i => t.getLit i) hv.1]
  simp only [ETables.getLit, Tbl.node?, decE_idx]
  rw [hk]; rfl

theorem decE_tag_lit (e : Word) (hh : e.toNat < 2 ^ 32) : ((decE e).tag = ETag.lit) ↔ e >>> 28 = 8 :=
  decE_tag_eq e hh 8 (by decide)

theorem isStrLit_run_not (a : AState) (e : EIdx) (h : e.tag ≠ ETag.lit) :
    (isStrLit e).run a = .ok (false, a) := by
  simp [isStrLit, h]; rfl

theorem isStrLit_run_lit (a : AState) (e : EIdx) (h : e.tag = ETag.lit) (l : ConLeche.Literal)
    (hl : a.store.viewLit e = some l) :
    (isStrLit e).run a = .ok (match l with | .strVal _ => true | _ => false, a) := by
  cases l <;> simp [isStrLit, h, viewLit, hl, StateT.run_bind, StateT.run_get] <;> rfl

/-- **`is_str_lit` refines `isStrLit`.** -/
theorem isStrLit_refines' (p : Prog) (hp : p.lookup "is_str_lit" = some isStrLitL) :
    IsStrLitOK p := by
  intro n s₀ a₀ dn vis fe MM eb h hS hh
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hmem, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (isStrLit_spec p hp n s₀ h)
  refine ⟨hloc, ?_⟩
  have hR := hS.arena.1
  unfold islW at hW
  by_cases h8 : h >>> 28 = 8
  · simp only [h8, ne_eq, not_true_eq_false, ↓reduceIte] at hW
    by_cases hv1 : tierW h ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
    · simp [hv1] at hW
    simp only [hv1, ↓reduceIte] at hW
    by_cases hv2 : rdW (s₀.mem.arr64 CTL) (2 + tierW h) ≤ idxW h
    · simp [hv2] at hW
    simp only [hv2, ↓reduceIte, Option.some.injEq] at hW
    obtain ⟨l, hl, hrel⟩ := viewLit_ok s₀.mem a₀ hR h hh ⟨hv1, UInt64.not_le.mp hv2⟩
    refine CoreRef.of_pure hS (isStrLit_run_lit a₀ _ ((decE_tag_lit h hh).mpr h8) l hl) hmem ?_ ?_
    · cases l with
      | natVal N =>
        have := hrel.1
        show false = _
        simp only [decBool]; rw [← hW, this]; simp
      | strVal s =>
        have := hrel.1
        show true = _
        simp only [decBool]; rw [← hW, this]; simp
    · unfold ResH HW; rw [← hW]; split <;> decide
  · simp only [ne_eq, h8, not_false_eq_true, ↓reduceIte, Option.some.injEq] at hW
    refine CoreRef.of_pure hS (isStrLit_run_not a₀ _ (fun e => h8 ((decE_tag_lit h hh).mp e))) hmem ?_ ?_
    · simp only [decBool]; rw [← hW]; rfl
    · unfold ResH HW; rw [← hW]; decide

/-! ## The program hypotheses

`IotaProg` only lists this file's own functions; the proofs also need the callees' code. The
structure grows with the functions proved. -/

structure IotaProg' (p : Prog) : Prop extends IotaProg p where
  spine : SpineProg p
  envix : p.lookup "env_ix" = some envIxL
  envrow : p.lookup "env_row_get" = some envRowGetL
  envfind : p.lookup "env_find" = some envFindL

/-! ## `is_ctor_app(vis, e)` -/

theorem view_const_f (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h 18) (hg : h >>> 28 = 3) :
    a.store.view (decE h) = some (.const (decI (rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2)))
      (decI (rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1)))) ∧
    (rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2)).toNat < 2 ^ 32 ∧
    (rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1)).toNat < 2 ^ 32 := by
  obtain ⟨k, hk, hn, hu⟩ := node_of m a h constSch CeRecRel cehash (·.consts) _ hR.const hv.2
  rw [hn, hu, decI_word, decI_word]
  exact ⟨by rw [view_tier m a hR h hh hv.1, get_const _ h hh hg, Tbl.node?, hk]; rfl, word_lt _,
    word_lt _⟩

/-- Model of `is_ctor_app`, its callees through their runs. -/
def icaW (p : Prog) (n : Nat) (m : Mem) (vis e : Word) : Option (Word × Mem) :=
  match callW p n "get_app_fn" [e] m with
  | none => none
  | some (r₁, m₁) =>
    if r₁.headD 0 >>> 28 ≠ 3 then some (0, m₁)
    else if tierW (r₁.headD 0) ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0 then none
    else if rdW (m₁.arr64 CTL) (18 + tierW (r₁.headD 0)) ≤ idxW (r₁.headD 0) then none
    else match callW p n "env_find"
        [rdW (m₁.arr64 CREC) (idxW (r₁.headD 0) * 4 + tierW (r₁.headD 0) * 2), vis] m₁ with
      | none => none
      | some (r₂, m₂) =>
        if r₂.headD 0 = 0 then some (0, m₂)
        else some (if rdW (m₂.arr64 EREC) (r₂.tail.headD 0) = 4 then 1 else 0, m₂)

theorem isCtorApp_spec (p : Prog) (hp : IotaProg' p) (n : Nat) (s₀ : St) (vis e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "is_ctor_app" [vis, e]
    ⦃fun r s' => LocEq s' s₀ ∧ icaW p n s₀.mem vis e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.isCtorApp]
  simp only [callFn, isCtorAppL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "get_app_fn", callW_spec p n "env_find"] <;>
    finish [icaW, tierW, idxW]

theorem isCtorApp_run_not (fe : IFEnv) (a : AState) (e h : EIdx)
    (hga : (getAppFn coreWalkFuel e).run a = .ok (h, a)) (ht : h.tag ≠ ETag.const) :
    (isCtorApp fe e).run a = .ok (false, a) := by
  simp only [isCtorApp, StateT.run_bind, hga, except_ok_bind]
  simp [ht]; rfl

theorem isCtorApp_run_const (fe : IFEnv) (a : AState) (e h : EIdx)
    (hga : (getAppFn coreWalkFuel e).run a = .ok (h, a)) (ht : h.tag = ETag.const)
    (c : NIdx) (us : LsIdx) (hv : a.store.view h = some (.const c us)) :
    (isCtorApp fe e).run a = .ok (match fe.find? c with | some (.ctorInfo _ _ _) => true | _ => false, a) := by
  have hv' : (view h).run a = .ok (.const c us, a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  simp only [isCtorApp, StateT.run_bind, hga, except_ok_bind]
  simp only [ht, beq_self_eq_true, ↓reduceIte, StateT.run_bind, hv', except_ok_bind]
  cases fe.find? c with
  | none => rfl
  | some ci => cases ci <;> rfl

/-- **`is_ctor_app` refines `isCtorApp`.** -/
theorem isCtorApp_refines' (p : Prog) (hp : IotaProg' p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb e : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW e →
    CoreSpec p (n + 1) "is_ctor_app" [vis, e] (isCtorApp fe (decE e)) decBool s₀ a₀ dn vis fe MM eb := by
  intro n s₀ a₀ dn vis fe MM eb e hS he
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (isCtorApp_spec p hp n s₀ vis e)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hR := hS.arena.1
  simp only [icaW] at hW
  cases hc : callW p n "get_app_fn" [e] s.mem with
  | none => simp [hc] at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  simp only [hc] at hW
  obtain ⟨t₁, ht₁, hm₁, -, hh1, hga⟩ := triple_of_callW
    (getAppFn_refines' p hp.spine.fn n s a₀ hR e he) hc
  rw [ht₁] at hm₁
  subst hm₁
  by_cases h3 : r₁.headD 0 >>> 28 ≠ 3
  · simp only [h3, ↓reduceIte, ne_eq, not_false_eq_true, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hrun' := isCtorApp_run_not fe a₀ (decE e) _ hga (fun ht => h3 (by
      have := (decE_tag_eq _ hh1 3 (by decide)).mp ht; exact this))
    refine CoreRef.of_pure hS hrun' hm.symm ?_ ?_
    · simp only [decBool]; rw [← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  have h3' : r₁.headD 0 >>> 28 = 3 := by simpa using h3
  rw [if_neg h3] at hW
  by_cases hv1 : tierW (r₁.headD 0) ≠ 0 ∧ rdW (s.mem.arr64 CTL) 1 = 0
  · rw [if_pos hv1] at hW; cases hW
  rw [if_neg hv1] at hW
  by_cases hv2 : rdW (s.mem.arr64 CTL) (18 + tierW (r₁.headD 0)) ≤ idxW (r₁.headD 0)
  · rw [if_pos hv2] at hW; cases hW
  rw [if_neg hv2] at hW
  have h3 := h3'
  obtain ⟨hvw, hn32, -⟩ := view_const_f s.mem a₀ hR (r₁.headD 0) hh1 ⟨hv1, UInt64.not_le.mp hv2⟩ h3
  generalize rdW (s.mem.arr64 CREC) (idxW (r₁.headD 0) * 4 + tierW (r₁.headD 0) * 2) = cw at hvw hn32 hW
  cases hc2 : callW p n "env_find" [cw, vis] s.mem with
  | none => rw [hc2] at hW; simp at hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  simp only [hc2] at hW
  obtain ⟨t₂, ht₂, hm₂, -, hfind⟩ := triple_of_callW
    (envFind_refines p hp.envix hp.envrow hp.envfind n s vis _ hS.env hn32) hc2
  obtain ⟨t₂', ht₂', hm₂', -, hfound⟩ := triple_of_callW
    (envFind_found p hp.envix hp.envrow hp.envfind n s vis _ hn32) hc2
  rw [ht₂] at hm₂
  have htag : (decE (r₁.headD 0)).tag = ETag.const := (decE_tag_eq _ hh1 3 (by decide)).mpr h3
  have hrun1 := isCtorApp_run_const fe a₀ (decE e) _ hga htag _ _ hvw
  subst hm₂
  by_cases h0 : r₂.headD 0 = 0
  · rw [if_pos h0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hnone : fe.find? (decI cw) = none := by rw [hfind]; simp only [decFound, h0, ↓reduceIte]
    rw [hnone] at hrun1
    refine CoreRef.of_pure hS hrun1 hm.symm ?_ ?_
    · simp only [decBool]; rw [← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg h0] at hW
  obtain ⟨htag2, hrow, hq⟩ := hfound h0
  obtain ⟨ci, hci⟩ := hS.env.found_some cw hn32 htag2 hrow
  have hfind' : fe.find? (decI cw) = some ci := by
    rw [hfind]; simp only [decFound, h0, ↓reduceIte, hq]; exact hci
  rw [← hq] at hci
  have hctor := decCI_ctor hci (erecP_ext _) hS.erec
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  rw [hfind'] at hrun1
  by_cases h4 : rdW (s.mem.arr64 EREC) (r₂.tail.headD 0) = 4
  · obtain ⟨cv, np, nf, rfl, -⟩ := hctor.1 h4
    rw [if_pos h4] at hr
    refine CoreRef.of_pure hS hrun1 hm.symm ?_ ?_
    · simp only [decBool]; rw [← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  · rw [if_neg h4] at hr
    refine CoreRef.of_pure (v := false) hS ?_ hm.symm ?_ ?_
    · rw [hrun1]
      have := hctor.2 h4
      cases ci <;> first | rfl | exact absurd rfl (this _ _ _)
    · simp only [decBool]; rw [← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide

end L.Arena
