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
  ctf : p.lookup "ct_find" = some (memoFindG ctSch)
  ctp : p.lookup "ct_put" = some (memoPutG ctSch)
  rrf : p.lookup "rr_find" = some (memoFindG rrSch)
  rrp : p.lookup "rr_put" = some (memoPutG rrSch)

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

/-! ## The relation across a memo write (`ct`, `rr`, `cv`: the constant caches)

A `find; put` into one of the constant caches writes its array (`96 ≤ arr < 128`) and its count
word `CTL[cs + 1]`; every other relation is framed, the memo's own is `memoRV_set`. -/

theorem CoreS.setMemo {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (S : MemoSch) (c : Caches)
    (hS : CoreS dn m a vis fe M eb) (hf : MemFrame [S.arr] [S.cs + 1] m m')
    (h1 : 96 ≤ S.arr) (h2 : S.arr < 128) (h3 : (96 : Nat) ≤ S.cs.toNat) (h4 : S.cs.toNat + 1 < 128)
    (hc : CoreRM m' c M eb) (hL : c.readLC = a.caches.readLC) (hLs : c.readLsC = a.caches.readLsC) :
    CoreS dn m' { a with caches := c } vis fe M eb ∧ StackKept m m' := by
  obtain ⟨ar, har⟩ : ∃ ar : Nat, ar = S.arr := ⟨_, rfl⟩
  have n1 : 96 ≤ ar := by rw [har]; exact h1
  have n2 : ar < 128 := by rw [har]; exact h2
  have aA : ∀ lo hi : Nat, hi ≤ 96 ∨ 128 ≤ lo → AvoidA lo hi [S.arr] := fun lo hi h b hb => by
    simp only [List.mem_singleton] at hb; subst hb; rw [← har]; simp only [ArrId]; omega
  have aC : ∀ lo hi : Nat, hi ≤ 96 ∨ 128 ≤ lo → AvoidC lo hi [S.cs + 1] := fun lo hi h x hx => by
    simp only [List.mem_singleton] at hx; subst hx
    have : (S.cs + 1).toNat = S.cs.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    omega
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (fun h => by simp at h; simp only [SPN] at h; rw [← har] at h; rw [← h] at n2; exact absurd n2 (by decide)) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 :=
    hf.2.1 136 (fun h => by
      simp at h
      have : (S.cs + 1).toNat = S.cs.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; omega
      have h' := congrArg UInt64.toNat h
      simp at h'; omega)
  refine ⟨⟨⟨?_, ?_⟩, hc, ?_, ?_, ?_, ?_, hS.nwf, ?_, ?_⟩, ?_⟩
  · exact (ArenaR.frame_ext [S.arr] [S.cs + 1] (fun b hb => by simp at hb; subst hb; rw [← har]; exact Nat.le_trans (by decide : 64 ≤ 96) n1)
      (fun x hx => by
        simp at hx; subst hx
        have : (S.cs + 1).toNat = S.cs.toNat + 1 := by
          rw [UInt64.toNat_add]; simp; omega
        omega) m m' hf a hS.arena.1).caches_irrel c
  · have := DerR.frameM [S.arr] [S.cs + 1] m m' hf (fun b hb => by simp at hb; subst hb; rw [← har]; exact Or.inr (Nat.lt_of_lt_of_le (by decide : 46 < 96) n1)) a hS.arena.2
    exact DerR.of_store _ _ _ this rfl
  · exact hS.pins.congr (hf.1 PINS (fun h => by simp at h; simp only [PINS] at h; rw [← har] at h; rw [← h] at n2; exact absurd n2 (by decide))
      (by decide))
  · exact hS.env.frame (aA 132 144 (Or.inr (by omega))) (aC 128 136 (Or.inr (by omega))) hf
  · intro h l e; exact hS.readL h l (by simpa [hL] using e)
  · intro h l e; exact hS.readLs h l (by simpa [hLs] using e)
  · exact hf.2.2.1 EREC ▸ hS.erec
  · exact hf.2.2.1 SPN ▸ hS.spn
  · refine ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩

/-- **`constTyC`'s `find; put`**: the tier across it. -/
theorem CoreRM.setCt {m m' : Mem} {c : Caches} {M : ModeMaps} {eb : Word} (h : CoreRM m c M eb)
    (k1 k2 w : Word) (hk1 : k1.toNat < 2 ^ 32) (hk2 : k2.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32)
    (hs : msetG ctSch m k1 k2 w = some m') :
    CoreRM m' { c with constTyC := c.constTyC.insert ((decI k1 : NIdx), (decI k2 : LsIdx)) (decE w) } M eb := by
  have hf := msetG_frame ctSch (coreSch_wf _ _ (by decide) (by decide)) m m' k1 k2 w hs
  have wf := coreSch_wf
  have fr : ∀ (S : MemoSch), S.WF → S.arr ≠ 102 → S.cs ≠ 109 → S.arr ∉ [ctSch.arr] ∧ S.cs ∉ [ctSch.cs + 1] :=
    fun S _ h1 h2 => ⟨by simpa using h1, by simpa using h2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h.eb1, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.wc.frame (wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hf
  · exact h.wk.frame (wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hf
  · exact h.wh.frame (wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hf
  · exact h.inf.frame (wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hf
  · exact h.io.frame (wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hf
  · exact h.de.frame (wf _ _ (by decide) (by decide)) vb_const (by decide) (by decide) hf
  · exact memoRV_set ctSch (coreSch_wf _ _ (by decide) (by decide)) pairKey VH
      (fun _ _ _ _ _ h => h) m c.constTyC h.ct k1 k2 w ⟨hk1, hk2⟩ (decE w) ⟨rfl, hw⟩ m' hs
  · exact memoRV_frame _ (wf _ _ (by decide) (by decide)) _ _ [ctSch.arr] [ctSch.cs + 1]
      (by decide) (by decide) m m' hf (vh_const m m') _ h.cv
  · exact memoRV_frame _ (wf _ _ (by decide) (by decide)) _ _ [ctSch.arr] [ctSch.cs + 1]
      (by decide) (by decide) m m' hf (vh_const m m') _ h.rr
  · exact memoRG_frame _ (wf _ _ (by decide) (by decide)) _ _ [ctSch.arr] [ctSch.cs + 1]
      (by decide) (by decide) m m' hf _ h.lq
  · exact memoRG_frame _ (wf _ _ (by decide) (by decide)) _ _ [ctSch.arr] [ctSch.cs + 1]
      (by decide) (by decide) m m' hf _ h.lsq

/-- **`ruleRhsC`'s `find; put`**. -/
theorem CoreRM.setRr {m m' : Mem} {c : Caches} {M : ModeMaps} {eb : Word} (h : CoreRM m c M eb)
    (k1 k2 w : Word) (hk : k1.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32)
    (hs : msetG rrSch m k1 k2 w = some m') :
    CoreRM m' { c with ruleRhsC := c.ruleRhsC.insert (rrKey.dk k1 k2) (decE w) } M eb := by
  have hf := msetG_frame rrSch (coreSch_wf _ _ (by decide) (by decide)) m m' k1 k2 w hs
  have wf := coreSch_wf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h.eb1, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.wc.frame (wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hf
  · exact h.wk.frame (wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hf
  · exact h.wh.frame (wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hf
  · exact h.inf.frame (wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hf
  · exact h.io.frame (wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hf
  · exact h.de.frame (wf _ _ (by decide) (by decide)) vb_const (by decide) (by decide) hf
  · exact memoRV_frame _ (wf _ _ (by decide) (by decide)) _ _ [rrSch.arr] [rrSch.cs + 1]
      (by decide) (by decide) m m' hf (vh_const m m') _ h.ct
  · exact memoRV_frame _ (wf _ _ (by decide) (by decide)) _ _ [rrSch.arr] [rrSch.cs + 1]
      (by decide) (by decide) m m' hf (vh_const m m') _ h.cv
  · exact memoRV_set rrSch (coreSch_wf _ _ (by decide) (by decide)) rrKey VH
      (fun _ _ _ _ _ h => h) m c.ruleRhsC h.rr k1 k2 w hk (decE w) ⟨rfl, hw⟩ m' hs
  · exact memoRG_frame _ (wf _ _ (by decide) (by decide)) _ _ [rrSch.arr] [rrSch.cs + 1]
      (by decide) (by decide) m m' hf _ h.lq
  · exact memoRG_frame _ (wf _ _ (by decide) (by decide)) _ _ [rrSch.arr] [rrSch.cs + 1]
      (by decide) (by decide) m m' hf _ h.lsq

/-! ## `const_ty_at`, `rule_rhs_at`: a memo in front of `inst_lp` -/

/-- Model of `const_ty_at`. -/
def ctaW (p : Prog) (n : Nat) (m : Mem) (nn po pl ty us : Word) : Option (Word × Mem) :=
  if mfindG ctSch m nn us = [] then none
  else if (mfindG ctSch m nn us).headD 0 ≠ 0 then
    some (mvG ctSch m ((mfindG ctSch m nn us).tail.headD 0), m)
  else match callW p n "inst_lp" [po, pl, us, ty] m with
    | none => none
    | some (r, m₁) =>
      if mfindG ctSch m₁ nn us = [] then none else
      match mputG ctSch m₁ nn us (r.headD 0) ((mfindG ctSch m₁ nn us).headD 0)
          ((mfindG ctSch m₁ nn us).tail.headD 0) with
      | none => none
      | some m₂ => some (r.headD 0, m₂)

theorem constTyAt_spec (p : Prog) (hp : IotaProg' p) (n : Nat) (s₀ : St) (nn po pl ty us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "const_ty_at" [nn, po, pl, ty, us]
    ⦃fun r s' => LocEq s' s₀ ∧ ctaW p n s₀.mem nn po pl ty us = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.constTyAt]
  simp only [callFn, constTyAtL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec ctSch p _ hp.ctf n, memoPutG_spec ctSch p _ hp.ctp n,
      callW_spec p n "inst_lp"] <;>
    finish [ctaW, mvG]

/-- Model of `rule_rhs_at`. -/
def rraW (p : Prog) (n : Nat) (m : Mem) (rec ctor po pl rhs us : Word) : Option (Word × Mem) :=
  if mfindG rrSch m rec (ctor ||| (us <<< 32)) = [] then none
  else if (mfindG rrSch m rec (ctor ||| (us <<< 32))).headD 0 ≠ 0 then
    some (mvG rrSch m ((mfindG rrSch m rec (ctor ||| (us <<< 32))).tail.headD 0), m)
  else match callW p n "inst_lp" [po, pl, us, rhs] m with
    | none => none
    | some (r, m₁) =>
      if mfindG rrSch m₁ rec (ctor ||| (us <<< 32)) = [] then none else
      match mputG rrSch m₁ rec (ctor ||| (us <<< 32)) (r.headD 0)
          ((mfindG rrSch m₁ rec (ctor ||| (us <<< 32))).headD 0)
          ((mfindG rrSch m₁ rec (ctor ||| (us <<< 32))).tail.headD 0) with
      | none => none
      | some m₂ => some (r.headD 0, m₂)

theorem ruleRhsAt_spec (p : Prog) (hp : IotaProg' p) (n : Nat) (s₀ : St)
    (rec ctor po pl rhs us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rule_rhs_at" [rec, ctor, po, pl, rhs, us]
    ⦃fun r s' => LocEq s' s₀ ∧ rraW p n s₀.mem rec ctor po pl rhs us = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.ruleRhsAt]
  simp only [callFn, ruleRhsAtL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec rrSch p _ hp.rrf n, memoPutG_spec rrSch p _ hp.rrp n,
      callW_spec p n "inst_lp"] <;>
    finish [rraW, mvG]

/-- Fuel zero runs nothing. -/
theorem invoke_zero_run (p : Prog) (f : FnName) (args : List Word) (s : St) (r : List Word) (s' : St)
    (h : (invoke p (exec p 0) f args).run s = .ok (r, s')) : False := by
  simp only [invoke, lookupFn] at h
  cases hl : p.lookup f with
  | none =>
    simp [hl] at h
    have : StateT.run (throw (Err.noFun f) : M FunDecl) s = .error (.noFun f) := rfl
    rw [this] at h
    cases h
  | some fd =>
    simp [hl, callFn, exec] at h
    have : StateT.run (throw Err.outOfFuel : M Sig) { mem := s.mem, loc := Locals.init args } = .error .outOfFuel := rfl
    rw [this] at h
    cases h

theorem constTyAt_run_hit (cv : IConstantVal) (us : LsIdx) (a : AState) (r : EIdx)
    (h : a.caches.constTyC[(cv.name, us)]? = some r) : (constTyAt cv us).run a = .ok (r, a) := by
  simp [constTyAt, h, StateT.run_bind, StateT.run_get]; rfl

theorem constTyAt_run_miss (cv : IConstantVal) (us : LsIdx) (a a₁ : AState) (r : EIdx)
    (h : a.caches.constTyC[(cv.name, us)]? = none)
    (hi : (instLPFast coreWalkFuel cv.levelParams us cv.type).run a = .ok (r, a₁)) :
    (constTyAt cv us).run a = .ok (r, { a₁ with caches := { a₁.caches with
      constTyC := a₁.caches.constTyC.insert (cv.name, us) r } }) := by
  simp [constTyAt, h, StateT.run_bind, StateT.run_get, hi]
  rfl

/-- **`const_ty_at` refines `constTyAt`** (the `inst_lp` stub as `WhnfCallees.instLP`). -/
theorem constTyAt_refines' (p : Prog) (hp : IotaProg' p) (hw : WhnfCallees p) :
    ConstTyAtOK p := by
  intro n s₀ a₀ dn vis fe MM eb nn po pl ty us lps hS hnn hty hus hlps
  cases n with
  | zero =>
    apply L.M.triple_of_run
    intro s r s' _ hrun
    exact (invoke_zero_run _ _ _ _ _ _ hrun).elim
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (constTyAt_spec p hp n s₀ nn po pl ty us)
  subst hs0
  refine ⟨hloc, ?_⟩
  simp only [ctaW] at hW
  by_cases h0 : mfindG ctSch s.mem nn us = []
  · rw [if_pos h0] at hW; cases hW
  rw [if_neg h0] at hW
  have hf := memoRV_findP hS.core.ct nn us hnn hus h0
  by_cases h1 : (mfindG ctSch s.mem nn us).headD 0 ≠ 0
  · rw [if_pos h1] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    obtain ⟨hv, hv32⟩ := hf.1 h1
    have hrun1 := constTyAt_run_hit ⟨decI nn, lps, decE ty⟩ (decI us) a₀ _ hv
    refine CoreRef.of_pure hS hrun1 hm.symm ?_ ?_
    · simp only [decH]; rw [← hr]
    · unfold ResH HW; rw [← hr]; exact hv32
  rw [if_neg h1] at hW
  have hmiss := hf.2 (by simpa using h1)
  cases hc : callW p n "inst_lp" [po, pl, us, ty] s.mem with
  | none => rw [hc] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc] at hW
  simp only at hW
  obtain ⟨hok, ⟨M', hS₁, hK, hSt⟩, hres, hr₁⟩ :=
    CoreSpec.of_callW (hw.instLP n s a₀ dn vis fe MM eb po pl us ty lps hS hty hus hlps) hc
  have hrunI := AM.run_of_ok _ _ hok
  have hrun2 := constTyAt_run_miss ⟨decI nn, lps, decE ty⟩ (decI us) a₀ _ _ hmiss hrunI
  rw [hres] at hrun2
  by_cases h2 : mfindG ctSch m₁ nn us = []
  · rw [if_pos h2] at hW; cases hW
  rw [if_neg h2] at hW
  cases hp : mputG ctSch m₁ nn us (r₁.headD 0) ((mfindG ctSch m₁ nn us).headD 0)
      ((mfindG ctSch m₁ nn us).tail.headD 0) with
  | none => rw [hp] at hW; cases hW
  | some m₂ =>
  rw [hp] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  have hs : msetG ctSch m₁ nn us (r₁.headD 0) = some m₂ := by rw [msetG_eq _ _ _ _ _ h2]; exact hp
  have hwv : HW (r₁.headD 0) := hr₁
  have hcore := hS₁.core.setCt nn us (r₁.headD 0) hnn hus hwv hs
  obtain ⟨hS₂, hSt₂⟩ := CoreS.setMemo ctSch _ hS₁
    (msetG_frame ctSch (coreSch_wf _ _ (by decide) (by decide)) _ _ _ _ _ hs)
    (by decide) (by decide) (by decide) (by decide) hcore rfl rfl
  obtain ⟨hok2, hst2, hres2⟩ := AM.of_run_ok _ _ _ _ hrun2
  refine ⟨hok2, ⟨M', ?_, hK, hm ▸ hSt.trans hSt₂⟩, ?_, ?_⟩
  · rw [hst2, ← hm]; exact hS₂
  · rw [hres2]; simp only [decH]; rw [← hr]
  · unfold ResH HW; rw [← hr]; exact hwv

theorem ruleRhsAt_run_hit (rec ctor : NIdx) (lps : List NIdx) (rhs : EIdx) (us : LsIdx) (a : AState)
    (r : EIdx) (h : a.caches.ruleRhsC[(rec, ctor, us)]? = some r) :
    (ruleRhsAt rec ctor lps rhs us).run a = .ok (r, a) := by
  simp [ruleRhsAt, h, StateT.run_bind, StateT.run_get]; rfl

theorem ruleRhsAt_run_miss (rec ctor : NIdx) (lps : List NIdx) (rhs : EIdx) (us : LsIdx)
    (a a₁ : AState) (r : EIdx) (h : a.caches.ruleRhsC[(rec, ctor, us)]? = none)
    (hi : (instLPFast coreWalkFuel lps us rhs).run a = .ok (r, a₁)) :
    (ruleRhsAt rec ctor lps rhs us).run a = .ok (r, { a₁ with caches := { a₁.caches with
      ruleRhsC := a₁.caches.ruleRhsC.insert (rec, ctor, us) r } }) := by
  simp [ruleRhsAt, h, StateT.run_bind, StateT.run_get, hi]
  rfl

/-- **`rule_rhs_at` refines `ruleRhsAt`** (the `inst_lp` stub as `WhnfCallees.instLP`). -/
theorem ruleRhsAt_refines' (p : Prog) (hp : IotaProg' p) (hw : WhnfCallees p) :
    RuleRhsAtOK p := by
  intro n s₀ a₀ dn vis fe MM eb rec ctor po pl rhs us lps hS hrec hctor hrhs hus hlps
  cases n with
  | zero =>
    apply L.M.triple_of_run
    intro s r s' _ hrun
    exact (invoke_zero_run _ _ _ _ _ _ hrun).elim
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (ruleRhsAt_spec p hp n s₀ rec ctor po pl rhs us)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hdk := rrKey_dk rec ctor us hctor hus
  simp only [rraW] at hW
  by_cases h0 : mfindG rrSch s.mem rec (ctor ||| (us <<< 32)) = []
  · rw [if_pos h0] at hW; cases hW
  rw [if_neg h0] at hW
  have hf := memoRV_findR hS.core.rr rec (ctor ||| (us <<< 32)) hrec h0
  rw [hdk] at hf
  by_cases h1 : (mfindG rrSch s.mem rec (ctor ||| (us <<< 32))).headD 0 ≠ 0
  · rw [if_pos h1] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    obtain ⟨hv, hv32⟩ := hf.1 h1
    have hrun1 := ruleRhsAt_run_hit (decI rec) (decI ctor) lps (decE rhs) (decI us) a₀ _ hv
    refine CoreRef.of_pure hS hrun1 hm.symm ?_ ?_
    · simp only [decH]; rw [← hr]
    · unfold ResH HW; rw [← hr]; exact hv32
  rw [if_neg h1] at hW
  have hmiss := hf.2 (by simpa using h1)
  cases hc : callW p n "inst_lp" [po, pl, us, rhs] s.mem with
  | none => rw [hc] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc] at hW
  simp only at hW
  obtain ⟨hok, ⟨M', hS₁, hK, hSt⟩, hres, hr₁⟩ :=
    CoreSpec.of_callW (hw.instLP n s a₀ dn vis fe MM eb po pl us rhs lps hS hrhs hus hlps) hc
  have hrunI := AM.run_of_ok _ _ hok
  have hrun2 := ruleRhsAt_run_miss (decI rec) (decI ctor) lps (decE rhs) (decI us) a₀ _ _ hmiss hrunI
  rw [hres] at hrun2
  by_cases h2 : mfindG rrSch m₁ rec (ctor ||| (us <<< 32)) = []
  · rw [if_pos h2] at hW; cases hW
  rw [if_neg h2] at hW
  cases hp : mputG rrSch m₁ rec (ctor ||| (us <<< 32)) (r₁.headD 0)
      ((mfindG rrSch m₁ rec (ctor ||| (us <<< 32))).headD 0)
      ((mfindG rrSch m₁ rec (ctor ||| (us <<< 32))).tail.headD 0) with
  | none => rw [hp] at hW; cases hW
  | some m₂ =>
  rw [hp] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  have hs : msetG rrSch m₁ rec (ctor ||| (us <<< 32)) (r₁.headD 0) = some m₂ := by
    rw [msetG_eq _ _ _ _ _ h2]; exact hp
  have hwv : HW (r₁.headD 0) := hr₁
  have hcore := hS₁.core.setRr rec (ctor ||| (us <<< 32)) (r₁.headD 0) hrec hwv hs
  rw [hdk] at hcore
  obtain ⟨hS₂, hSt₂⟩ := CoreS.setMemo rrSch _ hS₁
    (msetG_frame rrSch (coreSch_wf _ _ (by decide) (by decide)) _ _ _ _ _ hs)
    (by decide) (by decide) (by decide) (by decide) hcore rfl rfl
  obtain ⟨hok2, hst2, hres2⟩ := AM.of_run_ok _ _ _ _ hrun2
  refine ⟨hok2, ⟨M', ?_, hK, hm ▸ hSt.trans hSt₂⟩, ?_, ?_⟩
  · rw [hst2, ← hm]; exact hS₂
  · rw [hres2]; simp only [decH]; rw [← hr]
  · unfold ResH HW; rw [← hr]; exact hwv

/-! ## `pi_residual(e, ao, an)` -/

/-- Model of the `pi_residual` loop at L fuel `k` (each iteration spends one unit, the callee
runs at the rest): `none` the L code aborts or runs out of fuel, `some ([0, 0], m)` the early
`return (0, 0)`, `some ([1, e], m)` the loop's normal exit with accumulator `e`. -/
def pirW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, e, ao, an, i =>
    if i < an then
      if e >>> 28 ≠ 6 then some ([0, 0], m)
      else if tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
      else if rdW (m.arr64 CTL) (30 + tierW e) ≤ idxW e then none
      else match callW p k "inst_entry"
          [rdW (m.arr64 FAREC) (idxW e * 4 + tierW e * 2 + 1), rdW (m.arr64 SPN) (ao + i), 0] m with
        | none => none
        | some (r, m₁) => pirW p k m₁ (r.headD 0) ao an (i + 1)
    else some ([1, e], m)

theorem pirW_end (p : Prog) (k : Nat) (m : Mem) (e ao an i : Word) (h : ¬ i < an) :
    pirW p (k + 1) m e ao an i = some ([1, e], m) := by
  simp [pirW, h]

theorem pirW_exit (p : Prog) (k : Nat) (m : Mem) (e ao an i : Word) (h : i < an)
    (h6 : e >>> 28 ≠ 6) : pirW p (k + 1) m e ao an i = some ([0, 0], m) := by
  simp [pirW, h, h6]

theorem pirW_ab1 (p : Prog) (k : Nat) (m : Mem) (e ao an i : Word) (h : i < an)
    (h6 : ¬ e >>> 28 ≠ 6) (h1 : tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) :
    pirW p (k + 1) m e ao an i = none := by
  simp [pirW, h, h6, h1]

theorem pirW_ab2 (p : Prog) (k : Nat) (m : Mem) (e ao an i : Word) (h : i < an)
    (h6 : ¬ e >>> 28 ≠ 6) (h1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (h2 : rdW (m.arr64 CTL) (30 + tierW e) ≤ idxW e) :
    pirW p (k + 1) m e ao an i = none := by
  simp only [pirW, h, h6, h1, h2]; simp

theorem pirW_cont (p : Prog) (k : Nat) (m m₁ : Mem) (e ao an i : Word) (r : List Word)
    (h : i < an) (h6 : ¬ e >>> 28 ≠ 6) (h1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (h2 : ¬ rdW (m.arr64 CTL) (30 + tierW e) ≤ idxW e)
    (hc : callW p k "inst_entry"
          [rdW (m.arr64 FAREC) (idxW e * 4 + tierW e * 2 + 1), rdW (m.arr64 SPN) (ao + i), 0] m =
        some (r, m₁)) :
    pirW p (k + 1) m e ao an i = pirW p k m₁ (r.headD 0) ao an (i + 1) := by
  simp only [pirW, h, h6, h1, h2, hc]; simp

theorem piResidualLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k piResidualLoop
    ⦃fun r s' => r ≠ .brk ∧ pirW p k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) =
      some (r.retOr [1, s'.loc 0], s'.mem); ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := piResidualLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p k "inst_entry", ih] <;>
      finish [pirW_end, pirW_exit, pirW_ab1, pirW_ab2, pirW_cont, tierW, idxW]

theorem piResidualLoop_step_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p k) piResidualLoop
    ⦃fun r s' => r ≠ .brk ∧ pirW p (k + 1) s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) =
      some (r.retOr [1, s'.loc 0], s'.mem); ⊤⦄ :=
  Triple.step_exec (piResidualLoop_spec p (k + 1) s₀)

theorem piResidual_spec (p : Prog) (hp : p.lookup "pi_residual" = some piResidualL) (k : Nat)
    (s₀ : St) (e ao an : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "pi_residual" [e, ao, an]
    ⦃fun r s' => LocEq s' s₀ ∧ pirW p (k + 1) s₀.mem e ao an 0 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, piResidualL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, piResidualLoop_step_spec p k] <;>
    finish

theorem viewBind_run₀ (h : EIdx) (a : AState) :
    (ConRon.Arena.viewBind h).run a = .ok (a.store.viewBind h, a) := rfl

theorem piResidual_nil_run (e : EIdx) (a : AState) :
    (piResidual e []).run a = .ok (some e, a) := by
  simp [piResidual]; rfl

theorem piResidual_not_run (h a' : EIdx) (as : List EIdx) (a : AState) (ht : h.tag ≠ ETag.forallE) :
    (piResidual h (a' :: as)).run a = .ok (none, a) := by
  simp [piResidual, ht]; rfl

theorem piResidual_cons_run (h a' b b' : EIdx) (as : List EIdx) (a a₁ a₂ : AState)
    (res : Option EIdx) (ht : h.tag = ETag.forallE) (c : EIdx)
    (hv : a.store.viewBind h = some (c, b))
    (hi : (instantiate1Fast coreWalkFuel b a' 0).run a = .ok (b', a₁))
    (hr : (piResidual b' as).run a₁ = .ok (res, a₂)) :
    (piResidual h (a' :: as)).run a = .ok (res, a₂) := by
  simp only [piResidual, ht, beq_self_eq_true, ↓reduceIte, StateT.run_bind, viewBind_run₀, hv,
    except_ok_bind, hi, hr]

/-- **The `pi_residual` loop refines `piResidual`**, by induction on the remaining count. -/
theorem pirW_ok (p : Prog) (hinst : IotaInst1OK p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (eb ao an : Word) (args : Array EIdx) :
    ∀ (K k : Nat) (m : Mem) (a : AState) (M : ModeMaps) (e i : Word) (L : List Word) (m' : Mem),
      an.toNat - i.toNat = K → i.toNat ≤ an.toNat → CoreS dn m a vis fe M eb → HW e →
      SpineR m ao an args → ao.toNat + an.toNat ≤ (spTop m).toNat →
      pirW p k m e ao an i = some (L, m') →
      AM.ok (piResidual (decE e) (args.toList.drop i.toNat)) a ∧
      CoreAfter dn m m' (AM.st (piResidual (decE e) (args.toList.drop i.toNat)) a) vis fe M eb ∧
      AM.res (piResidual (decE e) (args.toList.drop i.toNat)) a = decOptR L ∧
      HW (L.headD 0) ∧ HW (L.tail.headD 0) := by
  intro K
  induction K with
  | zero =>
    intro k m a M e i L m' hK hi hS he hsp htop hL
    have hni : ¬ i < an := by
      intro h; have : i.toNat < an.toNat := h; omega
    cases k with
    | zero => simp [pirW] at hL
    | succ k =>
    rw [pirW_end p k m e ao an i hni] at hL
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
    have hdrop : args.toList.drop i.toNat = [] := by
      apply List.drop_eq_nil_of_le; simp [hsp.size]; omega
    rw [hdrop]
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (piResidual_nil_run (decE e) a)
    refine ⟨hok, ?_, ?_, by simp [HW], he⟩
    · rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩
    · rw [hres]; simp [decOptR, decOpt]
  | succ K ih =>
    intro k m a M e i L m' hK hi hS he hsp htop hL
    have hlt : i < an := by
      have : i.toNat < an.toNat := by omega
      exact this
    have hlt' : i.toNat < an.toNat := hlt
    have hsz : i.toNat < args.size := by rw [hsp.size]; exact hlt'
    have hdrop : args.toList.drop i.toNat = args[i.toNat] :: args.toList.drop (i.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hsz)]; simp
    cases k with
    | zero => simp [pirW] at hL
    | succ k =>
    by_cases h6 : e >>> 28 ≠ 6
    · rw [pirW_exit p k m e ao an i hlt h6] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      rw [hdrop]
      have htag : (decE e).tag ≠ ETag.forallE := fun h => h6 ((decE_tag_forall e he).mp h)
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (piResidual_not_run (decE e) _ _ a htag)
      refine ⟨hok, ?_, ?_, by simp [HW], by simp [HW]⟩
      · rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩
      · rw [hres]; simp [decOptR, decOpt]
    have h6' : e >>> 28 = 6 := by simpa using h6
    by_cases hv1 : tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
    · rw [pirW_ab1 p k m e ao an i hlt h6 hv1] at hL; cases hL
    by_cases hv2 : rdW (m.arr64 CTL) (30 + tierW e) ≤ idxW e
    · rw [pirW_ab2 p k m e ao an i hlt h6 hv1 hv2] at hL; cases hL
    cases hc : callW p k "inst_entry"
        [rdW (m.arr64 FAREC) (idxW e * 4 + tierW e * 2 + 1), rdW (m.arr64 SPN) (ao + i), 0] m with
    | none => simp [pirW, hlt, h6, hv1, hv2, hc] at hL
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [pirW_cont p k m m₁ e ao an i r₁ hlt h6 hv1 hv2 hc] at hL
    obtain ⟨hvb, hbw, -⟩ := view_forall m a hS.arena.1 e he ⟨hv1, UInt64.not_le.mp hv2⟩ h6'
    have hvb' := viewBind_forall m a hS.arena.1 e he ⟨hv1, UInt64.not_le.mp hv2⟩ h6'
    obtain ⟨hok, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres, hr₁⟩ := CoreSpec.of_callW
      (hinst k ⟨m, Locals.init []⟩ a dn vis fe M eb _ (rdW (m.arr64 SPN) (ao + i)) 0 hS (by
        have := (view_forall m a hS.arena.1 e he ⟨hv1, UInt64.not_le.mp hv2⟩ h6').2.2
        exact this)) hc
    have hsp₁ : SpineR m₁ ao an args := hsp.keep hSt₁.2.1 hSt₁.2.2 htop hS.spn
    have htop₁ : ao.toNat + an.toNat ≤ (spTop m₁).toNat := by rw [hSt₁.1]; exact htop
    have h1 : (i + 1).toNat = i.toNat + 1 := uint64_succ_toNat an i hlt
    obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hL1, hL2⟩ :=
      ih k m₁ (AM.st (instantiate1Fast coreWalkFuel (decE (rdW (m.arr64 FAREC) (idxW e * 4 + tierW e * 2 + 1)))
        (decE (rdW (m.arr64 SPN) (ao + i))) (UInt64.toNat 0)) a) M₁ (r₁.headD 0) (i + 1) L m'
        (by omega) (by omega) hS₁ hr₁ hsp₁ htop₁ hL
    have hget : args[i.toNat] = decE (rdW (m.arr64 SPN) (ao + i)) := by
      have := hsp.get i.toNat hsz
      simpa [spW] using this
    have hrunT := AM.run_of_ok _ _ hok
    rw [hres] at hrunT
    have hrunR := AM.run_of_ok _ _ hok2
    rw [h1] at hrunR
    have hrun := piResidual_cons_run (decE e) args[i.toNat] (decE (rdW (m.arr64 FAREC) (idxW e * 4 + tierW e * 2 + 1)))
      (decH r₁) (args.toList.drop (i.toNat + 1)) a _ _ _ ((decE_tag_forall e he).mpr h6') _ hvb'
      (by rw [hget]; exact hrunT) hrunR
    rw [h1] at hS₂ hres2
    rw [hdrop]
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun
    refine ⟨hokF, ⟨M₂, ?_, hK₁.trans hK₂, hSt₁.trans hSt₂⟩, ?_, hL1, hL2⟩
    · rw [hstF]; exact hS₂
    · rw [hresF]; exact hres2

/-- **`pi_residual` refines `piResidual`.** Statement change: `PiResidualOK` plus
`ao + an ≤ spTop` (the argument slice lies below the stack top, so the `inst_entry` calls, which
may use the stack above it, leave it alone). -/
theorem piResidual_refines' (p : Prog) (hp : IotaProg' p) (hc : IotaCallees p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb e ao an : Word) (args : Array EIdx), CoreS dn s₀.mem a₀ vis fe MM eb →
    HW e → SpineR s₀.mem ao an args → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p n "pi_residual" [e, ao, an] (piResidual (decE e) args.toList) decOptR s₀ a₀ dn vis fe
      MM eb ResW := by
  intro n s₀ a₀ dn vis fe MM eb e ao an args hS he hsp htop
  cases n with
  | zero =>
    apply L.M.triple_of_run
    intro s r s' _ hrun
    exact (invoke_zero_run _ _ _ _ _ _ hrun).elim
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (piResidual_spec p hp.piResidual n s₀ e ao an)
  subst hs0
  refine ⟨hloc, ?_⟩
  obtain ⟨hok, hca, hres, hL1, hL2⟩ := pirW_ok p hc.inst1 dn vis fe eb ao an args
    (an.toNat - (0 : Word).toNat) (n + 1) s.mem a₀ MM e 0 r s'.mem rfl (by simp) hS he hsp htop hW
  refine ⟨hok, ?_, ?_, ⟨hL1, hL2⟩⟩
  · simpa using hca
  · simpa using hres

/-! ## `defeq_list(mode, vis, d, ao, an, bo, bn)` -/

/-- Model of the `defeq_list` loop at L fuel `k`. -/
def dlW (p : Prog) (mode vis d ao an bo bn : Word) : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | k + 1, m, i =>
    if i < an ∧ i < bn then
      match callW p k "defeq" [mode, vis, d, rdW (m.arr64 SPN) (ao + i), rdW (m.arr64 SPN) (bo + i)] m with
      | none => none
      | some (r, m₁) => if r.headD 0 = 0 then some ([0], m₁) else dlW p mode vis d ao an bo bn k m₁ (i + 1)
    else some ([Cmp.eq.evalW an bn], m)

theorem dlW_end (p : Prog) (mode vis d ao an bo bn : Word) (k : Nat) (m : Mem) (i : Word)
    (h : ¬ (i < an ∧ i < bn)) :
    dlW p mode vis d ao an bo bn (k + 1) m i = some ([Cmp.eq.evalW an bn], m) := by
  simp only [dlW, h, ↓reduceIte]

theorem dlW_stop (p : Prog) (mode vis d ao an bo bn : Word) (k : Nat) (m m₁ : Mem) (i : Word)
    (r : List Word) (h : i < an ∧ i < bn)
    (hc : callW p k "defeq" [mode, vis, d, rdW (m.arr64 SPN) (ao + i), rdW (m.arr64 SPN) (bo + i)] m =
      some (r, m₁)) (h0 : r.headD 0 = 0) :
    dlW p mode vis d ao an bo bn (k + 1) m i = some ([0], m₁) := by
  simp only [dlW, h.1, h.2, and_self, ↓reduceIte, hc, h0]

theorem dlW_cont (p : Prog) (mode vis d ao an bo bn : Word) (k : Nat) (m m₁ : Mem) (i : Word)
    (r : List Word) (h : i < an ∧ i < bn)
    (hc : callW p k "defeq" [mode, vis, d, rdW (m.arr64 SPN) (ao + i), rdW (m.arr64 SPN) (bo + i)] m =
      some (r, m₁)) (h0 : ¬ r.headD 0 = 0) :
    dlW p mode vis d ao an bo bn (k + 1) m i = dlW p mode vis d ao an bo bn k m₁ (i + 1) := by
  simp only [dlW, h.1, h.2, and_self, ↓reduceIte, hc, h0]

theorem defeqListLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k defeqListLoop
    ⦃fun r s' => r ≠ .brk ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 6 = s₀.loc 6 ∧
      dlW p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)
      (s₀.loc 6) k s₀.mem (s₀.loc 7) =
        some (r.retOr [Cmp.eq.evalW (s₀.loc 4) (s₀.loc 6)], s'.mem); ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := defeqListLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p k "defeq", ih] <;> finish [dlW_end, dlW_stop, dlW_cont]

theorem defeqListLoop_step_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p k) defeqListLoop
    ⦃fun r s' => r ≠ .brk ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 6 = s₀.loc 6 ∧
      dlW p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)
      (s₀.loc 6) (k + 1) s₀.mem (s₀.loc 7) =
        some (r.retOr [Cmp.eq.evalW (s₀.loc 4) (s₀.loc 6)], s'.mem); ⊤⦄ :=
  Triple.step_exec (defeqListLoop_spec p (k + 1) s₀)

theorem defeqList_spec (p : Prog) (hp : p.lookup "defeq_list" = some defeqListL) (k : Nat)
    (s₀ : St) (mode vis d ao an bo bn : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "defeq_list" [mode, vis, d, ao, an, bo, bn]
    ⦃fun r s' => LocEq s' s₀ ∧ dlW p mode vis d ao an bo bn (k + 1) s₀.mem 0 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, defeqListL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, defeqListLoop_step_spec p k] <;>
    finish

theorem defEqList_nil_run (r : CoreFnsA) (fe : IFEnv) (d : Nat) (a : AState) :
    (defEqList r fe d [] []).run a = .ok (true, a) := by
  simp [defEqList]; rfl

theorem defEqList_nil_cons_run (r : CoreFnsA) (fe : IFEnv) (d : Nat) (b : EIdx) (bs : List EIdx)
    (a : AState) : (defEqList r fe d [] (b :: bs)).run a = .ok (false, a) := by
  simp [defEqList]; rfl

theorem defEqList_cons_nil_run (r : CoreFnsA) (fe : IFEnv) (d : Nat) (x : EIdx) (xs : List EIdx)
    (a : AState) : (defEqList r fe d (x :: xs) []).run a = .ok (false, a) := by
  simp [defEqList]; rfl

theorem defEqList_stop_run (r : CoreFnsA) (fe : IFEnv) (d : Nat) (x y : EIdx) (xs ys : List EIdx)
    (a a₁ : AState) (h : (r.defeq d x y).run a = .ok (false, a₁)) :
    (defEqList r fe d (x :: xs) (y :: ys)).run a = .ok (false, a₁) := by
  simp only [defEqList, StateT.run_bind, h, except_ok_bind]; rfl

theorem defEqList_cont_run (r : CoreFnsA) (fe : IFEnv) (d : Nat) (x y : EIdx) (xs ys : List EIdx)
    (a a₁ a₂ : AState) (res : Bool) (h : (r.defeq d x y).run a = .ok (true, a₁))
    (hr : (defEqList r fe d xs ys).run a₁ = .ok (res, a₂)) :
    (defEqList r fe d (x :: xs) (y :: ys)).run a = .ok (res, a₂) := by
  simp only [defEqList, StateT.run_bind, h, except_ok_bind, if_true]; exact hr

theorem toUInt64_toNat_self (i : Word) : i.toNat.toUInt64 = i := by
  simp [Nat.toUInt64]

/-- A spine slice that may be empty anywhere (an empty slice has no bound to keep). -/
def SpineN (m : Mem) (off cnt : Word) (xs : Array EIdx) : Prop :=
  xs.size = cnt.toNat ∧ (cnt ≠ 0 → SpineR m off cnt xs)

theorem SpineR.toN {m : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs) :
    SpineN m off cnt xs := ⟨h.size, fun _ => h⟩

theorem SpineN.keep {m m' : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineN m off cnt xs)
    (hsz : (m'.arr64 SPN).size = (m.arr64 SPN).size)
    (hk : ∀ i : Word, i < spTop m → spW m' i = spW m i)
    (htop : off.toNat + cnt.toNat ≤ (spTop m).toNat) (hspn : (m.arr64 SPN).size < 2 ^ 63) :
    SpineN m' off cnt xs :=
  ⟨h.1, fun hc => (h.2 hc).keep hsz hk htop hspn⟩

/-- The loop's exit: one of the two spines is used up. -/
theorem dl_exit (r : CoreFnsA) (fe : IFEnv) (d : Nat) (an bn i : Word) (aas bs : Array EIdx)
    (hna : aas.size = an.toNat) (hnb : bs.size = bn.toNat) (hia : i.toNat ≤ an.toNat)
    (hib : i.toNat ≤ bn.toNat) (hn : ¬ (i < an ∧ i < bn)) (a : AState) :
    (defEqList r fe d (aas.toList.drop i.toNat) (bs.toList.drop i.toNat)).run a =
      .ok (decide (an = bn), a) := by
  have h1 : ¬ (i.toNat < an.toNat ∧ i.toNat < bn.toNat) := fun h => hn ⟨h.1, h.2⟩
  by_cases hab : an = bn
  · subst hab
    have : aas.toList.drop i.toNat = [] := List.drop_eq_nil_of_le (by simp [hna]; omega)
    have h2 : bs.toList.drop i.toNat = [] := List.drop_eq_nil_of_le (by simp [hnb]; omega)
    rw [this, h2]; simpa using defEqList_nil_run r fe d a
  · have hne : an.toNat ≠ bn.toNat := fun h => hab (UInt64.toNat_inj.mp h)
    simp only [hab, decide_false]
    by_cases hi : i.toNat < an.toNat
    · have hb : bn.toNat ≤ i.toNat := by omega
      have h2 : bs.toList.drop i.toNat = [] := List.drop_eq_nil_of_le (by simp [hnb]; omega)
      rw [h2, List.drop_eq_getElem_cons (by simp [hna]; omega)]
      exact defEqList_cons_nil_run r fe d _ _ a
    · have h2 : aas.toList.drop i.toNat = [] := List.drop_eq_nil_of_le (by simp [hna]; omega)
      rw [h2, List.drop_eq_getElem_cons (by simp [hnb]; omega)]
      exact defEqList_nil_cons_run r fe d _ _ a

/-- **The `defeq_list` loop refines `defEqList`**, by induction on the remaining count. -/
theorem dlW_ok (p : Prog) (n F : Nat) (hknot : KnotUpTo p n) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode d ao an bo bn : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (aas bs : Array EIdx) :
    ∀ (K k : Nat) (m : Mem) (a : AState) (M : ModeMaps) (i : Word) (L : List Word) (m' : Mem),
      an.toNat - i.toNat = K → i.toNat ≤ an.toNat → i.toNat ≤ bn.toNat → k ≤ n + 1 →
      CoreS dn m a vis fe M eb → SpineN m ao an aas → SpineN m bo bn bs →
      (an ≠ 0 → ao.toNat + an.toNat ≤ (spTop m).toNat) →
      (bn ≠ 0 → bo.toNat + bn.toNat ≤ (spTop m).toNat) →
      dlW p mode vis d ao an bo bn k m i = some (L, m') →
      AM.ok (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat (aas.toList.drop i.toNat)
        (bs.toList.drop i.toNat)) a ∧
      CoreAfter dn m m' (AM.st (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat
        (aas.toList.drop i.toNat) (bs.toList.drop i.toNat)) a) vis fe M eb ∧
      AM.res (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat (aas.toList.drop i.toNat)
        (bs.toList.drop i.toNat)) a = decBool L ∧ HW (L.headD 0) := by
  intro K
  induction K with
  | zero =>
    intro k m a M i L m' hK hia hib hk hS hsa hsb hta htb hL
    have hn : ¬ (i < an ∧ i < bn) := fun h => by
      have : i.toNat < an.toNat := h.1
      omega
    cases k with
    | zero => simp [dlW] at hL
    | succ k =>
    rw [dlW_end p mode vis d ao an bo bn k m i hn] at hL
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _
      (dl_exit (coreKnot (decMode mode) fe id F) fe d.toNat an bn i aas bs hsa.1 hsb.1 hia hib hn a)
    refine ⟨hok, ?_, ?_, ?_⟩
    · rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩
    · rw [hres]; simp only [decBool, Cmp.evalW, Cmp.eval]; by_cases h : an = bn <;> simp [h]
    · simp only [Cmp.evalW]; split <;> simp [HW]
  | succ K ih =>
    intro k m a M i L m' hK hia hib hk hS hsa hsb hta htb hL
    cases k with
    | zero => simp [dlW] at hL
    | succ k =>
    rcases Classical.em ¬(i < an ∧ i < bn) with hn | hn
    · rw [dlW_end p mode vis d ao an bo bn k m i hn] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _
        (dl_exit (coreKnot (decMode mode) fe id F) fe d.toNat an bn i aas bs hsa.1 hsb.1 hia hib hn a)
      refine ⟨hok, ?_, ?_, ?_⟩
      · rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩
      · rw [hres]; simp only [decBool, Cmp.evalW, Cmp.eval]; by_cases h : an = bn <;> simp [h]
      · simp only [Cmp.evalW]; split <;> simp [HW]
    replace hn := Classical.not_not.mp hn
    have hia' : i.toNat < an.toNat := hn.1
    have hib' : i.toNat < bn.toNat := hn.2
    have hna : an ≠ 0 := fun h => by rw [h] at hia'; simp at hia'
    have hnb : bn ≠ 0 := fun h => by rw [h] at hib'; simp at hib'
    have hsa := hsa.2 hna
    have hsb := hsb.2 hnb
    have hsza : i.toNat < aas.size := by rw [hsa.size]; exact hia'
    have hszb : i.toNat < bs.size := by rw [hsb.size]; exact hib'
    have hdra : aas.toList.drop i.toNat = aas[i.toNat] :: aas.toList.drop (i.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hsza)]; simp
    have hdrb : bs.toList.drop i.toNat = bs[i.toNat] :: bs.toList.drop (i.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hszb)]; simp
    have hga : aas[i.toNat] = decE (rdW (m.arr64 SPN) (ao + i)) := by
      have := hsa.get i.toNat hsza
      simpa [spW, toUInt64_toNat_self] using this
    have hgb : bs[i.toNat] = decE (rdW (m.arr64 SPN) (bo + i)) := by
      have := hsb.get i.toNat hszb
      simpa [spW, toUInt64_toNat_self] using this
    have hxa : HW (rdW (m.arr64 SPN) (ao + i)) := by
      have := hsa.lt i.toNat hia'
      unfold HW; simpa [spW, toUInt64_toNat_self] using this
    have hxb : HW (rdW (m.arr64 SPN) (bo + i)) := by
      have := hsb.lt i.toNat hib'
      unfold HW; simpa [spW, toUInt64_toNat_self] using this
    rw [hga] at hdra
    rw [hgb] at hdrb
    cases hc : callW p k "defeq" [mode, vis, d, rdW (m.arr64 SPN) (ao + i), rdW (m.arr64 SPN) (bo + i)] m with
    | none => simp [dlW, hn.1, hn.2, hc] at hL
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    obtain ⟨hok, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres, hr₁⟩ := CoreSpec.of_callW
      ((hknot k (by omega)).defeq F ⟨m, Locals.init []⟩ a dn vis fe M eb mode d _ _ (by omega)
        (by omega) ⟨hS, hm4, hebm⟩ hxa hxb) hc
    have hrunT := AM.run_of_ok _ _ hok
    by_cases h0 : r₁.headD 0 = 0
    · rw [dlW_stop p mode vis d ao an bo bn k m m₁ i r₁ hn hc h0] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      have hres' : AM.res ((coreKnot (decMode mode) fe id F).defeq d.toNat
          (decE (rdW (m.arr64 SPN) (ao + i))) (decE (rdW (m.arr64 SPN) (bo + i)))) a = false := by
        rw [hres]; simpa [decBool] using h0
      rw [hres'] at hrunT
      have hrun := defEqList_stop_run (coreKnot (decMode mode) fe id F) fe d.toNat _ _
        (aas.toList.drop (i.toNat + 1)) (bs.toList.drop (i.toNat + 1)) a _ hrunT
      rw [hdra, hdrb]
      obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun
      refine ⟨hokF, ⟨M₁, ?_, hK₁, hSt₁⟩, ?_, by simp [HW]⟩
      · rw [hstF]; exact hS₁
      · rw [hresF]; simp [decBool]
    · rw [dlW_cont p mode vis d ao an bo bn k m m₁ i r₁ hn hc h0] at hL
      have hsa₁ : SpineN m₁ ao an aas := hsa.toN.keep hSt₁.2.1 hSt₁.2.2 (hta hna) hS.spn
      have hsb₁ : SpineN m₁ bo bn bs := hsb.toN.keep hSt₁.2.1 hSt₁.2.2 (htb hnb) hS.spn
      have hta₁ : an ≠ 0 → ao.toNat + an.toNat ≤ (spTop m₁).toNat := fun h => by
        rw [hSt₁.1]; exact hta h
      have htb₁ : bn ≠ 0 → bo.toNat + bn.toNat ≤ (spTop m₁).toNat := fun h => by
        rw [hSt₁.1]; exact htb h
      have h1 : (i + 1).toNat = i.toNat + 1 := uint64_succ_toNat an i hn.1
      obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hL1⟩ := ih k m₁ _ M₁ (i + 1) L m'
        (by omega) (by omega) (by omega) (by omega) hS₁ hsa₁ hsb₁ hta₁ htb₁ hL
      have hres' : AM.res ((coreKnot (decMode mode) fe id F).defeq d.toNat
          (decE (rdW (m.arr64 SPN) (ao + i))) (decE (rdW (m.arr64 SPN) (bo + i)))) a = true := by
        rw [hres]; simpa [decBool] using h0
      rw [hres'] at hrunT
      have hrunR := AM.run_of_ok _ _ hok2
      rw [h1] at hrunR
      rw [h1] at hS₂ hres2
      have hrun := defEqList_cont_run (coreKnot (decMode mode) fe id F) fe d.toNat _ _
        (aas.toList.drop (i.toNat + 1)) (bs.toList.drop (i.toNat + 1)) a _ _ _
        hrunT hrunR
      rw [hdra, hdrb]
      obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun
      refine ⟨hokF, ⟨M₂, ?_, hK₁.trans hK₂, hSt₁.trans hSt₂⟩, ?_, hL1⟩
      · rw [hstF]; exact hS₂
      · rw [hresF]; exact hres2

/-- **`defeq_list` refines `defEqList`.** Statement changes (the knot's `defeq` slot needs them):
`n ≤ 2 ^ 62`, the eager bit `eb = (mode >>> 1) &&& 1`, and both slices (when not empty) below the stack top. -/
theorem defeqList_refines' (p : Prog) (hp : IotaProg' p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d ao an bo bn : Word) (aas bs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 →
    SpineN s₀.mem ao an aas → SpineN s₀.mem bo bn bs →
    (an ≠ 0 → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) →
    (bn ≠ 0 → bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat) →
    CoreSpec p (n + 1) "defeq_list" [mode, vis, d, ao, an, bo, bn]
      (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat aas.toList bs.toList) decBool s₀ a₀ dn
      vis fe MM eb := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d ao an bo bn aas bs hS hm4 hebm hsa hsb hta htb
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (defeqList_spec p hp.defeqList n s₀ mode vis d ao an bo bn)
  subst hs0
  refine ⟨hloc, ?_⟩
  obtain ⟨hok, hca, hres, hL1⟩ := dlW_ok p n F hk hnF hn62 dn vis fe eb mode d ao an bo bn hm4 hebm aas bs
    (an.toNat - (0 : Word).toNat) (n + 1) s.mem a₀ MM 0 r s'.mem rfl (by simp) (by simp) (Nat.le_refl _)
    hS hsa hsb hta htb hW
  refine ⟨hok, ?_, ?_, hL1⟩
  · simpa using hca
  · simpa using hres

/-! ## `iota_index_ok` -/

/-- Model of `iota_index_ok`. -/
def ioW (p : Prog) (n : Nat) (m : Mem) (mode vis d mI rP cnP tyCtor mo mn xo xn : Word) :
    Option (List Word × Mem) :=
  if mI = rP then some ([1], m)
  else match callW p n "pi_residual" [tyCtor, mo, mn] m with
    | none => none
    | some (r₁, m₁) =>
      if r₁.headD 0 = 0 then some ([0], m₁)
      else if ¬ (136 : Word).toNat < (m₁.arr64 CTL).size then none
      else match callW p n "get_app_args" [r₁.tail.headD 0] m₁ with
        | none => none
        | some (r₂, m₂) =>
          match callW p n "defeq_list" [mode, vis, d, r₂.headD 0 + cnP,
              (r₂.tail.headD 0 - cnP) * (if cnP ≤ r₂.tail.headD 0 then 1 else 0), xo, xn] m₂ with
          | none => none
          | some (r₃, m₃) =>
            if (136 : Word).toNat < (m₃.arr64 CTL).size then
              some ([r₃.headD 0], m₃.set64 CTL 136 (rdW (m₁.arr64 CTL) 136))
            else none

theorem iotaIndexOk_spec (p : Prog) (hp : p.lookup "iota_index_ok" = some iotaIndexOkL) (n : Nat)
    (s₀ : St) (mode vis d mI rP cnP tyCtor mo mn xo xn : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_index_ok" [mode, vis, d, mI, rP, cnP, tyCtor, mo, mn, xo, xn]
    ⦃fun r s' => LocEq s' s₀ ∧
      ioW p n s₀.mem mode vis d mI rP cnP tyCtor mo mn xo xn = some (r.headD 0 :: [], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaIndexOkL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "pi_residual", callW_spec p n "get_app_args", callW_spec p n "defeq_list"] <;>
  simp_all [ioW, Cmp.eval, Cmp.evalW, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr, rdW, CTL] <;>
  (try refine ⟨?_, ?_⟩) <;>
  first
    | (congr 1; rw [Array.getElem?_eq_getElem]; rfl)
    | assumption
    | simpa using ‹UInt64.toNat 136 < _›

/-- The slice after the first `c` words, as `iota_index_ok` computes it. -/
theorem spine_drop (m : Mem) (off cnt c : Word) (xs : Array EIdx) (h : SpineR m off cnt xs)
    (hspn : (m.arr64 SPN).size < 2 ^ 63) :
    SpineN m (off + c) ((cnt - c) * (if c ≤ cnt then 1 else 0)) (xs.toList.drop c.toNat).toArray ∧
    (c ≤ cnt → (off + c).toNat + (cnt - c).toNat = off.toNat + cnt.toNat) := by
  by_cases hc : c ≤ cnt
  · have hc' : c.toNat ≤ cnt.toNat := hc
    have h1 : (cnt - c).toNat = cnt.toNat - c.toNat := UInt64.toNat_sub_of_le _ _ hc
    have hb := h.bound
    have h2 : (off + c).toNat = off.toNat + c.toNat := by
      rw [UInt64.toNat_add]; simp; omega
    simp only [hc, ↓reduceIte, UInt64.mul_one]
    refine ⟨⟨by simp [h.size, h1], fun hne => ?_⟩, fun _ => by rw [h2, h1]; omega⟩
    have hcnt : (cnt - c).toNat = xs.size - c.toNat := by rw [h1, h.size]
    refine ⟨by simp [h.size, h1], by rw [h2, h1]; omega, fun i hi => ?_, fun i hi => ?_⟩
    · have hi' : c.toNat + i < cnt.toNat := by omega
      have := h.lt (c.toNat + i) hi'
      have e : off + c + i.toUInt64 = off + (c.toNat + i).toUInt64 := by
        simp [Nat.toUInt64, UInt64.ofNat_add, UInt64.add_assoc]
      rw [e]; exact this
    · have hi' : c.toNat + i < xs.size := by
        simp at hi; omega
      have := h.get (c.toNat + i) hi'
      have e : off + c + i.toUInt64 = off + (c.toNat + i).toUInt64 := by
        simp [Nat.toUInt64, UInt64.ofNat_add, UInt64.add_assoc]
      rw [e]
      simpa using this
  · have hc' : cnt.toNat < c.toNat := by
      have : ¬ c.toNat ≤ cnt.toNat := hc
      omega
    simp only [hc, ↓reduceIte, UInt64.mul_zero]
    refine ⟨⟨by simp [h.size]; omega, fun hne => absurd rfl hne⟩, fun h => h.elim⟩

theorem iotaIndexOk_run_eq (r : CoreFnsA) (fe : IFEnv) (d mI rP cnP : Nat) (tyCtor : EIdx)
    (margs idx : List EIdx) (a : AState) (h : mI = rP) :
    (iotaIndexOk r fe d mI rP cnP tyCtor margs idx).run a = .ok (true, a) := by
  simp [iotaIndexOk, h]; rfl

theorem iotaIndexOk_run_none (r : CoreFnsA) (fe : IFEnv) (d mI rP cnP : Nat) (tyCtor : EIdx)
    (margs idx : List EIdx) (a a₁ : AState) (h : mI ≠ rP)
    (hp : (piResidual tyCtor margs).run a = .ok (none, a₁)) :
    (iotaIndexOk r fe d mI rP cnP tyCtor margs idx).run a = .ok (false, a₁) := by
  simp only [iotaIndexOk, h, ↓reduceIte, StateT.run_bind, hp, except_ok_bind]; rfl

theorem iotaIndexOk_run_some (r : CoreFnsA) (fe : IFEnv) (d mI rP cnP : Nat) (tyCtor : EIdx)
    (margs idx : List EIdx) (a a₁ a₂ : AState) (res : EIdx) (xs : List EIdx) (b : Bool)
    (h : mI ≠ rP) (hp : (piResidual tyCtor margs).run a = .ok (some res, a₁))
    (hg : (getAppArgs coreWalkFuel res).run a₁ = .ok (xs, a₁))
    (hd : (defEqList r fe d (xs.drop cnP) idx).run a₁ = .ok (b, a₂)) :
    (iotaIndexOk r fe d mI rP cnP tyCtor margs idx).run a = .ok (b, a₂) := by
  simp only [iotaIndexOk, h, ↓reduceIte, StateT.run_bind, hp, except_ok_bind, hg, hd]

/-- **`iota_index_ok` refines `iotaIndexOk`.** Statement changes (the callees need them): `n ≤ 2 ^ 62`,
the eager bit `eb = (mode >>> 1) &&& 1`, and both slices below the stack top. -/
theorem iotaIndexOk_refines' (p : Prog) (hp : IotaProg' p) (hc : IotaCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d mI rP cnP tyCtor mo mn xo xn : Word) (margs idx : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW tyCtor →
    SpineR s₀.mem mo mn margs → SpineR s₀.mem xo xn idx →
    mo.toNat + mn.toNat ≤ (spTop s₀.mem).toNat → xo.toNat + xn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p (n + 1) "iota_index_ok" [mode, vis, d, mI, rP, cnP, tyCtor, mo, mn, xo, xn]
      (iotaIndexOk (coreKnot (decMode mode) fe id F) fe d.toNat mI.toNat rP.toNat cnP.toNat
        (decE tyCtor) margs.toList idx.toList) decBool s₀ a₀ dn vis fe MM eb := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d mI rP cnP tyCtor mo mn xo xn margs idx hS hm4
    hebm hty hsm hsx htm htx
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (iotaIndexOk_spec p hp.iotaIndexOk n s₀ mode vis d mI rP cnP tyCtor mo mn xo xn)
  subst hs0
  refine ⟨hloc, ?_⟩
  simp only [ioW] at hW
  by_cases hI : mI = rP
  · rw [if_pos hI] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hr1 : r.headD 0 = 1 := by simpa using hr.symm
    have hrun1 := iotaIndexOk_run_eq (coreKnot (decMode mode) fe id F) fe d.toNat mI.toNat rP.toNat
      cnP.toNat (decE tyCtor) margs.toList idx.toList a₀ (by rw [hI])
    refine CoreRef.of_pure hS hrun1 hm.symm ?_ ?_
    · simp only [decBool]; rw [hr1]; rfl
    · unfold ResH HW; rw [hr1]; decide
  rw [if_neg hI] at hW
  have hI' : mI.toNat ≠ rP.toNat := fun h => hI (UInt64.toNat_inj.mp h)
  cases hc1 : callW p n "pi_residual" [tyCtor, mo, mn] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  simp only at hW
  obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hr₁⟩ := CoreSpec.of_callW
    (piResidual_refines' p hp hc n ⟨s.mem, Locals.init []⟩ a₀ dn vis fe MM eb tyCtor mo mn margs hS hty
      hsm htm) hc1
  have hrunP := AM.run_of_ok _ _ hok1
  rw [hres1] at hrunP
  by_cases h0 : r₁.headD 0 = 0
  · rw [if_pos h0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hnone : decOptR r₁ = none := by simp only [decOptR, decOpt, h0, ↓reduceIte]
    rw [hnone] at hrunP
    have hrun1 := iotaIndexOk_run_none (coreKnot (decMode mode) fe id F) fe d.toNat mI.toNat rP.toNat
      cnP.toNat (decE tyCtor) margs.toList idx.toList a₀ _ hI' hrunP
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun1
    have hr0 : r.headD 0 = 0 := by simpa using hr.symm
    refine ⟨hokF, ⟨M₁, ?_, hK₁, hm ▸ hSt₁⟩, ?_, ?_⟩
    · rw [hstF, ← hm]; exact hS₁
    · rw [hresF]; simp only [decBool]; rw [hr0]; rfl
    · unfold ResH HW; rw [hr0]; decide
  rw [if_neg h0] at hW
  by_cases h136 : ¬ (136 : Word).toNat < (m₁.arr64 CTL).size
  · rw [if_pos h136] at hW; cases hW
  rw [if_neg h136] at hW
  have h136' : (136 : Word).toNat < (m₁.arr64 CTL).size := Classical.not_not.mp h136
  obtain ⟨hf1, hh1⟩ := hr₁
  have hsome : decOptR r₁ = some (decE (r₁.tail.headD 0)) := by
    simp only [decOptR, decOpt, h0, ↓reduceIte]
  rw [hsome] at hrunP
  cases hc2 : callW p n "get_app_args" [r₁.tail.headD 0] m₁ with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW
  simp only at hW
  obtain ⟨t₂, ht₂, hloc2, hfr, hgrew, hhead, htop2, xs, hga, hsp2⟩ := triple_of_callW
    (getAppArgs_refines p hp.spine n ⟨m₁, Locals.init []⟩ (AM.st (piResidual (decE tyCtor) margs.toList) a₀)
      hS₁.arena.1 (r₁.tail.headD 0) hh1 hS₁.spn) hc2
  rw [ht₂] at hfr hgrew htop2 hsp2
  have hS₂ : CoreS dn m₂ (AM.st (piResidual (decE tyCtor) margs.toList) a₀) vis fe M₁ eb :=
    hS₁.frame_stk hfr (fun b hb => by simpa using hb) (fun x hx => by simpa using hx)
  have hsx₁ : SpineR m₁ xo xn idx := hsx.keep hSt₁.2.1 hSt₁.2.2 htx hS.spn
  have htx₁ : xo.toNat + xn.toNat ≤ (spTop m₁).toNat := by rw [hSt₁.1]; exact htx
  have hsx₂ : SpineR m₂ xo xn idx := hsx₁.keep hgrew.2.1 hgrew.2.2 htx₁ hS₁.spn
  have htx₂ : xo.toNat + xn.toNat ≤ (spTop m₂).toNat :=
    Nat.le_trans htx₁ (by have := hgrew.1; exact this)
  cases n with
  | zero => rw [callW_zero] at hW; cases hW
  | succ n' =>
  cases hc3 : callW p (n' + 1) "defeq_list" [mode, vis, d, r₂.headD 0 + cnP,
      (r₂.tail.headD 0 - cnP) * (if cnP ≤ r₂.tail.headD 0 then 1 else 0), xo, xn] m₂ with
  | none => rw [hc3] at hW; cases hW
  | some q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [hc3] at hW
  simp only at hW
  by_cases h136n : ¬ (136 : Word).toNat < (m₃.arr64 CTL).size
  · rw [if_neg (by simpa using h136n)] at hW; cases hW
  have h136₃ : (136 : Word).toNat < (m₃.arr64 CTL).size := Classical.not_not.mp h136n
  rw [if_pos h136₃] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  have hhead' : r₂.headD 0 = spTop m₁ := hhead
  have htop2' : spTop m₂ = spTop m₁ + r₂.tail.headD 0 := htop2
  obtain ⟨hsd, hsd2⟩ := spine_drop m₂ (r₂.headD 0) (r₂.tail.headD 0) cnP xs.toArray hsp2 hS₂.spn
  have hdrop : xs.toArray.toList.drop cnP.toNat = xs.drop cnP.toNat := by simp
  rw [hdrop] at hsd
  have htd : (r₂.tail.headD 0 - cnP) * (if cnP ≤ r₂.tail.headD 0 then 1 else 0) ≠ 0 →
      (r₂.headD 0 + cnP).toNat + ((r₂.tail.headD 0 - cnP) * (if cnP ≤ r₂.tail.headD 0 then 1 else 0)).toNat
        ≤ (spTop m₂).toNat := by
    intro hne
    have hcle : cnP ≤ r₂.tail.headD 0 := by
      exact Classical.byContradiction fun hn => by
        simp only [hn, ↓reduceIte, UInt64.mul_zero, ne_eq, not_true_eq_false] at hne
    simp only [hcle, ↓reduceIte, UInt64.mul_one] at hne ⊢
    rw [hsd2 hcle]
    have hb := hsp2.bound
    rw [hhead'] at hb
    have hsp := hS₂.spn
    have : (spTop m₂).toNat = (spTop m₁).toNat + (r₂.tail.headD 0).toNat := by
      rw [htop2', UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [hhead', this]
    exact Nat.le_refl _
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hr₃⟩ := CoreSpec.of_callW
    (defeqList_refines' p hp n' (hk.mono (Nat.le_succ n')) F (by omega) (by omega)
      ⟨m₂, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₂.headD 0 + cnP) _ xo xn
      (xs.drop cnP.toNat).toArray idx hS₂ hm4 hebm hsd hsx₂.toN htd (fun _ => htx₂)) hc3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  simp only [List.toList_toArray] at hrun3
  have hrunF := iotaIndexOk_run_some (coreKnot (decMode mode) fe id F) fe d.toNat mI.toNat rP.toNat
    cnP.toNat (decE tyCtor) margs.toList idx.toList a₀ _ _ (decE (r₁.tail.headD 0)) xs (decBool r₃)
    hI' hrunP hga hrun3
  obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrunF
  have hr3 : r₃.headD 0 = r.headD 0 := by simpa using hr
  refine ⟨hokF, ⟨M₃, ?_, hK₁.trans hK₃, ?_⟩, ?_, ?_⟩
  · rw [hstF, ← hm]
    exact hS₃.frame_stk (MemFrame.setCtl m₃ 136 _) (by simp) (by simp)
  · rw [← hm]
    have t1 : spTop m₁ = spTop s.mem := hSt₁.1
    refine hSt₁.trans ?_
    apply StackKept.restore _ (by rw [hSt₃.2.1, hgrew.2.1]) h136₃
    intro i hi
    have hi2 : i < spTop m₂ := UInt64.lt_of_lt_of_le hi hgrew.1
    rw [hSt₃.2.2 i hi2, hgrew.2.2 i hi]
  · rw [hresF]; simp only [decBool]; rw [← hr3]
  · unfold ResH HW; rw [← hr3]; exact hr₃

/-! ## `tower_slots_all(vis, T, nF)` -/

/-- Model of the `tower_slots_all` loop at L fuel `k`. -/
def tsW (p : Prog) (vis T nF : Word) : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | k + 1, m, j =>
    if j < nF then
      match callW p k "find_proj" [vis, T, j] m with
      | none => none
      | some (r, m₁) => if r.headD 0 = 0 then some ([0], m₁) else tsW p vis T nF k m₁ (j + 1)
    else some ([1], m)

theorem tsW_end (p : Prog) (vis T nF : Word) (k : Nat) (m : Mem) (j : Word) (h : ¬ j < nF) :
    tsW p vis T nF (k + 1) m j = some ([1], m) := by
  simp only [tsW, h, ↓reduceIte]

theorem tsW_stop (p : Prog) (vis T nF : Word) (k : Nat) (m m₁ : Mem) (j : Word) (r : List Word)
    (h : j < nF) (hc : callW p k "find_proj" [vis, T, j] m = some (r, m₁)) (h0 : r.headD 0 = 0) :
    tsW p vis T nF (k + 1) m j = some ([0], m₁) := by
  simp only [tsW, h, ↓reduceIte, hc, h0]

theorem tsW_cont (p : Prog) (vis T nF : Word) (k : Nat) (m m₁ : Mem) (j : Word) (r : List Word)
    (h : j < nF) (hc : callW p k "find_proj" [vis, T, j] m = some (r, m₁)) (h0 : ¬ r.headD 0 = 0) :
    tsW p vis T nF (k + 1) m j = tsW p vis T nF k m₁ (j + 1) := by
  simp only [tsW, h, ↓reduceIte, hc, h0]

theorem towerSlotsAllLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k towerSlotsAllLoop
    ⦃fun r s' => r ≠ .brk ∧
      tsW p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) k s₀.mem (s₀.loc 3) = some (r.retOr [1], s'.mem); ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := towerSlotsAllLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs,
        callW_spec p k "find_proj", ih] <;> finish [tsW_end, tsW_stop, tsW_cont]

theorem towerSlotsAllLoop_step_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p k) towerSlotsAllLoop
    ⦃fun r s' => r ≠ .brk ∧
      tsW p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (k + 1) s₀.mem (s₀.loc 3) =
        some (r.retOr [1], s'.mem); ⊤⦄ :=
  Triple.step_exec (towerSlotsAllLoop_spec p (k + 1) s₀)

theorem towerSlotsAll_spec (p : Prog) (hp : p.lookup "tower_slots_all" = some towerSlotsAllL)
    (k : Nat) (s₀ : St) (vis T nF : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "tower_slots_all" [vis, T, nF]
    ⦃fun r s' => LocEq s' s₀ ∧ tsW p vis T nF (k + 1) s₀.mem 0 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, towerSlotsAllL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, towerSlotsAllLoop_step_spec p k] <;>
    finish

theorem towerSlotsAllGo_zero_run (fe : IFEnv) (T : NIdx) (j : Nat) (a : AState) :
    (towerSlotsAllGo fe T 0 j).run a = .ok (true, a) := by
  simp [towerSlotsAllGo]; rfl

theorem towerSlotsAllGo_stop_run (fe : IFEnv) (T : NIdx) (n j : Nat) (a a₁ : AState)
    (o : Option IProjEntry) (h : (fe.findProj? T j).run a = .ok (o, a₁)) (ho : o.isSome = false) :
    (towerSlotsAllGo fe T (n + 1) j).run a = .ok (false, a₁) := by
  simp only [towerSlotsAllGo, StateT.run_bind, h, except_ok_bind, ho]; rfl

theorem towerSlotsAllGo_cont_run (fe : IFEnv) (T : NIdx) (n j : Nat) (a a₁ a₂ : AState)
    (o : Option IProjEntry) (b : Bool) (h : (fe.findProj? T j).run a = .ok (o, a₁))
    (ho : o.isSome = true) (hr : (towerSlotsAllGo fe T n (j + 1)).run a₁ = .ok (b, a₂)) :
    (towerSlotsAllGo fe T (n + 1) j).run a = .ok (b, a₂) := by
  simp only [towerSlotsAllGo, StateT.run_bind, h, except_ok_bind, ho]; exact hr

/-- **The `tower_slots_all` loop refines `towerSlotsAllGo`**, by induction on the remaining count. -/
theorem tsW_ok (p : Prog) (hcc : CoreCallees p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (eb T nF : Word) (hT : HW T) :
    ∀ (K k : Nat) (m : Mem) (a : AState) (M : ModeMaps) (j : Word) (L : List Word) (m' : Mem),
      nF.toNat - j.toNat = K → j.toNat ≤ nF.toNat → CoreS dn m a vis fe M eb →
      tsW p vis T nF k m j = some (L, m') →
      AM.ok (towerSlotsAllGo fe (decI T) K j.toNat) a ∧
      CoreAfter dn m m' (AM.st (towerSlotsAllGo fe (decI T) K j.toNat) a) vis fe M eb ∧
      AM.res (towerSlotsAllGo fe (decI T) K j.toNat) a = decBool L ∧ HW (L.headD 0) := by
  intro K
  induction K with
  | zero =>
    intro k m a M j L m' hK hj hS hL
    have hn : ¬ j < nF := fun h => by
      have : j.toNat < nF.toNat := h
      omega
    cases k with
    | zero => simp [tsW] at hL
    | succ k =>
    rw [tsW_end p vis T nF k m j hn] at hL
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (towerSlotsAllGo_zero_run fe (decI T) j.toNat a)
    refine ⟨hok, ?_, ?_, by simp [HW]⟩
    · rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩
    · rw [hres]; simp [decBool]
  | succ K ih =>
    intro k m a M j L m' hK hj hS hL
    have hlt : j < nF := by
      have : j.toNat < nF.toNat := by omega
      exact this
    cases k with
    | zero => simp [tsW] at hL
    | succ k =>
    cases hc : callW p k "find_proj" [vis, T, j] m with
    | none => simp [tsW, hlt, hc] at hL
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    obtain ⟨hok, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres, hr₁⟩ := CoreSpec.of_callW
      (hcc.findProj k ⟨m, Locals.init []⟩ a dn vis fe M eb T j hS hT) hc
    have hrunF := AM.run_of_ok _ _ hok
    by_cases h0 : r₁.headD 0 = 0
    · rw [tsW_stop p vis T nF k m m₁ j r₁ hlt hc h0] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      have hnone : AM.res (fe.findProj? (decI T) j.toNat) a = none := by
        rw [hres]; simp only [decEntry, h0, ↓reduceIte]
      rw [hnone] at hrunF
      obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _
        (towerSlotsAllGo_stop_run fe (decI T) K j.toNat a _ none hrunF rfl)
      refine ⟨hokF, ⟨M₁, ?_, hK₁, hSt₁⟩, ?_, by simp [HW]⟩
      · rw [hstF]; exact hS₁
      · rw [hresF]; simp [decBool]
    · rw [tsW_cont p vis T nF k m m₁ j r₁ hlt hc h0] at hL
      obtain ⟨tbl, htbl⟩ := hcc.projFound k m a dn vis fe M eb T j r₁ m₁ hS hc h0
      have hsome : AM.res (fe.findProj? (decI T) j.toNat) a = some (tbl.entry j.toNat) := by
        rw [hres]; simp only [decEntry, if_neg h0, htbl, Option.map_some]
      rw [hsome] at hrunF
      have h1 : (j + 1).toNat = j.toNat + 1 := uint64_succ_toNat nF j hlt
      obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hL1⟩ := ih k m₁ _ M₁ (j + 1) L m'
        (by omega) (by omega) hS₁ hL
      rw [h1] at hok2 hS₂ hres2
      have hrunR := AM.run_of_ok _ _ hok2
      obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _
        (towerSlotsAllGo_cont_run fe (decI T) K j.toNat a _ _ _ _ hrunF rfl hrunR)
      refine ⟨hokF, ⟨M₂, ?_, hK₁.trans hK₂, hSt₁.trans hSt₂⟩, ?_, hL1⟩
      · rw [hstF]; exact hS₂
      · rw [hresF]; exact hres2

/-- **`tower_slots_all` refines `towerSlotsAll`** (`find_proj` and its decoding fact as
`CoreCallees`). -/
theorem towerSlotsAll_refines' (p : Prog) (hp : IotaProg' p) (hcc : CoreCallees p) :
    TowerSlotsAllOK p := by
  intro n s₀ a₀ dn vis fe MM eb T nF hS hT
  cases n with
  | zero =>
    apply L.M.triple_of_run
    intro s r s' _ hrun
    exact (invoke_zero_run _ _ _ _ _ _ hrun).elim
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (towerSlotsAll_spec p hp.towerSlotsAll n s₀ vis T nF)
  subst hs0
  refine ⟨hloc, ?_⟩
  obtain ⟨hok, hca, hres, hL1⟩ := tsW_ok p hcc dn vis fe eb T nF hT (nF.toNat - (0 : Word).toNat) (n + 1)
    s.mem a₀ MM 0 r s'.mem rfl (by simp) hS hW
  refine ⟨hok, ?_, ?_, hL1⟩
  · simpa [towerSlotsAll] using hca
  · simpa [towerSlotsAll] using hres

end L.Arena
