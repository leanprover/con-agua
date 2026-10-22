import ConAgua.Arena.WhnfIota
import ConAgua.Arena.PinsNatOp
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.RomExprRef

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
  pinat : p.lookup "pin_at" = some pinAtL
  projf : p.lookup "proj_find" = some projFind
  projp : p.lookup "proj_push" = some projPush
  proji : p.lookup "intern_proj" = some internProj
  mkproj : p.lookup "mk_proj" = some mkProj

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

/-! ## `inst_spine(ao, an, t, e)` -/

/-- Model of the `inst_spine` loop at L fuel `k`. -/
def isW (p : Prog) (ao an : Word) : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | k + 1, m, t, e, i =>
    if i < an then
      match callW p k "inst_entry" [e, rdW (m.arr64 SPN) (ao + i), t] m with
      | none => none
      | some (r, m₁) => isW p ao an k m₁ (t - 1) (r.headD 0) (i + 1)
    else some (e, m)

theorem isW_end (p : Prog) (ao an : Word) (k : Nat) (m : Mem) (t e i : Word) (h : ¬ i < an) :
    isW p ao an (k + 1) m t e i = some (e, m) := by
  simp only [isW, h, ↓reduceIte]

theorem isW_cont (p : Prog) (ao an : Word) (k : Nat) (m m₁ : Mem) (t e i : Word) (r : List Word)
    (h : i < an) (hc : callW p k "inst_entry" [e, rdW (m.arr64 SPN) (ao + i), t] m = some (r, m₁)) :
    isW p ao an (k + 1) m t e i = isW p ao an k m₁ (t - 1) (r.headD 0) (i + 1) := by
  simp only [isW, h, ↓reduceIte, hc]

theorem instSpineLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k instSpineLoop
    ⦃fun r s' => r = .normal ∧
      isW p (s₀.loc 0) (s₀.loc 1) k s₀.mem (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) = some (s'.loc 3, s'.mem); ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := instSpineLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p k "inst_entry", ih] <;> finish [isW_end, isW_cont]

theorem instSpineLoop_step_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p k) instSpineLoop
    ⦃fun r s' => r = .normal ∧
      isW p (s₀.loc 0) (s₀.loc 1) (k + 1) s₀.mem (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) =
        some (s'.loc 3, s'.mem); ⊤⦄ :=
  Triple.step_exec (instSpineLoop_spec p (k + 1) s₀)

theorem instSpine_spec (p : Prog) (hp : p.lookup "inst_spine" = some instSpineL) (k : Nat)
    (s₀ : St) (ao an t e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "inst_spine" [ao, an, t, e]
    ⦃fun r s' => LocEq s' s₀ ∧ isW p ao an (k + 1) s₀.mem t e 0 = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, instSpineL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, instSpineLoop_step_spec p k] <;>
    finish

theorem instSpine_nil_run (fuel : Nat) (t : Nat) (e : EIdx) (a : AState) :
    (instSpine fuel [] t e).run a = .ok (e, a) := by
  simp [instSpine]; rfl

theorem instSpine_cons_run (fuel : Nat) (x : EIdx) (xs : List EIdx) (t : Nat) (e e' : EIdx)
    (a a₁ a₂ : AState) (res : EIdx) (h : (instantiate1Fast fuel e x t).run a = .ok (e', a₁))
    (hr : (instSpine fuel xs (t - 1) e').run a₁ = .ok (res, a₂)) :
    (instSpine fuel (x :: xs) t e).run a = .ok (res, a₂) := by
  simp only [instSpine, StateT.run_bind, h, except_ok_bind]; exact hr

/-- **The `inst_spine` loop refines `instSpine`**, by induction on the remaining count. -/
theorem isW_ok (p : Prog) (hinst : IotaInst1OK p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (eb ao an : Word) (args : Array EIdx) :
    ∀ (K k : Nat) (m : Mem) (a : AState) (M : ModeMaps) (t e i : Word) (tN : Nat) (r : Word) (m' : Mem),
      an.toNat - i.toNat = K → i.toNat ≤ an.toNat → an.toNat - i.toNat ≤ t.toNat + 1 →
      (an.toNat - i.toNat ≠ 0 → tN = t.toNat) →
      CoreS dn m a vis fe M eb → HW e → SpineR m ao an args →
      ao.toNat + an.toNat ≤ (spTop m).toNat →
      isW p ao an k m t e i = some (r, m') →
      AM.ok (instSpine coreWalkFuel (args.toList.drop i.toNat) tN (decE e)) a ∧
      CoreAfter dn m m' (AM.st (instSpine coreWalkFuel (args.toList.drop i.toNat) tN (decE e)) a) vis fe M eb ∧
      AM.res (instSpine coreWalkFuel (args.toList.drop i.toNat) tN (decE e)) a = decE r ∧ HW r := by
  intro K
  induction K with
  | zero =>
    intro k m a M t e i tN r m' hK hia ht htN hS he hsp htop hL
    have hn : ¬ i < an := fun h => by
      have : i.toNat < an.toNat := h
      omega
    cases k with
    | zero => simp [isW] at hL
    | succ k =>
    rw [isW_end p ao an k m t e i hn] at hL
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
    have hdrop : args.toList.drop i.toNat = [] := by
      apply List.drop_eq_nil_of_le; simp [hsp.size]; omega
    rw [hdrop]
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (instSpine_nil_run coreWalkFuel tN (decE e) a)
    exact ⟨hok, by rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, hres, he⟩
  | succ K ih =>
    intro k m a M t e i tN r m' hK hia ht htN hS he hsp htop hL
    have hlt : i < an := by
      have : i.toNat < an.toNat := by omega
      exact this
    have hlt' : i.toNat < an.toNat := hlt
    have hsz : i.toNat < args.size := by rw [hsp.size]; exact hlt'
    have hdrop : args.toList.drop i.toNat = args[i.toNat] :: args.toList.drop (i.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hsz)]; simp
    have hget : args[i.toNat] = decE (rdW (m.arr64 SPN) (ao + i)) := by
      have := hsp.get i.toNat hsz
      simpa [spW, toUInt64_toNat_self] using this
    rw [hget] at hdrop
    have htt : tN = t.toNat := htN (by omega)
    cases k with
    | zero => simp [isW] at hL
    | succ k =>
    cases hc : callW p k "inst_entry" [e, rdW (m.arr64 SPN) (ao + i), t] m with
    | none => simp [isW, hlt, hc] at hL
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [isW_cont p ao an k m m₁ t e i r₁ hlt hc] at hL
    obtain ⟨hok, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres, hr₁⟩ := CoreSpec.of_callW
      (hinst k ⟨m, Locals.init []⟩ a dn vis fe M eb e (rdW (m.arr64 SPN) (ao + i)) t hS he) hc
    have hsp₁ : SpineR m₁ ao an args := hsp.keep hSt₁.2.1 hSt₁.2.2 htop hS.spn
    have htop₁ : ao.toNat + an.toNat ≤ (spTop m₁).toNat := by rw [hSt₁.1]; exact htop
    have h1 : (i + 1).toNat = i.toNat + 1 := uint64_succ_toNat an i hlt
    have ht1 : (an.toNat - (i.toNat + 1) ≠ 0 → tN - 1 = (t - 1).toNat) := by
      intro hne
      have ht0 : t ≠ 0 := fun h => by subst h; simp at ht; omega
      have : (t - 1).toNat = t.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by
          have : t.toNat ≠ 0 := fun h => ht0 (UInt64.toNat_inj.mp (by simpa using h))
          simp [UInt64.le_iff_toNat_le]; omega)]
        simp
      rw [this, htt]
    obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hr⟩ := ih k m₁ _ M₁ (t - 1) (r₁.headD 0) (i + 1) (tN - 1)
      r m' (by omega) (by omega) (by
        have e0 : an.toNat - (i + 1).toNat = an.toNat - i.toNat - 1 := by omega
        by_cases ht0 : t = 0
        · have h00 : t.toNat = 0 := by rw [ht0]; rfl
          rw [e0]; omega
        · have ht0' : t.toNat ≠ 0 := fun h => ht0 (UInt64.toNat_inj.mp (by simpa using h))
          have : (t - 1).toNat = t.toNat - 1 := by
            rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]
            simp
          rw [e0, this]; omega)
      (by rw [h1]; exact ht1) hS₁ hr₁ hsp₁ htop₁ hL
    have hrunT := AM.run_of_ok _ _ hok
    rw [hres] at hrunT
    have hrunR := AM.run_of_ok _ _ hok2
    rw [h1] at hrunR
    rw [h1] at hS₂ hres2
    have hrun := instSpine_cons_run coreWalkFuel (decE (rdW (m.arr64 SPN) (ao + i)))
      (args.toList.drop (i.toNat + 1)) tN (decE e) (decH r₁) a _ _ _
      (by rw [htt]; exact hrunT) hrunR
    rw [hdrop]
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun
    refine ⟨hokF, ⟨M₂, ?_, hK₁.trans hK₂, hSt₁.trans hSt₂⟩, ?_, hr⟩
    · rw [hstF]; exact hS₂
    · rw [hresF]; exact hres2

/-- **`inst_spine` refines `instSpine`.** Statement changes: `ao + an ≤ spTop` (the slice is below the
top, so `inst_entry` leaves it alone) and `an ≤ t + 1` (the L counter `t - 1` wraps where the twin's
`Nat` subtraction saturates; with `an ≤ t + 1` it is only after the last use). -/
theorem instSpine_refines' (p : Prog) (hp : IotaProg' p) (hc : IotaCallees p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb ao an t e : Word) (args : Array EIdx), CoreS dn s₀.mem a₀ vis fe MM eb →
    HW e → SpineR s₀.mem ao an args → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    an.toNat ≤ t.toNat + 1 →
    CoreSpec p n "inst_spine" [ao, an, t, e] (instSpine coreWalkFuel args.toList t.toNat (decE e))
      decH s₀ a₀ dn vis fe MM eb := by
  intro n s₀ a₀ dn vis fe MM eb ao an t e args hS he hsp htop ht
  cases n with
  | zero =>
    apply L.M.triple_of_run
    intro s r s' _ hrun
    exact (invoke_zero_run _ _ _ _ _ _ hrun).elim
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (instSpine_spec p hp.instSpine n s₀ ao an t e)
  subst hs0
  refine ⟨hloc, ?_⟩
  obtain ⟨hok, hca, hres, hr⟩ := isW_ok p hc.inst1 dn vis fe eb ao an args
    (an.toNat - (0 : Word).toNat) (n + 1) s.mem a₀ MM t e 0 t.toNat (r.headD 0) s'.mem rfl (by simp)
    (by simpa using ht) (fun _ => rfl) hS he hsp htop hW
  refine ⟨hok, ?_, ?_, hr⟩
  · simpa using hca
  · simpa [decH] using hres

/-! ## `inst_spine_pins(po, pl, us, ao, rP, pvo, pvc)` -/

/-- Model of the `inst_spine_pins` loop at L fuel `k`. -/
def ispW (p : Prog) (po pl us ao rP pvo pvc so : Word) : Nat → Mem → Word → Option Mem
  | 0, _, _ => none
  | k + 1, m, j =>
    if j < pvc then
      match callW p k "inst_lp" [po, pl, us, rdW (m.arr64 SPN) (pvo + j)] m with
      | none => none
      | some (r₁, m₁) =>
        match callW p k "inst_spine" [ao, rP, rP - 1, r₁.headD 0] m₁ with
        | none => none
        | some (r₂, m₂) =>
          if (so + j).toNat < (m₂.arr64 SPN).size ∧ (136 : Word).toNat < (m₂.arr64 CTL).size then
            ispW p po pl us ao rP pvo pvc so k
              ((m₂.set64 SPN (so + j) (r₂.headD 0)).set64 CTL 136 (so + j + 1)) (j + 1)
          else none
    else some m

theorem ispW_end (p : Prog) (po pl us ao rP pvo pvc so : Word) (k : Nat) (m : Mem) (j : Word)
    (h : ¬ j < pvc) : ispW p po pl us ao rP pvo pvc so (k + 1) m j = some m := by
  simp only [ispW, h, ↓reduceIte]

theorem ispW_cont (p : Prog) (po pl us ao rP pvo pvc so : Word) (k : Nat) (m m₁ m₂ : Mem) (j : Word)
    (r₁ r₂ : List Word) (h : j < pvc)
    (hc1 : callW p k "inst_lp" [po, pl, us, rdW (m.arr64 SPN) (pvo + j)] m = some (r₁, m₁))
    (hc2 : callW p k "inst_spine" [ao, rP, rP - 1, r₁.headD 0] m₁ = some (r₂, m₂))
    (hg : (so + j).toNat < (m₂.arr64 SPN).size ∧ (136 : Word).toNat < (m₂.arr64 CTL).size) :
    ispW p po pl us ao rP pvo pvc so (k + 1) m j =
      ispW p po pl us ao rP pvo pvc so k
        ((m₂.set64 SPN (so + j) (r₂.headD 0)).set64 CTL 136 (so + j + 1)) (j + 1) := by
  simp only [ispW, h, ↓reduceIte, hc1, hc2, hg, and_self]

theorem ispW_bad (p : Prog) (po pl us ao rP pvo pvc so : Word) (k : Nat) (m m₁ m₂ : Mem) (j : Word)
    (r₁ r₂ : List Word) (h : j < pvc)
    (hc1 : callW p k "inst_lp" [po, pl, us, rdW (m.arr64 SPN) (pvo + j)] m = some (r₁, m₁))
    (hc2 : callW p k "inst_spine" [ao, rP, rP - 1, r₁.headD 0] m₁ = some (r₂, m₂))
    (hg : ¬ ((so + j).toNat < (m₂.arr64 SPN).size ∧ (136 : Word).toNat < (m₂.arr64 CTL).size)) :
    ispW p po pl us ao rP pvo pvc so (k + 1) m j = none := by
  simp only [ispW, h, ↓reduceIte, hc1, hc2, hg]

theorem instSpinePinsLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k instSpinePinsLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 6 = s₀.loc 6 ∧ s'.loc 7 = s₀.loc 7 ∧
      ispW p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7)
        k s₀.mem (s₀.loc 8) = some s'.mem; ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := instSpinePinsLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        callW_spec p k "inst_lp", callW_spec p k "inst_spine", ih] <;>
      finish [ispW_end, ispW_cont, ispW_bad]

theorem instSpinePinsLoop_step_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p k) instSpinePinsLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 6 = s₀.loc 6 ∧ s'.loc 7 = s₀.loc 7 ∧
      ispW p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7)
        (k + 1) s₀.mem (s₀.loc 8) = some s'.mem; ⊤⦄ :=
  Triple.step_exec (instSpinePinsLoop_spec p (k + 1) s₀)

/-- Model of `inst_spine_pins`. -/
def ispTop (p : Prog) (k : Nat) (m : Mem) (po pl us ao rP pvo pvc : Word) :
    Option (List Word × Mem) :=
  if (136 : Word).toNat < (m.arr64 CTL).size then
    if UInt64.ofNat (m.arr64 SPN).size < rdW (m.arr64 CTL) 136 then none
    else if UInt64.ofNat (m.arr64 SPN).size - rdW (m.arr64 CTL) 136 < pvc then none
    else match ispW p po pl us ao rP pvo pvc (rdW (m.arr64 CTL) 136) (k + 1) m 0 with
      | none => none
      | some m' => some ([rdW (m.arr64 CTL) 136, pvc], m')
  else none

theorem getD_136 (a : Array Word) (h : 136 < a.size) : a[136]?.getD 0 = a[136] := by simp [h]

theorem instSpinePins_spec (p : Prog) (hp : p.lookup "inst_spine_pins" = some instSpinePinsL)
    (k : Nat) (s₀ : St) (po pl us ao rP pvo pvc : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "inst_spine_pins" [po, pl, us, ao, rP, pvo, pvc]
    ⦃fun r s' => LocEq s' s₀ ∧ ispTop p k s₀.mem po pl us ao rP pvo pvc = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, instSpinePinsL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    instSpinePinsLoop_step_spec p k] <;>
  simp_all [ispTop, Cmp.eval, BinOp.eval, Mem.len64, LocEq, St.setLocs_cons, St.setLoc_loc,
    St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal,
    Sig.retOr, rdW, CTL] <;>
  (have h136 : 136 < (s₀.mem.arr64 1).size := by assumption
   refine ⟨h136, ?_⟩
   simp_all [getD_136 _ h136, SPN])

/-! ### The push of `inst_spine_pins`: one word stored at the top, the top raised -/

/-- Storing `v` at the top `q` of the stack and raising the top: the frame, the new top, the slot,
and that the stack below the old top is as it was. -/
theorem push_step (m : Mem) (q v : Word) (hq : q.toNat < (m.arr64 SPN).size)
    (h136 : (136 : Word).toNat < (m.arr64 CTL).size) (htop : spTop m = q)
    (hq1 : q.toNat + 1 < 2 ^ 64) :
    MemFrame [SPN] [136] m ((m.set64 SPN q v).set64 CTL 136 (q + 1)) ∧
    spTop ((m.set64 SPN q v).set64 CTL 136 (q + 1)) = q + 1 ∧
    StackGrew m ((m.set64 SPN q v).set64 CTL 136 (q + 1)) ∧
    spW ((m.set64 SPN q v).set64 CTL 136 (q + 1)) q = v ∧
    (((m.set64 SPN q v).set64 CTL 136 (q + 1)).arr64 SPN).size = (m.arr64 SPN).size := by
  have f1 : MemFrame [SPN] [136] m (m.set64 SPN q v) :=
    (MemFrame.set64 m SPN (by decide) q v).mono (fun b hb => hb)
      (fun x hx => absurd hx (by simp))
  have f2 : MemFrame [SPN] [136] (m.set64 SPN q v) ((m.set64 SPN q v).set64 CTL 136 (q + 1)) :=
    (MemFrame.setCtl (m.set64 SPN q v) 136 (q + 1)).mono (fun b hb => absurd hb (by simp))
      (fun x hx => hx)
  have hsz : (((m.set64 SPN q v).set64 CTL 136 (q + 1)).arr64 SPN).size = (m.arr64 SPN).size := by
    rw [size_set64, size_set64]
  have htop' : spTop ((m.set64 SPN q v).set64 CTL 136 (q + 1)) = q + 1 := by
    unfold spTop
    rw [rdW_set64, if_pos ⟨rfl, rfl, by rw [size_set64]; exact h136⟩]
  have hq1' : (q + 1).toNat = q.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  refine ⟨f1.trans f2, htop', ⟨?_, hsz, fun i hi => ?_⟩, ?_, hsz⟩
  · rw [htop', htop, UInt64.le_iff_toNat_le, hq1']; omega
  · rw [spW_setCtl]
    have : q ≠ i := by
      intro h; rw [htop, ← h] at hi
      exact absurd (UInt64.lt_iff_toNat_lt.mp hi) (Nat.lt_irrefl _)
    rw [spW_set64_ne _ _ _ _ this]
  · rw [spW_setCtl, spW_set64_eq _ _ _ hq]

theorem word_succ_add (off : Word) (i : Nat) :
    off + (i + 1).toUInt64 = (off + 1) + i.toUInt64 := by
  simp [Nat.toUInt64, UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm]

/-- A slot followed by a spine slice is a spine slice. -/
theorem SpineR.cons_slot (m : Mem) (off cnt v : Word) (ys : List EIdx) (hv : HW v)
    (hslot : spW m off = v) (htail : SpineR m (off + 1) cnt ys.toArray)
    (hb : off.toNat + cnt.toNat + 1 ≤ (m.arr64 SPN).size) (hcap : (m.arr64 SPN).size < 2 ^ 63) :
    SpineR m off (cnt + 1) (decE v :: ys).toArray := by
  have hc1 : (cnt + 1).toNat = cnt.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have ho1 : (off + 1).toNat = off.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have hsize := htail.size
  simp only [List.size_toArray] at hsize
  refine ⟨by simp [hsize, hc1], by rw [hc1]; omega, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hc1] at hi
    cases i with
    | zero => simpa [hslot, HW] using hv
    | succ i =>
      rw [word_succ_add]
      exact htail.lt i (by omega)
  · simp only [List.size_toArray, List.length_cons] at hi
    cases i with
    | zero => simp [hslot]
    | succ i =>
      rw [word_succ_add]
      have := htail.get i (by simp only [List.size_toArray]; omega)
      simpa using this

theorem instSpinePins_nil_run (lps : List NIdx) (us : LsIdx) (args : List EIdx) (rP : Nat)
    (a : AState) : (instSpinePins lps us args rP []).run a = .ok ([], a) := by
  simp [instSpinePins]; rfl

theorem instSpinePins_cons_run (lps : List NIdx) (us : LsIdx) (args : List EIdx) (rP : Nat)
    (x : EIdx) (xs : List EIdx) (a a₁ a₂ a₃ : AState) (q s : EIdx) (ys : List EIdx)
    (h1 : (instLPFast coreWalkFuel lps us x).run a = .ok (q, a₁))
    (h2 : (instSpine coreWalkFuel (args.take rP) (rP - 1) q).run a₁ = .ok (s, a₂))
    (h3 : (instSpinePins lps us args rP xs).run a₂ = .ok (ys, a₃)) :
    (instSpinePins lps us args rP (x :: xs)).run a = .ok (s :: ys, a₃) := by
  simp only [instSpinePins, StateT.run_bind, h1, except_ok_bind, h2, h3]; rfl

/-- **`inst_lp` and `inst_spine` leave the record pool alone** (new stub assumption, as `ErecKept`
for `find_proj`/`fire_ok`): `inst_spine_pins` re-reads the level-parameter slice `(po, pl)` of
`EREC` at every iteration, the twin holds it as a value. -/
def ErecKeptInst (p : Prog) : Prop :=
  ∀ (n : Nat) (f : FnName) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem),
    (f = "inst_lp" ∨ f = "inst_spine") → callW p n f vs m = some (r, m') →
    m'.arr64 EREC = m.arr64 EREC

theorem SpineR.nil_at (m : Mem) (off : Word) (h : off.toNat ≤ (m.arr64 SPN).size) :
    SpineR m off 0 #[] :=
  ⟨rfl, by simpa using h, fun i hi => absurd hi (by simp), fun i hi => absurd hi (by simp)⟩

/-- **The `inst_spine_pins` loop refines `instSpinePins`**, by induction on the remaining count. -/
theorem ispW_ok (p : Prog) (hp : IotaProg' p) (hc : IotaCallees p) (hw : WhnfCallees p)
    (hE : ErecKeptInst p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb po pl us ao rP pvo pvc so : Word) (hus : HW us) (lps : List NIdx) (args pins : Array EIdx) :
    ∀ (K k : Nat) (m : Mem) (a : AState) (M : ModeMaps) (j : Word) (m' : Mem),
      pvc.toNat - j.toNat = K → j.toNat ≤ pvc.toNat → CoreS dn m a vis fe M eb →
      hslice? (m.arr64 EREC) po.toNat pl.toNat = some lps →
      spTop m = so + j → so.toNat + pvc.toNat ≤ (m.arr64 SPN).size →
      ao.toNat + rP.toNat ≤ so.toNat → pvo.toNat + pvc.toNat ≤ so.toNat →
      SpineR m ao rP args → SpineR m pvo pvc pins →
      ispW p po pl us ao rP pvo pvc so k m j = some m' →
      ∃ ys, AM.ok (instSpinePins lps (decI us) args.toList rP.toNat (pins.toList.drop j.toNat)) a ∧
        CoreAfterG dn m m' (AM.st (instSpinePins lps (decI us) args.toList rP.toNat
          (pins.toList.drop j.toNat)) a) vis fe M eb ∧
        AM.res (instSpinePins lps (decI us) args.toList rP.toNat (pins.toList.drop j.toNat)) a = ys ∧
        SpineR m' (so + j) (pvc - j) ys.toArray := by
  intro K
  induction K with
  | zero =>
    intro k m a M j m' hK hj hS hlps htop hso hat hpt hsa hsp hL
    have hn : ¬ j < pvc := fun h => by
      have : j.toNat < pvc.toNat := h
      omega
    cases k with
    | zero => simp [ispW] at hL
    | succ k =>
    rw [ispW_end p po pl us ao rP pvo pvc so k m j hn] at hL
    cases hL
    have hdrop : pins.toList.drop j.toNat = [] := by
      apply List.drop_eq_nil_of_le; simp [hsp.size]; omega
    rw [hdrop]
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _
      (instSpinePins_nil_run lps (decI us) args.toList rP.toNat a)
    refine ⟨[], hok, ?_, hres, ?_⟩
    · rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, (StackKept.refl _).toGrew⟩
    · have hjp : pvc - j = 0 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]
        simp; omega
      rw [hjp]
      have hlen : (so + j).toNat ≤ (m.arr64 SPN).size := by
        have := hS.spn
        rw [UInt64.toNat_add]; simp; omega
      exact SpineR.nil_at m _ hlen
  | succ K ih =>
    intro k m a M j m' hK hj hS hlps htop hso hat hpt hsa hsp hL
    have hlt : j < pvc := by
      have : j.toNat < pvc.toNat := by omega
      exact this
    have hlt' : j.toNat < pvc.toNat := hlt
    cases k with
    | zero => simp [ispW] at hL
    | succ k =>
    have hspn := hS.spn
    have hsoj : (so + j).toNat = so.toNat + j.toNat := by
      rw [UInt64.toNat_add]; simp; omega
    have hszp : j.toNat < pins.size := by rw [hsp.size]; exact hlt'
    have hdrop : pins.toList.drop j.toNat = pins[j.toNat] :: pins.toList.drop (j.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hszp)]; simp
    have hget : pins[j.toNat] = decE (rdW (m.arr64 SPN) (pvo + j)) := by
      have := hsp.get j.toNat hszp
      simpa [spW, toUInt64_toNat_self] using this
    have hpinw : HW (rdW (m.arr64 SPN) (pvo + j)) := by
      have := hsp.lt j.toNat hlt'
      unfold HW; simpa [spW, toUInt64_toNat_self] using this
    rw [hget] at hdrop
    cases hc1 : callW p k "inst_lp" [po, pl, us, rdW (m.arr64 SPN) (pvo + j)] m with
    | none => simp only [ispW, hlt, ↓reduceIte, hc1] at hL; cases hL
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hr₁⟩ := CoreSpec.of_callW
      (hw.instLP k ⟨m, Locals.init []⟩ a dn vis fe M eb po pl us _ lps hS hpinw hus hlps) hc1
    have hSt₁ : StackKept m m₁ := hSt₁
    have hEr1 : m₁.arr64 EREC = m.arr64 EREC := hE k "inst_lp" _ m r₁ m₁ (Or.inl rfl) hc1
    have hlps₁ : hslice? (m₁.arr64 EREC) po.toNat pl.toNat = some lps := by rw [hEr1]; exact hlps
    have htopm : (so.toNat + j.toNat) ≤ (spTop m).toNat := by rw [htop, hsoj]; exact Nat.le_refl _
    have hsa₁ : SpineR m₁ ao rP args := hsa.keep hSt₁.2.1 hSt₁.2.2 (by omega) hspn
    have hat₁ : ao.toNat + rP.toNat ≤ (spTop m₁).toNat := by
      rw [hSt₁.1]; omega
    cases hc2 : callW p k "inst_spine" [ao, rP, rP - 1, r₁.headD 0] m₁ with
    | none => simp only [ispW, hlt, ↓reduceIte, hc1, hc2] at hL; cases hL
    | some q =>
    obtain ⟨r₂, m₂⟩ := q
    have hrP : rP.toNat ≤ (rP - 1).toNat + 1 := by
      by_cases h0 : rP = 0
      · subst h0; simp
      · have : rP.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by simpa using h))
        rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]
        simp; omega
    obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hr₂⟩ := CoreSpec.of_callW
      (instSpine_refines' p hp hc k ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb ao rP (rP - 1) (r₁.headD 0)
        args hS₁ hr₁ hsa₁ hat₁ hrP) hc2
    have hEr2 : m₂.arr64 EREC = m₁.arr64 EREC := hE k "inst_spine" _ m₁ r₂ m₂ (Or.inr rfl) hc2
    have hSt₂ : StackKept m₁ m₂ := hSt₂
    by_cases hgn : ¬ ((so + j).toNat < (m₂.arr64 SPN).size ∧ (136 : Word).toNat < (m₂.arr64 CTL).size)
    · rw [ispW_bad p po pl us ao rP pvo pvc so k m m₁ m₂ j r₁ r₂ hlt hc1 hc2 hgn] at hL; cases hL
    have hg := Classical.not_not.mp hgn
    rw [ispW_cont p po pl us ao rP pvo pvc so k m m₁ m₂ j r₁ r₂ hlt hc1 hc2 hg] at hL
    have hv32 : HW (r₂.headD 0) := hr₂
    have htop₂ : spTop m₂ = so + j := by rw [hSt₂.1, hSt₁.1]; exact htop
    have hsz1 : (m₁.arr64 SPN).size = (m.arr64 SPN).size := hSt₁.2.1
    have hsz2 : (m₂.arr64 SPN).size = (m.arr64 SPN).size := hSt₂.2.1.trans hsz1
    have hjpv : (so + j).toNat + 1 < 2 ^ 64 := by omega
    obtain ⟨hfr, hsp3, hgrew, hslot, hsz3⟩ := push_step m₂ (so + j) (r₂.headD 0) hg.1 hg.2 htop₂ hjpv
    have hS₃ := hS₂.frame_stk hfr (by simp) (by simp)
    have hEr3 : ((m₂.set64 SPN (so + j) (r₂.headD 0)).set64 CTL 136 (so + j + 1)).arr64 EREC =
        m.arr64 EREC := by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide), hEr2, hEr1]
    have hso₂ : so.toNat + pvc.toNat ≤ (m₂.arr64 SPN).size := by rw [hsz2]; exact hso
    have hat₂ : ao.toNat + rP.toNat ≤ (spTop m₂).toNat := by rw [htop₂, hsoj]; omega
    have hpt₂ : pvo.toNat + pvc.toNat ≤ (spTop m₂).toNat := by rw [htop₂, hsoj]; omega
    have hspn₂ : (m₂.arr64 SPN).size < 2 ^ 63 := by rw [hsz2]; exact hS.spn
    have hsa₂ : SpineR m₂ ao rP args := hsa₁.keep hSt₂.2.1 hSt₂.2.2 hat₁ hS₁.spn
    have hsp₁ : SpineR m₁ pvo pvc pins := hsp.keep hSt₁.2.1 hSt₁.2.2 (by omega) hspn
    have hsp₂ : SpineR m₂ pvo pvc pins := hsp₁.keep hSt₂.2.1 hSt₂.2.2 (by rw [hSt₁.1]; omega) hS₁.spn
    have hsa₃ := hsa₂.keep hgrew.2.1 hgrew.2.2 hat₂ hspn₂
    have hsp₃ := hsp₂.keep hgrew.2.1 hgrew.2.2 hpt₂ hspn₂
    have h1 : (j + 1).toNat = j.toNat + 1 := uint64_succ_toNat pvc j hlt
    have hlps₃ : hslice? (((m₂.set64 SPN (so + j) (r₂.headD 0)).set64 CTL 136 (so + j + 1)).arr64 EREC)
        po.toNat pl.toNat = some lps := by rw [hEr3]; exact hlps
    obtain ⟨ys, hok3, ⟨M₄, hS₄, hK₄, hSt₄⟩, hres3, hys⟩ := ih k _ _ M₂ (j + 1) m' (by omega)
      (by omega) hS₃ hlps₃ (by rw [hsp3, UInt64.add_assoc]) (by rw [hsz3]; exact hso₂) hat hpt hsa₃ hsp₃ hL
    -- the twin
    have hSt₄ : StackGrew _ m' := hSt₄
    have hrunT1 := AM.run_of_ok _ _ hok1
    rw [hres1] at hrunT1
    have hI : ∀ q : EIdx, instSpine coreWalkFuel (args.toList.take rP.toNat) (rP.toNat - 1) q =
        instSpine coreWalkFuel args.toList (rP - 1 : Word).toNat q := by
      intro q
      by_cases h0 : rP = 0
      · have : args.toList = [] := by
          have := hsa.size
          rw [h0] at this
          simpa using this
        rw [this]; simp only [List.take_nil, instSpine]
      · have h0' : rP.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by simpa using h))
        have hsub : (rP - 1 : Word).toNat = rP.toNat - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]
          simp
        rw [hsub, List.take_of_length_le (by simp [hsa.size])]
    have hrunT2 := AM.run_of_ok _ _ hok2
    rw [hres2] at hrunT2
    have hrunR := AM.run_of_ok _ _ hok3
    rw [h1] at hrunR hres3
    have hrun := instSpinePins_cons_run lps (decI us) args.toList rP.toNat
      (decE (rdW (m.arr64 SPN) (pvo + j))) (pins.toList.drop (j.toNat + 1)) a _ _ _ _ _ _
      hrunT1 (by rw [hI]; exact hrunT2) hrunR
    rw [hdrop]
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun
    refine ⟨decE (r₂.headD 0) :: ys, hokF, ⟨M₄, ?_, hK₁.trans (hK₂.trans hK₄), ?_⟩, hresF.trans (by rw [hres3]; rfl), ?_⟩
    · rw [hstF]; rw [h1] at hS₄; exact hS₄
    · exact (hSt₁.toGrew.trans (hSt₂.toGrew.trans (hgrew.trans hSt₄)))
    · have e1 : pvc - j = (pvc - (j + 1)) + 1 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega),
          UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega), h1]
        simp; omega
      have e2 : so + (j + 1) = so + j + 1 := by rw [UInt64.add_assoc]
      have hsjp1 : (so + j + 1).toNat = (so + j).toNat + 1 := by
        rw [UInt64.toNat_add]; simp; omega
      rw [e1]
      rw [e2] at hys
      have hsize' : (m'.arr64 SPN).size = (m.arr64 SPN).size := by
        rw [hSt₄.2.1, hsz3, hsz2]
      refine SpineR.cons_slot m' (so + j) (pvc - (j + 1)) (r₂.headD 0) ys hv32 ?_ hys ?_ (by rw [hsize']; exact hS.spn)
      · have := hSt₄.2.2 (so + j) (by
          rw [hsp3, UInt64.lt_iff_toNat_lt, hsjp1]; omega)
        rw [this, hslot]
      · rw [hsize', UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega), hsoj]
        omega

/-- **`inst_spine_pins` refines `instSpinePins`.** Statement changes: `CoreAfterG` (the function leaves
its result slice on the stack: the top grows) in place of `CoreAfter`; both input slices below the
top; and the L code now raises the top after each store (see `instSpinePinsLoop`). -/
theorem instSpinePins_refines' (p : Prog) (hp : IotaProg' p) (hc : IotaCallees p) (hw : WhnfCallees p)
    (hE : ErecKeptInst p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb po pl us ao rP pvo pvc : Word) (lps : List NIdx) (args pins : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW us →
    hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps → SpineR s₀.mem ao rP args →
    SpineR s₀.mem pvo pvc pins → ao.toNat + rP.toNat ≤ (spTop s₀.mem).toNat →
    pvo.toNat + pvc.toNat ≤ (spTop s₀.mem).toNat →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "inst_spine_pins" [po, pl, us, ao, rP, pvo, pvc]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (instSpinePins lps (decI us) args.toList rP.toNat pins.toList) a₀ ∧
      CoreAfterG dn s₀.mem s'.mem
        (AM.st (instSpinePins lps (decI us) args.toList rP.toNat pins.toList) a₀) vis fe MM eb ∧
      ∃ xs, AM.res (instSpinePins lps (decI us) args.toList rP.toNat pins.toList) a₀ = xs ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄ := by
  intro n s₀ a₀ dn vis fe MM eb po pl us ao rP pvo pvc lps args pins hS hus hlps hsa hsp hat hpt
  cases n with
  | zero =>
    apply L.M.triple_of_run
    intro s r s' _ hrun
    exact (invoke_zero_run _ _ _ _ _ _ hrun).elim
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (instSpinePins_spec p hp.instSpinePins n s₀ po pl us ao rP pvo pvc)
  subst hs0
  refine ⟨hloc, ?_⟩
  simp only [ispTop] at hW
  by_cases h136n : ¬ (136 : Word).toNat < (s.mem.arr64 CTL).size
  · rw [if_neg h136n] at hW; cases hW
  have h136 : (136 : Word).toNat < (s.mem.arr64 CTL).size := Classical.not_not.mp h136n
  rw [if_pos h136] at hW
  by_cases hg1 : UInt64.ofNat (s.mem.arr64 SPN).size < rdW (s.mem.arr64 CTL) 136
  · rw [if_pos hg1] at hW; cases hW
  rw [if_neg hg1] at hW
  by_cases hg2 : UInt64.ofNat (s.mem.arr64 SPN).size - rdW (s.mem.arr64 CTL) 136 < pvc
  · rw [if_pos hg2] at hW; cases hW
  rw [if_neg hg2] at hW
  cases hm : ispW p po pl us ao rP pvo pvc (rdW (s.mem.arr64 CTL) 136) (n + 1) s.mem 0 with
  | none => rw [hm] at hW; cases hW
  | some m' =>
  rw [hm] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hmm⟩ := hW
  have hspn := hS.spn
  have h64 : (s.mem.arr64 SPN).size < 2 ^ 64 := by omega
  have hsolt : (rdW (s.mem.arr64 CTL) 136).toNat ≤ (s.mem.arr64 SPN).size := by
    have : ¬ (s.mem.arr64 SPN).size < (rdW (s.mem.arr64 CTL) 136).toNat := by
      intro h
      apply hg1
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' h64]; exact h
    omega
  have hso : (rdW (s.mem.arr64 CTL) 136).toNat + pvc.toNat ≤ (s.mem.arr64 SPN).size := by
    have h2 : ¬ UInt64.ofNat (s.mem.arr64 SPN).size - rdW (s.mem.arr64 CTL) 136 < pvc := hg2
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' h64]; exact hsolt),
      UInt64.toNat_ofNat_of_lt' h64] at h2
    omega
  have hspt : spTop s.mem = rdW (s.mem.arr64 CTL) 136 + 0 := by
    rw [UInt64.add_zero]; rfl
  obtain ⟨ys, hok, hca, hres, hys⟩ := ispW_ok p hp hc hw hE dn vis fe eb po pl us ao rP pvo pvc
    (rdW (s.mem.arr64 CTL) 136) hus lps args pins (pvc.toNat - (0 : Word).toNat) (n + 1) s.mem a₀ MM 0
    m' rfl (by simp) hS hlps hspt hso (by rw [← show (spTop s.mem) = rdW (s.mem.arr64 CTL) 136 from rfl]; exact hat)
    (by rw [← show (spTop s.mem) = rdW (s.mem.arr64 CTL) 136 from rfl]; exact hpt) hsa hsp hm
  have hr1 : r.headD 0 = rdW (s.mem.arr64 CTL) 136 := by
    have := congrArg (fun l => l.headD 0) hr.symm; simpa using this
  have hr2 : r.tail.headD 0 = pvc := by
    have := congrArg (fun l => l.tail.headD 0) hr.symm; simpa using this
  refine ⟨hok, ?_, ys, hres, ?_⟩
  · simpa [← hmm] using hca
  · rw [hr1, hr2, ← hmm]
    simpa using hys

/-! ## `rec_fire_args(fireKind, pvo, pvc, po, pc, us, ao, rP, ctorParams)` -/

/-- Model of `rec_fire_args`. -/
def rfaW (p : Prog) (k : Nat) (m : Mem) (fireKind pvo pvc po pc us ao rP cp : Word) :
    Option (List Word × Mem) :=
  if fireKind = 1 then
    match callW p k "inst_spine_pins" [po, pc, us, ao, rP, pvo, pvc] m with
    | none => none
    | some (r, m₁) => some ([r.headD 0, r.tail.headD 0], m₁)
  else some ([ao, cp], m)

theorem recFireArgs_spec (p : Prog) (hp : p.lookup "rec_fire_args" = some recFireArgsL) (k : Nat)
    (s₀ : St) (fireKind pvo pvc po pc us ao rP cp : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "rec_fire_args" [fireKind, pvo, pvc, po, pc, us, ao, rP, cp]
    ⦃fun r s' => LocEq s' s₀ ∧
      rfaW p k s₀.mem fireKind pvo pvc po pc us ao rP cp = some ([r.headD 0, r.tail.headD 0], s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, recFireArgsL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
    callW_spec p k "inst_spine_pins"] <;>
  simp_all [rfaW, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc,
    St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal,
    Sig.retOr]

/-- A leading part of a spine slice. -/
theorem SpineR.take {m : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (c : Word) (hc : c.toNat ≤ cnt.toNat) :
    SpineR m off c (xs.toList.take c.toNat).toArray := by
  have hb := h.bound
  refine ⟨by simp [h.size]; omega, by omega, fun i hi => h.lt i (by omega), fun i hi => ?_⟩
  have hi' : i < xs.size := by
    simp only [List.size_toArray, List.length_take, Array.length_toList] at hi
    omega
  have := h.get i hi'
  simpa [List.getElem_take] using this

theorem recFireArgs_nested_eq (rl : IRecRule) (lps : List NIdx) (us : LsIdx) (args : List EIdx)
    (rP : Nat) (lv : List LIdx) (pins : List EIdx) (h : rl.fire = .nested lv pins) :
    recFireArgs rl lps us args rP = instSpinePins lps us args rP pins := by
  simp [recFireArgs, h]

theorem recFireArgs_plain_run (rl : IRecRule) (lps : List NIdx) (us : LsIdx) (args : List EIdx)
    (rP : Nat) (h : rl.fire = .plain) (a : AState) :
    (recFireArgs rl lps us args rP).run a = .ok (args.take rl.ctorParams, a) := by
  simp [recFireArgs, h]; rfl

/-- **`rec_fire_args` refines `recFireArgs`.** Statement changes: `CoreAfterG` (the nested arm leaves a
slice on the stack), both input slices below the stack top, and `ctorParams ≤ rP` in the plain arm
(the returned slice is a prefix of the arguments). -/
theorem recFireArgs_refines' (p : Prog) (hp : IotaProg' p) (hc : IotaCallees p) (hw : WhnfCallees p)
    (hE : ErecKeptInst p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb fireKind pvo pvc po pc us ao rP ctorParams : Word) (rl : IRecRule)
    (lps : List NIdx) (args : Array EIdx), CoreS dn s₀.mem a₀ vis fe MM eb → HW us →
    hslice? (s₀.mem.arr64 EREC) po.toNat pc.toNat = some lps → SpineR s₀.mem ao rP args →
    (fireKind = 1 → ∃ lvls pins, rl.fire = .nested lvls pins ∧ SpineR s₀.mem pvo pvc pins.toArray) →
    (fireKind ≠ 1 → rl.fire = .plain ∧ ctorParams.toNat ≤ rP.toNat) → rl.ctorParams = ctorParams.toNat →
    ao.toNat + rP.toNat ≤ (spTop s₀.mem).toNat →
    (fireKind = 1 → pvo.toNat + pvc.toNat ≤ (spTop s₀.mem).toNat) →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rec_fire_args" [fireKind, pvo, pvc, po, pc, us, ao, rP, ctorParams]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (recFireArgs rl lps (decI us) args.toList rP.toNat) a₀ ∧
      CoreAfterG dn s₀.mem s'.mem (AM.st (recFireArgs rl lps (decI us) args.toList rP.toNat) a₀) vis
        fe MM eb ∧
      ∃ xs, AM.res (recFireArgs rl lps (decI us) args.toList rP.toNat) a₀ = xs ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄ := by
  intro n s₀ a₀ dn vis fe MM eb fireKind pvo pvc po pc us ao rP cp rl lps args hS hus hlps hsa hnest
    hplain hcp hat hpt
  cases n with
  | zero =>
    apply L.M.triple_of_run
    intro s r s' _ hrun
    exact (invoke_zero_run _ _ _ _ _ _ hrun).elim
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (recFireArgs_spec p hp.recFireArgs n s₀ fireKind pvo pvc po pc us ao rP cp)
  subst hs0
  refine ⟨hloc, ?_⟩
  simp only [rfaW] at hW
  by_cases h1 : fireKind = 1
  · rw [if_pos h1] at hW
    obtain ⟨lv, pins, hfire, hsp⟩ := hnest h1
    cases hc1 : callW p n "inst_spine_pins" [po, pc, us, ao, rP, pvo, pvc] s.mem with
    | none => rw [hc1] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hc1] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    obtain ⟨t₁, ht₁, hloc1, hok, hca, xs, hres, hxs⟩ := triple_of_callW
      (instSpinePins_refines' p hp hc hw hE n ⟨s.mem, Locals.init []⟩ a₀ dn vis fe MM eb po pc us ao rP
        pvo pvc lps args pins.toArray hS hus hlps hsa hsp hat (hpt h1)) hc1
    rw [recFireArgs_nested_eq rl lps (decI us) args.toList rP.toNat lv pins hfire]
    simp only [List.toList_toArray] at hok hca hres
    simp only [ht₁] at hxs hca
    rw [← hm]
    have hr1 : r.headD 0 = r₁.headD 0 := by
      have := congrArg (fun l => l.headD 0) hr; simpa using this.symm
    have hr2 : r.tail.headD 0 = r₁.tail.headD 0 := by
      have := congrArg (fun l => l.tail.headD 0) hr; simpa using this.symm
    exact ⟨hok, hca, xs, hres, by rw [hr1, hr2]; exact hxs⟩
  · rw [if_neg h1] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    obtain ⟨hfire, hle⟩ := hplain h1
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (recFireArgs_plain_run rl lps (decI us) args.toList
      rP.toNat hfire a₀)
    have hr1 : r.headD 0 = ao := by
      have := congrArg (fun l => l.headD 0) hr.symm; simpa using this
    have hr2 : r.tail.headD 0 = cp := by
      have := congrArg (fun l => l.tail.headD 0) hr.symm; simpa using this
    refine ⟨hok, ?_, _, hres, ?_⟩
    · rw [hst, ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, (StackKept.refl _).toGrew⟩
    · rw [hr1, hr2, ← hm, hcp]
      exact hsa.take cp hle |> fun h => by simpa [hcp] using h

/-! ## `and_rescue_slots(vis, ctor, nP, us)` -/

theorem rdW_eq_getElem (a : Array Word) (x : Word) (h : x.toNat < a.size) : rdW a x = a[x.toNat] := by
  simp [rdW, h]


/-- A checked word read, as `ld64`: `none` out of bounds. -/
def ldE (a : Array Word) (x : Word) : Option Word :=
  if h : x.toNat < a.size then some a[x.toNat] else none

/-- Model of the `and_rescue_slots` loop at L fuel `k`. -/
def arW (p : Prog) (vis ctor nP us an : Word) : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | k + 1, m, j =>
    if j < 2 then
      match callW p k "find_proj" [vis, an, j] m with
      | none => none
      | some (r₁, m₁) =>
        if r₁.headD 0 = 0 then some ([0], m₁)
        else match callW p k "fire_ok" [r₁.tail.headD 0, j, us] m₁ with
          | none => none
          | some (r₂, m₂) =>
            match ldE (m₂.arr64 EREC) (r₁.tail.headD 0 + 6) with
            | none => none
            | some w₆ =>
              if w₆ ≠ ctor then some ([0], m₂)
              else match ldE (m₂.arr64 EREC) (r₁.tail.headD 0 + 5) with
                | none => none
                | some w₅ =>
                  if w₅ ≠ nP then some ([0], m₂)
                  else match ldE (m₂.arr64 EREC) (r₁.tail.headD 0 + 7) with
                    | none => none
                    | some w₇ =>
                      if w₇ ≠ 2 then some ([0], m₂)
                      else if r₂.headD 0 = 0 then some ([0], m₂)
                      else arW p vis ctor nP us an k m₂ (j + 1)
    else some ([1], m)

theorem andRescueLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k andRescueLoop
    ⦃fun r s' => r ≠ .brk ∧
      arW p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) k s₀.mem (s₀.loc 5) =
        some (r.retOr [1], s'.mem); ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := andRescueLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p k "find_proj", callW_spec p k "fire_ok", ih] <;>
      finish (gen := 20) [arW, ldE]

theorem andRescueLoop_step_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p k) andRescueLoop
    ⦃fun r s' => r ≠ .brk ∧
      arW p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (k + 1) s₀.mem (s₀.loc 5) =
        some (r.retOr [1], s'.mem); ⊤⦄ :=
  Triple.step_exec (andRescueLoop_spec p (k + 1) s₀)

/-- Model of `and_rescue_slots`. -/
def arTop (p : Prog) (k : Nat) (m : Mem) (vis ctor nP us : Word) : Option (List Word × Mem) :=
  match callW p k "pin_at" [11] m with
  | none => none
  | some (r₀, m₀) => arW p vis ctor nP us (r₀.headD 0) (k + 1) m₀ 0

theorem andRescueSlots_spec (p : Prog) (hp : p.lookup "and_rescue_slots" = some andRescueSlotsL)
    (k : Nat) (s₀ : St) (vis ctor nP us : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "and_rescue_slots" [vis, ctor, nP, us]
    ⦃fun r s' => LocEq s' s₀ ∧ arTop p k s₀.mem vis ctor nP us = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, andRescueSlotsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p k "pin_at", andRescueLoop_step_spec p k] <;>
    finish [arTop]

theorem andRescueSlotsGo_zero_run (fe : IFEnv) (an ctor : NIdx) (nP : Nat) (ust : LsIdx) (j : Nat)
    (a : AState) : (andRescueSlotsGo fe an ctor nP ust 0 j).run a = .ok (true, a) := by
  simp [andRescueSlotsGo]; rfl

theorem andRescueSlotsGo_none_run (fe : IFEnv) (an ctor : NIdx) (nP : Nat) (ust : LsIdx) (n j : Nat)
    (a a₁ : AState) (h : (fe.findProj? an j).run a = .ok (none, a₁)) :
    (andRescueSlotsGo fe an ctor nP ust (n + 1) j).run a = .ok (false, a₁) := by
  simp only [andRescueSlotsGo, StateT.run_bind, h, except_ok_bind]; rfl

theorem andRescueSlotsGo_stop_run (fe : IFEnv) (an ctor : NIdx) (nP : Nat) (ust : LsIdx) (n j : Nat)
    (a a₁ a₂ : AState) (e : IProjEntry) (b : Bool) (h : (fe.findProj? an j).run a = .ok (some e, a₁))
    (hb : (e.fireOk ust).run a₁ = .ok (b, a₂))
    (hc : (e.ctor == ctor && e.numParams == nP && e.numFields == 2 && b) = false) :
    (andRescueSlotsGo fe an ctor nP ust (n + 1) j).run a = .ok (false, a₂) := by
  simp only [andRescueSlotsGo, StateT.run_bind, h, except_ok_bind, hb, hc]
  rfl

theorem andRescueSlotsGo_cont_run (fe : IFEnv) (an ctor : NIdx) (nP : Nat) (ust : LsIdx) (n j : Nat)
    (a a₁ a₂ a₃ : AState) (e : IProjEntry) (b res : Bool)
    (h : (fe.findProj? an j).run a = .ok (some e, a₁)) (hb : (e.fireOk ust).run a₁ = .ok (b, a₂))
    (hc : (e.ctor == ctor && e.numParams == nP && e.numFields == 2 && b) = true)
    (hr : (andRescueSlotsGo fe an ctor nP ust n (j + 1)).run a₂ = .ok (res, a₃)) :
    (andRescueSlotsGo fe an ctor nP ust (n + 1) j).run a = .ok (res, a₃) := by
  simp only [andRescueSlotsGo, StateT.run_bind, h, except_ok_bind, hb, hc, if_true]
  exact hr

theorem decTbl_bound (a : Array Word) (q : Nat) (tbl : IProjTable) (h : decTbl a q = some tbl) :
    q + 13 < a.size := by
  simp only [decTbl, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, off, hoff, -⟩ := h
  simp only [Option.map_eq_some_iff] at hoff
  obtain ⟨w, hw, -⟩ := hoff
  exact (Array.getElem?_eq_some_iff.mp hw).1

theorem ldE_eq (a : Array Word) (x : Word) (h : x.toNat < a.size) : ldE a x = some (rdW a x) := by
  simp [ldE, rdW, h]

theorem addW13 (q c : Word) (a : Array Word) (hq : q.toNat + 13 < a.size)
    (hsz : a.size < 2 ^ 63) (hc : c.toNat ≤ 13) : (q + c).toNat = q.toNat + c.toNat := by
  rw [UInt64.toNat_add]; simp; omega

/-- **The `and_rescue_slots` loop refines `andRescueSlotsGo`**. -/
theorem arW_ok (p : Prog) (hcc : CoreCallees p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (eb ctor nP us anW : Word) (hctor : HW ctor) (hus : HW us) (hanW : HW anW) :
    ∀ (K k : Nat) (m : Mem) (a : AState) (M : ModeMaps) (j : Word) (L : List Word) (m' : Mem),
      j.toNat + K = 2 → CoreS dn m a vis fe M eb →
      arW p vis ctor nP us anW k m j = some (L, m') →
      AM.ok (andRescueSlotsGo fe (decI anW) (decI ctor) nP.toNat (decI us) K j.toNat) a ∧
      CoreAfter dn m m' (AM.st (andRescueSlotsGo fe (decI anW) (decI ctor) nP.toNat (decI us) K
        j.toNat) a) vis fe M eb ∧
      AM.res (andRescueSlotsGo fe (decI anW) (decI ctor) nP.toNat (decI us) K j.toNat) a = decBool L ∧
      HW (L.headD 0) := by
  intro K
  induction K with
  | zero =>
    intro k m a M j L m' hK hS hL
    have hn : ¬ j < 2 := fun h => by
      have : j.toNat < 2 := h
      omega
    cases k with
    | zero => simp [arW] at hL
    | succ k =>
    simp only [arW, hn, ↓reduceIte] at hL
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _
      (andRescueSlotsGo_zero_run fe (decI anW) (decI ctor) nP.toNat (decI us) j.toNat a)
    refine ⟨hok, ?_, ?_, by simp [HW]⟩
    · rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩
    · rw [hres]; simp [decBool]
  | succ K ih =>
    intro k m a M j L m' hK hS hL
    have hlt : j < 2 := by
      have : j.toNat < 2 := by omega
      exact this
    cases k with
    | zero => simp [arW] at hL
    | succ k =>
    cases hc1 : callW p k "find_proj" [vis, anW, j] m with
    | none => simp only [arW, hlt, ↓reduceIte, hc1] at hL; cases hL
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hr₁⟩ := CoreSpec.of_callW
      (hcc.findProj k ⟨m, Locals.init []⟩ a dn vis fe M eb anW j hS hanW) hc1
    have hres1' : AM.res (fe.findProj? (decI anW) j.toNat) a =
        decEntry (m.arr64 EREC) (r₁.headD 0) (r₁.tail.headD 0) j.toNat := hres1
    have hSt₁ : StackKept m m₁ := hSt₁
    have hrunF := AM.run_of_ok _ _ hok1
    rw [hres1'] at hrunF
    by_cases h0 : r₁.headD 0 = 0
    · simp only [arW, hlt, ↓reduceIte, hc1, h0] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      have hnone : decEntry (m.arr64 EREC) (r₁.headD 0) (r₁.tail.headD 0) j.toNat = none := by
        simp only [decEntry, h0, ↓reduceIte]
      rw [hnone] at hrunF
      obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _
        (andRescueSlotsGo_none_run fe (decI anW) (decI ctor) nP.toNat (decI us) K j.toNat a _ hrunF)
      refine ⟨hokF, ⟨M₁, ?_, hK₁, hSt₁⟩, ?_, by simp [HW]⟩
      · rw [hstF]; exact hS₁
      · rw [hresF]; simp [decBool]
    obtain ⟨tbl, htbl⟩ := hcc.projFound k m a dn vis fe M eb anW j r₁ m₁ hS hc1 h0
    have hEr1 : m₁.arr64 EREC = m.arr64 EREC := hcc.erec k "find_proj" _ m r₁ m₁ (Or.inl rfl) hc1
    have hsome : decEntry (m.arr64 EREC) (r₁.headD 0) (r₁.tail.headD 0) j.toNat =
        some (tbl.entry j.toNat) := by
      simp only [decEntry, if_neg h0, htbl, Option.map_some]
    rw [hsome] at hrunF
    cases hc2 : callW p k "fire_ok" [r₁.tail.headD 0, j, us] m₁ with
    | none => simp only [arW, hlt, ↓reduceIte, hc1, h0, hc2] at hL; cases hL
    | some q =>
    obtain ⟨r₂, m₂⟩ := q
    obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hr₂⟩ := CoreSpec.of_callW
      (hcc.fireOk k ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb (r₁.tail.headD 0) j us tbl hS₁ hus
        (by rw [hEr1]; exact htbl)) hc2
    have hSt₂ : StackKept m₁ m₂ := hSt₂
    have hEr2 : m₂.arr64 EREC = m₁.arr64 EREC := hcc.erec k "fire_ok" _ m₁ r₂ m₂ (Or.inr rfl) hc2
    have hrunB := AM.run_of_ok _ _ hok2
    rw [hres2] at hrunB
    -- the record's words
    have hE2 : m₂.arr64 EREC = m.arr64 EREC := hEr2.trans hEr1
    have hsz := hS.erec
    have hbd := decTbl_bound _ _ _ htbl
    obtain ⟨-, hnp, hw6, hct, hnf⟩ := decTbl_words htbl hsz
    have hx6 : (r₁.tail.headD 0 + 6).toNat < (m₂.arr64 EREC).size := by
      rw [addW13 _ _ _ hbd hsz (by decide), hE2]; simp only [UInt64.toNat_ofNat]; omega
    have hx5 : (r₁.tail.headD 0 + 5).toNat < (m₂.arr64 EREC).size := by
      rw [addW13 _ _ _ hbd hsz (by decide), hE2]; simp only [UInt64.toNat_ofNat]; omega
    have hx7 : (r₁.tail.headD 0 + 7).toNat < (m₂.arr64 EREC).size := by
      rw [addW13 _ _ _ hbd hsz (by decide), hE2]; simp only [UInt64.toNat_ofNat]; omega
    -- the common twin data
    have hW6 : rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 6) = rdW (m.arr64 EREC) (r₁.tail.headD 0 + 6) := by
      rw [hE2]
    have hW5 : rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 5) = rdW (m.arr64 EREC) (r₁.tail.headD 0 + 5) := by
      rw [hE2]
    have hW7 : rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 7) = rdW (m.arr64 EREC) (r₁.tail.headD 0 + 7) := by
      rw [hE2]
    have hfire : (tbl.entry j.toNat).fireOk (decI us) = (tbl.entry j.toNat).fireOk (decI us) := rfl
    have hb : (((tbl.entry j.toNat).fireOk (decI us)).run (AM.st (fe.findProj? (decI anW) j.toNat) a)) =
        .ok (decBool r₂, AM.st ((tbl.entry j.toNat).fireOk (decI us)) (AM.st (fe.findProj? (decI anW) j.toNat) a)) :=
      hrunB
    have hb' := hb
    have hfin : ((tbl.entry j.toNat).ctor == decI ctor && (tbl.entry j.toNat).numParams == nP.toNat &&
          (tbl.entry j.toNat).numFields == 2 && decBool r₂) = false → L = [0] → m' = m₂ →
        AM.ok (andRescueSlotsGo fe (decI anW) (decI ctor) nP.toNat (decI us) (K + 1) j.toNat) a ∧
        CoreAfter dn m m' (AM.st (andRescueSlotsGo fe (decI anW) (decI ctor) nP.toNat (decI us) (K + 1)
          j.toNat) a) vis fe M eb ∧
        AM.res (andRescueSlotsGo fe (decI anW) (decI ctor) nP.toNat (decI us) (K + 1) j.toNat) a =
          decBool L ∧ HW (L.headD 0) := by
      intro hcf hLe hme
      subst hLe; subst hme
      obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _
        (andRescueSlotsGo_stop_run fe (decI anW) (decI ctor) nP.toNat (decI us) K j.toNat a _ _
          (tbl.entry j.toNat) (decBool r₂) hrunF hb' hcf)
      refine ⟨hokF, ⟨M₂, ?_, hK₁.trans hK₂, hSt₁.trans hSt₂⟩, ?_, by simp [HW]⟩
      · rw [hstF]; exact hS₂
      · rw [hresF]; simp [decBool]
    have hL' := hL
    simp only [arW, hlt, ↓reduceIte, hc1, h0, hc2] at hL'
    rw [ldE_eq _ _ hx6] at hL'
    dsimp only at hL'
    by_cases hc6 : rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 6) = ctor
    · rw [if_neg (by simpa using hc6)] at hL'
      rw [ldE_eq _ _ hx5] at hL'
      dsimp only at hL'
      by_cases hc5 : rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 5) = nP
      · rw [if_neg (by simpa using hc5)] at hL'
        rw [ldE_eq _ _ hx7] at hL'
        dsimp only at hL'
        by_cases hc7 : rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 7) = 2
        · rw [if_neg (by simpa using hc7)] at hL'
          by_cases hr20 : r₂.headD 0 = 0
          · rw [if_pos hr20] at hL'
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL')
            refine hfin ?_ rfl rfl
            have hb0 : decBool r₂ = false := by simp only [decBool]; rw [hr20]; rfl
            rw [hb0]; simp
          · rw [if_neg hr20] at hL'
            have h1 : (j + 1).toNat = j.toNat + 1 := uint64_succ_toNat 2 j hlt
            obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hL1⟩ := ih k m₂ _ M₂ (j + 1) L m'
              (by omega) hS₂ hL'
            rw [h1] at hok3 hS₃ hres3
            have hrunR := AM.run_of_ok _ _ hok3
            have hcond : ((tbl.entry j.toNat).ctor == decI ctor && (tbl.entry j.toNat).numParams == nP.toNat &&
                (tbl.entry j.toNat).numFields == 2 && decBool r₂) = true := by
              have hh6 : HW (rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 6)) := by rw [hW6]; exact hw6
              have e1 : ((tbl.entry j.toNat).ctor == decI ctor) = true := by
                show (tbl.ctor == decI ctor) = true
                rw [hct, ← hW6, decI_beq _ _ hh6 hctor]
                exact decide_eq_true hc6
              have e2 : ((tbl.entry j.toNat).numParams == nP.toNat) = true := by
                show (tbl.numParams == nP.toNat) = true
                rw [hnp, ← hW5, hc5]; simp
              have e3 : ((tbl.entry j.toNat).numFields == 2) = true := by
                show (tbl.numFields == 2) = true
                rw [hnf, ← hW7, hc7]; rfl
              have e4 : decBool r₂ = true := by simp only [decBool]; simpa using hr20
              rw [e1, e2, e3, e4]; rfl
            obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _
              (andRescueSlotsGo_cont_run fe (decI anW) (decI ctor) nP.toNat (decI us) K j.toNat a _ _ _
                (tbl.entry j.toNat) (decBool r₂) _ hrunF hb' hcond hrunR)
            refine ⟨hokF, ⟨M₃, ?_, hK₁.trans (hK₂.trans hK₃), hSt₁.trans (hSt₂.trans hSt₃)⟩, ?_, hL1⟩
            · rw [hstF]; exact hS₃
            · rw [hresF]; exact hres3
        · rw [if_pos (by simpa using hc7)] at hL'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL')
          refine hfin ?_ rfl rfl
          have : (tbl.entry j.toNat).numFields ≠ 2 := by
            show tbl.numFields ≠ 2
            rw [hnf, ← hW7]
            intro h; apply hc7; exact UInt64.toNat_inj.mp (by simpa using h)
          simp [this]
      · rw [if_pos (by simpa using hc5)] at hL'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL')
        refine hfin ?_ rfl rfl
        have : (tbl.entry j.toNat).numParams ≠ nP.toNat := by
          show tbl.numParams ≠ nP.toNat
          rw [hnp, ← hW5]
          intro h; apply hc5; exact UInt64.toNat_inj.mp h
        simp [this]
    · rw [if_pos (by simpa using hc6)] at hL'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL')
      refine hfin ?_ rfl rfl
      have hh6 : HW (rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 6)) := by rw [hW6]; exact hw6
      have : ((tbl.entry j.toNat).ctor == decI ctor) = false := by
        show (tbl.ctor == decI ctor) = false
        rw [hct, ← hW6, decI_beq _ _ hh6 hctor]
        exact decide_eq_false hc6
      simp [this]

theorem andRescueSlots_run (fe : IFEnv) (ctor : NIdx) (nP : Nat) (ust : LsIdx) (an : NIdx)
    (a a₁ : AState) (b : Bool) (hp : (pinAt PIN_AND).run a = .ok (an, a))
    (hr : (andRescueSlotsGo fe an ctor nP ust 2 0).run a = .ok (b, a₁)) :
    (andRescueSlots fe ctor nP ust).run a = .ok (b, a₁) := by
  simp only [andRescueSlots, pinAnd, StateT.run_bind, hp, except_ok_bind, hr]

/-- **`and_rescue_slots` refines `andRescueSlots`** (`find_proj`, `fire_ok` and their facts as
`CoreCallees`). -/
theorem andRescueSlots_refines' (p : Prog) (hp : IotaProg' p) (hcc : CoreCallees p) :
    AndRescueSlotsOK p := by
  intro n s₀ a₀ dn vis fe MM eb ctor nP us hS hctor hus
  cases n with
  | zero =>
    apply L.M.triple_of_run
    intro s r s' _ hrun
    exact (invoke_zero_run _ _ _ _ _ _ hrun).elim
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (andRescueSlots_spec p hp.andRescueSlots n s₀ vis ctor nP us)
  subst hs0
  refine ⟨hloc, ?_⟩
  simp only [arTop] at hW
  cases hc0 : callW p n "pin_at" [11] s.mem with
  | none => rw [hc0] at hW; cases hW
  | some q =>
  obtain ⟨r₀, m₀⟩ := q
  rw [hc0] at hW
  simp only at hW
  obtain ⟨t₀, ht₀, hm₀, hloc0, hanHW, hpin⟩ := triple_of_callW
    (pinAt_refines p hp.pinat n ⟨s.mem, Locals.init []⟩ a₀ ⟨fun _ => hS.pins⟩ 11) hc0
  have hmm : m₀ = s.mem := by rw [← ht₀]; exact hm₀
  subst hmm
  have hanW : HW (r₀.headD 0) := hanHW
  obtain ⟨hok, hca, hres, hL1⟩ := arW_ok p hcc dn vis fe eb ctor nP us (r₀.headD 0) hctor hus hanW 2
    (n + 1) s.mem a₀ MM 0 r s'.mem (by simp) hS hW
  have hrunA := andRescueSlots_run fe (decI ctor) nP.toNat (decI us) (decI (r₀.headD 0)) a₀ _ _
    (by simpa [PIN_AND] using hpin) (AM.run_of_ok _ _ hok)
  obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrunA
  refine ⟨hokF, ?_, ?_, hL1⟩
  · rw [hstF]; simpa using hca
  · rw [hresF]; simpa using hres

/-! ## `fab_scope_ok(d, fab, major)` -/

/-- Model of `fab_scope_ok`. -/
def fsW (p : Prog) (k : Nat) (m : Mem) (d fab major : Word) : Option (List Word × Mem) :=
  match callW p k "wscoped_bfast" [d, fab] m with
  | none => none
  | some (r₁, m₁) =>
    if r₁.headD 0 = 0 then some ([0], m₁)
    else match callW p k "loose_bvars_bounded_fast" [0, fab] m₁ with
      | none => none
      | some (r₂, m₂) =>
        if r₂.headD 0 = 0 then some ([0], m₂)
        else match callW p k "leaf_guard" [fab, major] m₂ with
          | none => none
          | some (r₃, m₃) => some ([r₃.headD 0], m₃)

theorem fabScopeOk_spec (p : Prog) (hp : p.lookup "fab_scope_ok" = some fabScopeOkL) (k : Nat)
    (s₀ : St) (d fab major : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "fab_scope_ok" [d, fab, major]
    ⦃fun r s' => LocEq s' s₀ ∧ fsW p k s₀.mem d fab major = some ([r.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, fabScopeOkL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
    callW_spec p k "wscoped_bfast", callW_spec p k "loose_bvars_bounded_fast",
    callW_spec p k "leaf_guard"] <;>
  simp_all [fsW, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]

theorem fabScopeOk_stop1 (d : Nat) (fab major : EIdx) (a a₁ : AState)
    (h : (wscopedBFast coreWalkFuel d fab).run a = .ok (false, a₁)) :
    (fabScopeOk d fab major).run a = .ok (false, a₁) := by
  simp only [fabScopeOk, StateT.run_bind, h, except_ok_bind]; rfl

theorem fabScopeOk_stop2 (d : Nat) (fab major : EIdx) (a a₁ a₂ : AState)
    (h : (wscopedBFast coreWalkFuel d fab).run a = .ok (true, a₁))
    (h2 : (looseBVarsBoundedFast coreWalkFuel 0 fab).run a₁ = .ok (false, a₂)) :
    (fabScopeOk d fab major).run a = .ok (false, a₂) := by
  simp only [fabScopeOk, StateT.run_bind, h, except_ok_bind, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, h2, Bool.not_false]; rfl

theorem fabScopeOk_go (d : Nat) (fab major : EIdx) (a a₁ a₂ a₃ : AState) (b : Bool)
    (h : (wscopedBFast coreWalkFuel d fab).run a = .ok (true, a₁))
    (h2 : (looseBVarsBoundedFast coreWalkFuel 0 fab).run a₁ = .ok (true, a₂))
    (h3 : (leafGuard coreWalkFuel fab major).run a₂ = .ok (b, a₃)) :
    (fabScopeOk d fab major).run a = .ok (b, a₃) := by
  simp only [fabScopeOk, StateT.run_bind, h, except_ok_bind, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, h2, Bool.not_false, h3]

/-- **`fab_scope_ok` refines `fabScopeOk`** (the three walks as `IotaCallees`' stubs). -/
theorem fabScopeOk_refines' (p : Prog) (hp : IotaProg' p) (hc : IotaCallees p) : FabScopeOkOK p := by
  intro n s₀ a₀ dn vis fe MM eb d fab major hS hfab hmaj
  cases n with
  | zero =>
    apply L.M.triple_of_run
    intro s r s' _ hrun
    exact (invoke_zero_run _ _ _ _ _ _ hrun).elim
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (fabScopeOk_spec p hp.fabScopeOk n s₀ d fab major)
  subst hs0
  refine ⟨hloc, ?_⟩
  simp only [fsW] at hW
  cases hc1 : callW p n "wscoped_bfast" [d, fab] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  simp only at hW
  obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hr₁⟩ := CoreSpec.of_callW
    (hc.wscopedBFast n ⟨s.mem, Locals.init []⟩ a₀ dn vis fe MM eb d fab hS hfab) hc1
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  by_cases h0 : r₁.headD 0 = 0
  · rw [if_pos h0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hb : decBool r₁ = false := by simp only [decBool]; rw [h0]; rfl
    rw [hb] at hrun1
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _
      (fabScopeOk_stop1 d.toNat (decE fab) (decE major) a₀ _ hrun1)
    have hr0 : r.headD 0 = 0 := by simpa using hr.symm
    refine ⟨hokF, ⟨M₁, ?_, hK₁, hm ▸ hSt₁⟩, ?_, ?_⟩
    · rw [hstF, ← hm]; exact hS₁
    · rw [hresF]; simp only [decBool]; rw [hr0]; rfl
    · unfold ResH HW; rw [hr0]; decide
  rw [if_neg h0] at hW
  have hb : decBool r₁ = true := by simp only [decBool]; simpa using h0
  rw [hb] at hrun1
  cases hc2 : callW p n "loose_bvars_bounded_fast" [0, fab] m₁ with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW
  simp only at hW
  obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hr₂⟩ := CoreSpec.of_callW
    (hc.looseBVarsBoundedFast n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb 0 fab hS₁ hfab) hc2
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun2
  have h00 : (0 : Word).toNat = 0 := rfl
  rw [h00] at hrun2
  by_cases h20 : r₂.headD 0 = 0
  · rw [if_pos h20] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hb2 : decBool r₂ = false := by simp only [decBool]; rw [h20]; rfl
    rw [hb2] at hrun2
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _
      (fabScopeOk_stop2 d.toNat (decE fab) (decE major) a₀ _ _ hrun1 hrun2)
    have hr0 : r.headD 0 = 0 := by simpa using hr.symm
    refine ⟨hokF, ⟨M₂, ?_, hK₁.trans hK₂, hm ▸ hSt₁.trans hSt₂⟩, ?_, ?_⟩
    · rw [hstF, ← hm]; exact hS₂
    · rw [hresF]; simp only [decBool]; rw [hr0]; rfl
    · unfold ResH HW; rw [hr0]; decide
  rw [if_neg h20] at hW
  have hb2 : decBool r₂ = true := by simp only [decBool]; simpa using h20
  rw [hb2] at hrun2
  cases hc3 : callW p n "leaf_guard" [fab, major] m₂ with
  | none => rw [hc3] at hW; cases hW
  | some q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [hc3] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hr₃⟩ := CoreSpec.of_callW
    (hc.leafGuard n ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb fab major hS₂ hfab hmaj) hc3
  have hrun3 := AM.run_of_ok _ _ hok3
  obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _
    (fabScopeOk_go d.toNat (decE fab) (decE major) a₀ _ _ _ _ hrun1 hrun2 hrun3)
  have hr3 : r₃.headD 0 = r.headD 0 := by simpa using hr
  refine ⟨hokF, ⟨M₃, ?_, hK₁.trans (hK₂.trans hK₃), hm ▸ hSt₁.trans (hSt₂.trans hSt₃)⟩, ?_, ?_⟩
  · rw [hstF, ← hm]; exact hS₃
  · rw [hresF, hres3]; simp only [decBool]; rw [hr3]
  · unfold ResH HW; rw [← hr3]; exact hr₃

/-! ## `lit_major_to_ctor(mode, vis, d, h)` -/

/-- Model of `lit_major_to_ctor`. -/
def lmW (p : Prog) (k : Nat) (m : Mem) (mode vis d h : Word) : Option (List Word × Mem) :=
  if h >>> 28 ≠ 8 then
    match callW p k "lit_to_ctor_if_nat" [vis, h] m with
    | none => none
    | some (r, m₁) => some ([r.headD 0], m₁)
  else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h then none
  else match ldE (m.arr64 REC) (idxW h * 8 + tierW h * 4) with
    | none => none
    | some kind =>
      if kind ≠ 1 then
        match callW p k "lit_to_ctor_if_nat" [vis, h] m with
        | none => none
        | some (r, m₁) => some ([r.headD 0], m₁)
      else match callW p k "str_lit_supported" [vis] m with
        | none => none
        | some (r₁, m₁) =>
          if r₁.headD 0 = 0 then some ([h], m₁)
          else match callW p k "str_lit_ctor" [h] m₁ with
            | none => none
            | some (r₂, m₂) =>
              match callW p k "whnf" [mode, vis, d, r₂.headD 0] m₂ with
              | none => none
              | some (r₃, m₃) => some ([r₃.headD 0], m₃)

theorem litMajorToCtor_spec (p : Prog) (hp : p.lookup "lit_major_to_ctor" = some litMajorToCtorL)
    (k : Nat) (s₀ : St) (mode vis d h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "lit_major_to_ctor" [mode, vis, d, h]
    ⦃fun r s' => LocEq s' s₀ ∧ lmW p k s₀.mem mode vis d h = some ([r.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, litMajorToCtorL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p k "lit_to_ctor_if_nat", callW_spec p k "str_lit_supported",
      callW_spec p k "str_lit_ctor", callW_spec p k "whnf"] <;>
    finish (gen := 20) [lmW, ldE, tierW, idxW]

theorem viewLit_ok' (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h 2) (hg : h >>> 28 = 8) :
    ∃ l, a.store.viewLit (decE h) = some l ∧ a.store.view (decE h) = some (.lit l) ∧
      RecRel m (tierW h) (idxW h) ⟨l⟩ := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h litSch RecRel litH (·.lits) _ hR.lit.2 hv.2
  refine ⟨k.l, ?_, ?_, hkr⟩
  · simp only [EStore.viewLit, EStore.persGetLit]
    rw [proj_tier m a hR h hh (fun t i => t.getLit i) hv.1]
    simp only [ETables.getLit, Tbl.node?, decE_idx]
    rw [hk]; rfl
  · rw [view_tier m a hR h hh hv.1, get_lit _ h hh hg, Tbl.node?, hk]; rfl

theorem litMajorToCtor_run_nolit (r : CoreFnsA) (fe : IFEnv) (d : Nat) (h : EIdx) (a : AState)
    (ht : h.tag ≠ ETag.lit) : (litMajorToCtor r fe d h).run a = (litToCtorIfNat fe h).run a := by
  simp [litMajorToCtor, ht]

theorem litMajorToCtor_run_nat (r : CoreFnsA) (fe : IFEnv) (d : Nat) (h : EIdx) (a : AState)
    (ht : h.tag = ETag.lit) (n : Nat) (hv : a.store.view h = some (.lit (.natVal n))) :
    (litMajorToCtor r fe d h).run a = (litToCtorIfNat fe h).run a := by
  have hv' : (view h).run a = .ok (.lit (.natVal n), a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  simp only [litMajorToCtor, ht, beq_self_eq_true, ↓reduceIte, StateT.run_bind, hv', except_ok_bind]

theorem litMajorToCtor_run_str_unsup (r : CoreFnsA) (fe : IFEnv) (d : Nat) (h : EIdx) (a a₁ : AState)
    (ht : h.tag = ETag.lit) (s : String) (hv : a.store.view h = some (.lit (.strVal s)))
    (hs : (strLitSupported fe).run a = .ok (false, a₁)) :
    (litMajorToCtor r fe d h).run a = .ok (h, a₁) := by
  have hv' : (view h).run a = .ok (.lit (.strVal s), a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  simp only [litMajorToCtor, ht, beq_self_eq_true, ↓reduceIte, StateT.run_bind, hv', except_ok_bind,
    hs]; rfl

theorem litMajorToCtor_run_str (r : CoreFnsA) (fe : IFEnv) (d : Nat) (h : EIdx) (a a₁ a₂ a₃ : AState)
    (ht : h.tag = ETag.lit) (s : String) (hv : a.store.view h = some (.lit (.strVal s)))
    (hs : (strLitSupported fe).run a = .ok (true, a₁)) (c res : EIdx)
    (hc : (strLitToConstructor s).run a₁ = .ok (c, a₂)) (hw : (r.whnf d c).run a₂ = .ok (res, a₃)) :
    (litMajorToCtor r fe d h).run a = .ok (res, a₃) := by
  have hv' : (view h).run a = .ok (.lit (.strVal s), a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  simp only [litMajorToCtor, ht, beq_self_eq_true, ↓reduceIte, StateT.run_bind, hv', except_ok_bind,
    hs, hc, hw]

theorem ldE_some (a : Array Word) (x w : Word) (h : ldE a x = some w) :
    x.toNat < a.size ∧ w = rdW a x := by
  unfold ldE at h
  split at h
  · rename_i hb
    simp only [Option.some.injEq] at h
    exact ⟨hb, by rw [← h, rdW_eq_getElem a x hb]⟩
  · cases h

/-- A refinement transports along twins with the same run. -/
theorem CoreRef.of_run_eq {α : Type} [Inhabited α] {T T' : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} (hT : T'.run a₀ = T.run a₀)
    (h : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok) : CoreRef T' a₀ dec dn m₀ vis fe M eb r m ok := by
  simp only [CoreRef, AM.ok, AM.st, AM.res, hT] at h ⊢
  exact h

/-- **`lit_major_to_ctor` refines `litMajorToCtor`.** Statement changes (the knot's `whnf` slot needs
them): `n ≤ 2 ^ 62`, the eager bit `eb = (mode >>> 1) &&& 1`; and `SupKeep` (`strLitSupported` keeps the
store's views: `WhnfBase.supKeep_twin`, a `sorry`) as a hypothesis. -/
theorem litMajorToCtor_refines' (p : Prog) (hp : IotaProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 →
    eb = (mode >>> 1) &&& 1 → HW h →
    CoreSpec p (n + 1) "lit_major_to_ctor" [mode, vis, d, h]
      (litMajorToCtor (coreKnot (decMode mode) fe id F) fe d.toNat (decE h)) decH s₀ a₀ dn vis fe MM
      eb := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d h hS hm4 hebm hh
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (litMajorToCtor_spec p hp.litMajorToCtor n s₀ mode vis d h)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hR := hS.arena.1
  simp only [lmW] at hW
  by_cases h8 : h >>> 28 = 8
  · rw [if_neg (by simpa using h8)] at hW
    by_cases hv1 : tierW h ≠ 0 ∧ rdW (s.mem.arr64 CTL) 1 = 0
    · rw [if_pos hv1] at hW; cases hW
    rw [if_neg hv1] at hW
    by_cases hv2 : rdW (s.mem.arr64 CTL) (2 + tierW h) ≤ idxW h
    · rw [if_pos hv2] at hW; cases hW
    rw [if_neg hv2] at hW
    obtain ⟨l, hl, hview, hrel⟩ := viewLit_ok' s.mem a₀ hR h hh ⟨hv1, UInt64.not_le.mp hv2⟩ h8
    have htag : (decE h).tag = ETag.lit := (decE_tag_lit h hh).mpr h8
    cases hld : ldE (s.mem.arr64 REC) (idxW h * 8 + tierW h * 4) with
    | none => rw [hld] at hW; cases hW
    | some kind =>
    rw [hld] at hW
    obtain ⟨-, hkind⟩ := ldE_some _ _ _ hld
    dsimp only at hW
    cases l with
    | natVal N =>
      have hk0 : kind = 0 := by rw [hkind]; exact hrel.1
      rw [if_pos (by rw [hk0]; decide)] at hW
      cases hc1 : callW p n "lit_to_ctor_if_nat" [vis, h] s.mem with
      | none => rw [hc1] at hW; cases hW
      | some q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [hc1] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr, hm⟩ := hW
      have hr1 : r.headD 0 = r₁.headD 0 := by simpa using hr.symm
      have hcr := CoreRef.of_run_eq (T' := litMajorToCtor (coreKnot (decMode mode) fe id F) fe d.toNat (decE h))
        (litMajorToCtor_run_nat _ fe d.toNat (decE h) a₀ htag N hview)
        (CoreSpec.of_callW (hc.litToCtorIfNat n ⟨s.mem, Locals.init []⟩ a₀ dn vis fe MM eb h hS hh) hc1)
      obtain ⟨hok, hca, hres, hr₁⟩ := hcr
      refine ⟨hok, ?_, ?_, ?_⟩
      · rw [← hm]; exact hca
      · rw [hres]; simp only [decH]; rw [hr1]
      · unfold ResH HW at hr₁ ⊢; rw [hr1]; exact hr₁
    | strVal str =>
      have hk1 : kind = 1 := by rw [hkind]; exact hrel.1
      rw [if_neg (by rw [hk1]; decide)] at hW
      cases hc1 : callW p n "str_lit_supported" [vis] s.mem with
      | none => rw [hc1] at hW; cases hW
      | some q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [hc1] at hW
      simp only at hW
      obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hr₁⟩ := CoreSpec.of_callW
        (hw.strLitSupported n ⟨s.mem, Locals.init []⟩ a₀ dn vis fe MM eb hS) hc1
      have hrun1 := AM.run_of_ok _ _ hok1
      rw [hres1] at hrun1
      by_cases h0 : r₁.headD 0 = 0
      · rw [if_pos h0] at hW
        simp only [Option.some.injEq, Prod.mk.injEq] at hW
        obtain ⟨hr, hm⟩ := hW
        have hb : decBool r₁ = false := by simp only [decBool]; rw [h0]; rfl
        rw [hb] at hrun1
        obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _
          (litMajorToCtor_run_str_unsup (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) a₀ _ htag
            str hview hrun1)
        have hr1 : r.headD 0 = h := by simpa using hr.symm
        refine ⟨hokF, ⟨M₁, ?_, hK₁, hm ▸ hSt₁⟩, ?_, ?_⟩
        · rw [hstF, ← hm]; exact hS₁
        · rw [hresF]; simp only [decH]; rw [hr1]
        · unfold ResH HW; rw [hr1]; exact hh
      · rw [if_neg h0] at hW
        have hb : decBool r₁ = true := by simp only [decBool]; simpa using h0
        rw [hb] at hrun1
        cases hc2 : callW p n "str_lit_ctor" [h] m₁ with
        | none => rw [hc2] at hW; cases hW
        | some q =>
        obtain ⟨r₂, m₂⟩ := q
        rw [hc2] at hW
        simp only at hW
        have hviewA : (AM.st (strLitSupported fe) a₀).store.view (decE h) = some (.lit (.strVal str)) :=
          hsup fe a₀ (decE h) _ hview
        obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hr₂⟩ := CoreSpec.of_callW
          (hw.strLitCtor n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb h str hS₁ hh hviewA) hc2
        have hrun2 := AM.run_of_ok _ _ hok2
        rw [hres2] at hrun2
        cases hc3 : callW p n "whnf" [mode, vis, d, r₂.headD 0] m₂ with
        | none => rw [hc3] at hW; cases hW
        | some q =>
        obtain ⟨r₃, m₃⟩ := q
        rw [hc3] at hW
        simp only [Option.some.injEq, Prod.mk.injEq] at hW
        obtain ⟨hr, hm⟩ := hW
        obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hr₃⟩ := CoreSpec.of_callW
          ((hk n (Nat.le_refl _)).whnf F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d _ hnF hn62
            ⟨hS₂, hm4, hebm⟩ hr₂) hc3
        have hrun3 := AM.run_of_ok _ _ hok3
        obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _
          (litMajorToCtor_run_str (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) a₀ _ _ _ htag
            str hview hrun1 _ _ hrun2 hrun3)
        have hr1 : r₃.headD 0 = r.headD 0 := by simpa using hr
        refine ⟨hokF, ⟨M₃, ?_, hK₁.trans (hK₂.trans hK₃), hm ▸ hSt₁.trans (hSt₂.trans hSt₃)⟩, ?_, ?_⟩
        · rw [hstF, ← hm]; exact hS₃
        · rw [hresF]; simp only [decH]; rw [← hr1]; exact hres3
        · unfold ResH HW; rw [← hr1]; exact hr₃
  · rw [if_pos h8] at hW
    cases hc1 : callW p n "lit_to_ctor_if_nat" [vis, h] s.mem with
    | none => rw [hc1] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hc1] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hr1 : r.headD 0 = r₁.headD 0 := by simpa using hr.symm
    have hcr := CoreRef.of_run_eq (T' := litMajorToCtor (coreKnot (decMode mode) fe id F) fe d.toNat (decE h))
      (litMajorToCtor_run_nolit _ fe d.toNat (decE h) a₀ (fun ht => h8 ((decE_tag_lit h hh).mp ht)))
      (CoreSpec.of_callW (hc.litToCtorIfNat n ⟨s.mem, Locals.init []⟩ a₀ dn vis fe MM eb h hS hh) hc1)
    obtain ⟨hok, hca, hres, hr₁⟩ := hcr
    refine ⟨hok, ?_, ?_, ?_⟩
    · rw [← hm]; exact hca
    · rw [hres]; simp only [decH]; rw [hr1]
    · unfold ResH HW at hr₁ ⊢; rw [hr1]; exact hr₁

/-! ## `mk_proj` as a run under `CoreS` -/

theorem pjinternW_hw (m : Mem) (a : AState) (hR : ProjR m a) (n u e : Word) (w : Word) (m' : Mem)
    (hI : pjinternW m n u e = some (w, m')) : w.toNat < 2 ^ 32 := by
  rw [pjinternW_eq] at hI
  exact internM_hw projSch PJRecRel pjhash projSch_wf m _ _ _ hR (pjMt m n u e) _ _ _ _
    (probe_homeG projSch m 0 _ _ (pjprobeW_arm m n u e 0) _)
    (probe_homeG projSch m 1 _ _ (pjprobeW_arm m n u e 1) _) _ (pjpushOK_room m) _ _ w m' hI

theorem mkProjW_hw (m : Mem) (a : AState) (hA : ArenaD m a) (n i e r : Word) (m' : Mem)
    (hI : mkProjW m n i e = some (r, m')) : r.toNat < 2 ^ 32 := by
  unfold mkProjW at hI
  split at hI
  · cases hI
  cases hI₁ : pjinternW m n i e with
  | none => simp [hI₁, mkK] at hI
  | some p =>
  obtain ⟨r₁, m₁⟩ := p
  simp only [hI₁, mkK_some] at hI
  cases hP : derPutW PJDER 32 m₁ (cnt2 m 32) r₁ (packBF (derBW m e) (derFW m e)) with
  | none => simp [hP] at hI
  | some m₂ =>
  simp only [hP, Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  exact pjinternW_hw m a hA.1.proj n i e _ m₁ hI₁

theorem keeps_cpl_internProj (n : NIdx) (i : Nat) (e : EIdx) :
    Keeps cpl (internE (.proj n i e)) := by
  simp only [internE]; exact keeps_cpl_internNodeE _

/-- **`mk_proj` as a run.** -/
theorem callW_mkProj (p : Prog) (hp : IotaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (hD : ArenaD s₀.mem a₀) (nm i e : Word) (r : List Word) (m' : Mem)
    (h : callW p n "mk_proj" [nm, i, e] s₀.mem = some (r, m')) :
    AM.ok (internE (.proj (decI nm) i.toNat (decE e))) a₀ ∧
    ArenaD m' (AM.st (internE (.proj (decI nm) i.toNat (decE e))) a₀) ∧
    AM.res (internE (.proj (decI nm) i.toNat (decE e))) a₀ = decE (r.headD 0) ∧
    MemFrame L.Rom.StoreA L.Rom.StoreC s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, hm⟩ := triple_of_callW (mkProj_spec p hp.spine.derb hp.projf hp.projp hp.proji
    hp.mkproj n s₀ nm i e) h
  obtain ⟨-, hm⟩ := hm
  obtain ⟨h1, h2, h3⟩ := mkProj_ok s₀.mem a₀ hD nm i e _ _ hm
  exact ⟨h1, h2, h3, L.Rom.mkProjW_store hm, mkProjW_hw _ a₀ hD nm i e _ _ hm⟩

/-- **`CoreS` across a `proj` interning step.** -/
theorem CoreS.of_proj {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (hD : ArenaD m' a')
    (hcpl : cpl a' = cpl a) (hf : MemFrame L.Rom.StoreA L.Rom.StoreC m m') :
    CoreS dn m' a' vis fe M eb :=
  hS.arena_frame hD hcpl hf
    (fun b hb => by
      have : b < 64 := by unfold L.Rom.StoreA at hb; exact List.mem_range.mp hb
      exact Or.inl (Nat.lt_of_lt_of_le this (by decide)))
    (by unfold L.Rom.StoreA; simp [PINS])
    (fun b hb => by
      have : b < 64 := by unfold L.Rom.StoreA at hb; exact List.mem_range.mp hb
      exact Or.inl (Nat.lt_of_lt_of_le this (by decide)))
    (fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (show x ∈ (List.range 64).map UInt64.ofNat by unfold L.Rom.StoreC at hx; exact hx)
      have := List.mem_range.mp hk
      left; simp [UInt64.toNat_ofNat]; omega)
    (fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (show x ∈ (List.range 64).map UInt64.ofNat by unfold L.Rom.StoreC at hx; exact hx)
      have := List.mem_range.mp hk
      left; simp [UInt64.toNat_ofNat]; omega)

theorem StackKept.of_store {m m' : Mem} (hf : MemFrame L.Rom.StoreA L.Rom.StoreC m m') : StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (fun h => by have : SPN < 64 := by unfold L.Rom.StoreA at h; exact List.mem_range.mp h
                          simp [SPN] at this) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 :=
    hf.2.1 136 (fun h => by
      obtain ⟨k, hk, hkk⟩ := List.mem_map.mp (show (136 : Word) ∈ (List.range 64).map UInt64.ofNat by unfold L.Rom.StoreC at h; exact h)
      have := List.mem_range.mp hk
      have h' := congrArg UInt64.toNat hkk
      simp [UInt64.toNat_ofNat] at h'; omega)
  exact ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩

/-! ## `eta_projs(T, b, nF)` -/

/-- Model of the `eta_projs` loop at L fuel `k`: the memory after the stores. -/
def etpW (p : Prog) (T b nF o : Word) : Nat → Mem → Word → Option Mem
  | 0, _, _ => none
  | k + 1, m, j =>
    if j < nF then
      match callW p k "mk_proj" [T, j, b] m with
      | none => none
      | some (r, m₁) =>
        if (o + j).toNat < (m₁.arr64 SPN).size then
          etpW p T b nF o k (m₁.set64 SPN (o + j) (r.headD 0)) (j + 1)
        else none
    else some m

theorem etpW_end (p : Prog) (T b nF o : Word) (k : Nat) (m : Mem) (j : Word) (h : ¬ j < nF) :
    etpW p T b nF o (k + 1) m j = some m := by
  simp only [etpW, h, ↓reduceIte]

theorem etpW_cont (p : Prog) (T b nF o : Word) (k : Nat) (m m₁ : Mem) (j : Word) (r : List Word)
    (h : j < nF) (hc : callW p k "mk_proj" [T, j, b] m = some (r, m₁))
    (hg : (o + j).toNat < (m₁.arr64 SPN).size) :
    etpW p T b nF o (k + 1) m j = etpW p T b nF o k (m₁.set64 SPN (o + j) (r.headD 0)) (j + 1) := by
  simp only [etpW, h, ↓reduceIte, hc, hg]

theorem etpW_bad (p : Prog) (T b nF o : Word) (k : Nat) (m m₁ : Mem) (j : Word) (r : List Word)
    (h : j < nF) (hc : callW p k "mk_proj" [T, j, b] m = some (r, m₁))
    (hg : ¬ (o + j).toNat < (m₁.arr64 SPN).size) :
    etpW p T b nF o (k + 1) m j = none := by
  simp only [etpW, h, ↓reduceIte, hc, hg]

theorem etaProjsLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k etaProjsLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
      etpW p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) k s₀.mem (s₀.loc 4) = some s'.mem; ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := etaProjsLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        callW_spec p k "mk_proj", ih] <;>
      finish (gen := 20) [etpW_end, etpW_cont, etpW_bad]

theorem etaProjsLoop_step_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p k) etaProjsLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
      etpW p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (k + 1) s₀.mem (s₀.loc 4) =
        some s'.mem; ⊤⦄ :=
  Triple.step_exec (etaProjsLoop_spec p (k + 1) s₀)

/-- Model of `eta_projs`. -/
def etpTop (p : Prog) (k : Nat) (m : Mem) (T b nF : Word) : Option (List Word × Mem) :=
  if (136 : Word).toNat < (m.arr64 CTL).size then
    if UInt64.ofNat (m.arr64 SPN).size < rdW (m.arr64 CTL) 136 then none
    else if UInt64.ofNat (m.arr64 SPN).size - rdW (m.arr64 CTL) 136 < nF then none
    else match etpW p T b nF (rdW (m.arr64 CTL) 136) (k + 1) m 0 with
      | none => none
      | some m' =>
        if (136 : Word).toNat < (m'.arr64 CTL).size then
          some ([rdW (m.arr64 CTL) 136, nF], m'.set64 CTL 136 (rdW (m.arr64 CTL) 136 + nF))
        else none
  else none

theorem etaProjs_spec (p : Prog) (hp : p.lookup "eta_projs" = some etaProjsL) (k : Nat)
    (s₀ : St) (T b nF : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "eta_projs" [T, b, nF]
    ⦃fun r s' => LocEq s' s₀ ∧ etpTop p k s₀.mem T b nF = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, etaProjsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      etaProjsLoop_step_spec p k] <;>
    finish (gen := 20) [etpTop, rdW, Mem.len64]

theorem projNodesGo_nil_run (T : NIdx) (b : EIdx) (j : Nat) (a : AState) :
    (projNodesGo T b 0 j).run a = .ok ([], a) := by
  simp [projNodesGo]; rfl

theorem projNodesGo_cons_run (T : NIdx) (b : EIdx) (n j : Nat) (a a₁ a₂ : AState) (pn : EIdx)
    (ys : List EIdx) (h1 : (internE (.proj T j b)).run a = .ok (pn, a₁))
    (h2 : (projNodesGo T b n (j + 1)).run a₁ = .ok (ys, a₂)) :
    (projNodesGo T b (n + 1) j).run a = .ok (pn :: ys, a₂) := by
  simp only [projNodesGo, StateT.run_bind, h1, except_ok_bind, h2]; rfl

/-- **The `eta_projs` loop refines `projNodesGo`**, by induction on the remaining count. -/
theorem etpW_ok (p : Prog) (hp : IotaProg' p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (eb T b nF o : Word) (hT : HW T) (hb : HW b) :
    ∀ (K k : Nat) (m : Mem) (a : AState) (M : ModeMaps) (j : Word) (m' : Mem),
      nF.toNat - j.toNat = K → j.toNat ≤ nF.toNat → CoreS dn m a vis fe M eb →
      o.toNat + nF.toNat ≤ (m.arr64 SPN).size →
      etpW p T b nF o k m j = some m' →
      ∃ ys, AM.ok (projNodesGo (decI T) (decE b) K j.toNat) a ∧
        CoreS dn m' (AM.st (projNodesGo (decI T) (decE b) K j.toNat) a) vis fe M eb ∧
        AM.res (projNodesGo (decI T) (decE b) K j.toNat) a = ys ∧
        (∀ i : Word, i < o + j → spW m' i = spW m i) ∧ (m'.arr64 SPN).size = (m.arr64 SPN).size ∧
        spTop m' = spTop m ∧ SpineR m' (o + j) (nF - j) ys.toArray := by
  intro K
  induction K with
  | zero =>
    intro k m a M j m' hK hj hS hso hL
    have hn : ¬ j < nF := fun h => by
      have : j.toNat < nF.toNat := h
      omega
    cases k with
    | zero => simp [etpW] at hL
    | succ k =>
    rw [etpW_end p T b nF o k m j hn] at hL
    cases hL
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (projNodesGo_nil_run (decI T) (decE b) j.toNat a)
    refine ⟨[], hok, ?_, hres, fun i _ => rfl, rfl, rfl, ?_⟩
    · rw [hst]; exact hS
    · have hjp : nF - j = 0 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]
        simp; omega
      rw [hjp]
      have hlen : (o + j).toNat ≤ (m.arr64 SPN).size := by
        have := hS.spn
        rw [UInt64.toNat_add]; simp; omega
      exact SpineR.nil_at m _ hlen
  | succ K ih =>
    intro k m a M j m' hK hj hS hso hL
    have hlt : j < nF := by
      have : j.toNat < nF.toNat := by omega
      exact this
    cases k with
    | zero => simp [etpW] at hL
    | succ k =>
    have hspn := hS.spn
    have hoj : (o + j).toNat = o.toNat + j.toNat := by
      rw [UInt64.toNat_add]; simp; omega
    cases hc1 : callW p k "mk_proj" [T, j, b] m with
    | none => simp only [etpW, hlt, ↓reduceIte, hc1] at hL; cases hL
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    by_cases hgn : ¬ (o + j).toNat < (m₁.arr64 SPN).size
    · rw [etpW_bad p T b nF o k m m₁ j r₁ hlt hc1 hgn] at hL; cases hL
    have hg := Classical.not_not.mp hgn
    rw [etpW_cont p T b nF o k m m₁ j r₁ hlt hc1 hg] at hL
    obtain ⟨hok1, hD1, hres1, hfr1, hw1⟩ := callW_mkProj p hp k ⟨m, Locals.init []⟩ a hS.arena T j b
      r₁ m₁ hc1
    have hfr1 : MemFrame L.Rom.StoreA L.Rom.StoreC m m₁ := hfr1
    have hrun1 := AM.run_of_ok _ _ hok1
    have hspn1 : m₁.arr64 SPN = m.arr64 SPN :=
      hfr1.1 SPN (fun h => by
        have : SPN < 64 := by unfold L.Rom.StoreA at h; exact List.mem_range.mp h
        simp [SPN] at this) (by decide)
    have hcpl := Keeps.run (keeps_cpl_internProj (decI T) j.toNat (decE b)) hrun1
    have hS1 : CoreS dn m₁ (AM.st (internE (.proj (decI T) j.toNat (decE b))) a) vis fe M eb :=
      hS.of_proj hD1 hcpl hfr1
    have hsz1 : (m₁.arr64 SPN).size = (m.arr64 SPN).size := by rw [hspn1]
    have hfrS : MemFrame [SPN] [] m₁ (m₁.set64 SPN (o + j) (r₁.headD 0)) :=
      MemFrame.set64 m₁ SPN (by decide) _ _
    have hS2 : CoreS dn (m₁.set64 SPN (o + j) (r₁.headD 0)) (AM.st (internE (.proj (decI T) j.toNat (decE b))) a)
        vis fe M eb := hS1.frame_stk hfrS (fun b hb => by simpa using hb) (fun x hx => by simp at hx)
    have hsz2 : ((m₁.set64 SPN (o + j) (r₁.headD 0)).arr64 SPN).size = (m.arr64 SPN).size := by
      rw [size_set64, hsz1]
    have h1 : (j + 1).toNat = j.toNat + 1 := uint64_succ_toNat nF j hlt
    obtain ⟨ys, hok3, hS3, hres3, hbelow, hsz3, htop3, hys⟩ := ih k _ _ M (j + 1) m' (by omega)
      (by omega) hS2 (by rw [hsz2]; exact hso) hL
    have hrunI := AM.run_of_ok _ _ hok1
    rw [hres1] at hrunI
    have hrunR := AM.run_of_ok _ _ hok3
    rw [h1] at hrunR hS3 hres3
    rw [hres3] at hrunR
    have hrun := projNodesGo_cons_run (decI T) (decE b) K j.toNat a _ _ _ ys hrunI hrunR
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun
    have hbelow' : ∀ i : Word, i < o + j → spW m' i = spW m i := by
      intro i hi
      have hi' : i < o + (j + 1) := by
        rw [UInt64.lt_iff_toNat_lt] at hi ⊢
        have : (o + (j + 1)).toNat = o.toNat + j.toNat + 1 := by
          rw [UInt64.toNat_add, h1]; simp; omega
        omega
      rw [hbelow i hi']
      have hne : o + j ≠ i := by
        intro h; rw [← h] at hi
        exact absurd (UInt64.lt_iff_toNat_lt.mp hi) (Nat.lt_irrefl _)
      rw [spW_set64_ne _ _ _ _ hne]
      simp only [spW, hspn1]
    refine ⟨decE (r₁.headD 0) :: ys, hokF, ?_, ?_, hbelow', ?_, ?_, ?_⟩
    · rw [hstF]; exact hS3
    · rw [hresF]
    · rw [hsz3, hsz2]
    · rw [htop3]
      unfold spTop
      rw [Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ SPN by decide)]
      exact hfr1.2.1 136 (fun h => by
        unfold L.Rom.StoreC at h
        obtain ⟨k', hk', hkk⟩ := List.mem_map.mp h
        have := List.mem_range.mp hk'
        have h' := congrArg UInt64.toNat hkk
        simp [UInt64.toNat_ofNat] at h'; omega)
    · have e1 : nF - j = (nF - (j + 1)) + 1 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega),
          UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega), h1]
        simp; omega
      have e2 : o + (j + 1) = o + j + 1 := by rw [UInt64.add_assoc]
      rw [e1]
      rw [e2] at hys
      have hsizeM : (m'.arr64 SPN).size = (m.arr64 SPN).size := by rw [hsz3, hsz2]
      refine SpineR.cons_slot m' (o + j) (nF - (j + 1)) (r₁.headD 0) ys hw1 ?_ hys ?_
        (by rw [hsizeM]; exact hspn)
      · have := hbelow (o + j) (by
          rw [UInt64.lt_iff_toNat_lt, e2, UInt64.toNat_add]
          have : (o + j + 1).toNat = o.toNat + j.toNat + 1 := by
            rw [UInt64.toNat_add]; simp; omega
          rw [← e2]
          rw [UInt64.toNat_add, h1]; simp; omega)
        rw [this, spW_set64_eq _ _ _ hg]
      · rw [hsizeM, UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega), hoj]
        omega

/-- **`eta_projs` refines `etaProjs`.** Statement change: `CoreAfterG` (the result slice is left on
the stack: the top grows) in place of `CoreAfter`. -/
theorem etaProjs_refines' (p : Prog) (hp : IotaProg' p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb T b nF : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW T → HW b →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "eta_projs" [T, b, nF]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (etaProjs (decI T) (decE b) nF.toNat) a₀ ∧
      CoreAfterG dn s₀.mem s'.mem (AM.st (etaProjs (decI T) (decE b) nF.toNat) a₀) vis fe MM eb ∧
      r.headD 0 = spTop s₀.mem ∧ r.tail.headD 0 = nF ∧
      ∃ xs, AM.res (etaProjs (decI T) (decE b) nF.toNat) a₀ = xs ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄ := by
  intro n s₀ a₀ dn vis fe MM eb T b nF hS hT hb
  cases n with
  | zero =>
    apply L.M.triple_of_run
    intro s r s' _ hrun
    exact (invoke_zero_run _ _ _ _ _ _ hrun).elim
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (etaProjs_spec p hp.etaProjs n s₀ T b nF)
  subst hs0
  refine ⟨hloc, ?_⟩
  simp only [etpTop] at hW
  by_cases h136n : ¬ (136 : Word).toNat < (s.mem.arr64 CTL).size
  · rw [if_neg h136n] at hW; cases hW
  have h136 : (136 : Word).toNat < (s.mem.arr64 CTL).size := Classical.not_not.mp h136n
  rw [if_pos h136] at hW
  by_cases hg1 : UInt64.ofNat (s.mem.arr64 SPN).size < rdW (s.mem.arr64 CTL) 136
  · rw [if_pos hg1] at hW; cases hW
  rw [if_neg hg1] at hW
  by_cases hg2 : UInt64.ofNat (s.mem.arr64 SPN).size - rdW (s.mem.arr64 CTL) 136 < nF
  · rw [if_pos hg2] at hW; cases hW
  rw [if_neg hg2] at hW
  cases hm : etpW p T b nF (rdW (s.mem.arr64 CTL) 136) (n + 1) s.mem 0 with
  | none => rw [hm] at hW; cases hW
  | some m' =>
  rw [hm] at hW
  dsimp only at hW
  by_cases hg3n : ¬ (136 : Word).toNat < (m'.arr64 CTL).size
  · rw [if_neg hg3n] at hW; cases hW
  have hg3 : (136 : Word).toNat < (m'.arr64 CTL).size := Classical.not_not.mp hg3n
  rw [if_pos hg3] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hmm⟩ := hW
  have hspn := hS.spn
  have h64 : (s.mem.arr64 SPN).size < 2 ^ 64 := by omega
  have hsolt : (rdW (s.mem.arr64 CTL) 136).toNat ≤ (s.mem.arr64 SPN).size := by
    have : ¬ (s.mem.arr64 SPN).size < (rdW (s.mem.arr64 CTL) 136).toNat := by
      intro h
      apply hg1
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' h64]; exact h
    omega
  have hso : (rdW (s.mem.arr64 CTL) 136).toNat + nF.toNat ≤ (s.mem.arr64 SPN).size := by
    have h2 : ¬ UInt64.ofNat (s.mem.arr64 SPN).size - rdW (s.mem.arr64 CTL) 136 < nF := hg2
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' h64]; exact hsolt),
      UInt64.toNat_ofNat_of_lt' h64] at h2
    omega
  obtain ⟨ys, hok, hS', hres, hbelow, hsz, htop, hys⟩ := etpW_ok p hp dn vis fe eb T b nF
    (rdW (s.mem.arr64 CTL) 136) hT hb (nF.toNat - (0 : Word).toNat) (n + 1) s.mem a₀ MM 0 m' rfl
    (by simp) hS hso hm
  have hr1 : r.headD 0 = rdW (s.mem.arr64 CTL) 136 := by
    have := congrArg (fun l => l.headD 0) hr.symm; simpa using this
  have hr2 : r.tail.headD 0 = nF := by
    have := congrArg (fun l => l.tail.headD 0) hr.symm; simpa using this
  have hfS : MemFrame [] [136] m' (m'.set64 CTL 136 (rdW (s.mem.arr64 CTL) 136 + nF)) :=
    MemFrame.setCtl _ _ _
  have hS'' := hS'.frame_stk hfS (fun b hb => by simpa using hb) (fun x hx => by simpa using hx)
  have hoo : (rdW (s.mem.arr64 CTL) 136 + nF).toNat = (rdW (s.mem.arr64 CTL) 136).toNat + nF.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  simp only [etaProjs]
  refine ⟨hok, ⟨MM, ?_, KeptAll.refl _ _, ?_⟩, hr1, hr2, ys, hres, ?_⟩
  · rw [← hmm]; simpa using hS''
  · rw [← hmm]
    refine ⟨?_, ?_, fun i hi => ?_⟩
    · unfold spTop
      rw [rdW_set64, if_pos ⟨rfl, rfl, hg3⟩, UInt64.le_iff_toNat_le, hoo]
      omega
    · rw [size_set64L, hsz]
    · rw [spW_setCtl]
      exact hbelow i (by rw [UInt64.add_zero]; exact hi)
  · rw [← hmm, hr1, hr2]
    have := hys.setCtl 136 (rdW (s.mem.arr64 CTL) 136 + nF)
    simpa using this

/-! ## `eta_fab_args(T, to, tn, major, nF)` -/

theorem word_add_split (off a : Word) (i : Nat) (h : a.toNat ≤ i) :
    off + i.toUInt64 = (off + a) + (i - a.toNat).toUInt64 := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  have : i - a.toNat = d := by omega
  rw [this, hd]
  simp [Nat.toUInt64, UInt64.ofNat_add, UInt64.add_assoc]

theorem SpineR.append {m : Mem} {off a b : Word} {xs ys : Array EIdx} (hx : SpineR m off a xs)
    (hy : SpineR m (off + a) b ys) (hspn : (m.arr64 SPN).size < 2 ^ 63) :
    SpineR m off (a + b) (xs ++ ys) := by
  have hxb := hx.bound
  have hyb := hy.bound
  have hoa : (off + a).toNat = off.toNat + a.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hab : (a + b).toNat = a.toNat + b.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  refine ⟨by simp [hx.size, hy.size, hab], by rw [hab]; omega, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hab] at hi
    by_cases hia : i < a.toNat
    · exact hx.lt i hia
    · rw [word_add_split off a i (by omega)]
      exact hy.lt (i - a.toNat) (by omega)
  · simp only [Array.size_append, hx.size, hy.size] at hi
    by_cases hia : i < a.toNat
    · rw [Array.getElem_append_left (by rw [hx.size]; exact hia)]
      exact hx.get i (by rw [hx.size]; exact hia)
    · rw [Array.getElem_append_right (by rw [hx.size]; omega), word_add_split off a i (by omega)]
      have := hy.get (i - a.toNat) (by rw [hy.size]; omega)
      simpa [hx.size] using this

/-- Model of `eta_fab_args`. -/
def efaW (p : Prog) (k : Nat) (m : Mem) (T to tn major nF : Word) : Option (List Word × Mem) :=
  match callW p k "eta_projs" [T, major, nF] m with
  | none => none
  | some (r, m₁) => some ([to, tn + r.tail.headD 0], m₁)

theorem etaFabArgs_spec (p : Prog) (hp : p.lookup "eta_fab_args" = some etaFabArgsL) (k : Nat)
    (s₀ : St) (T to tn major nF : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "eta_fab_args" [T, to, tn, major, nF]
    ⦃fun r s' => LocEq s' s₀ ∧ efaW p k s₀.mem T to tn major nF = some ([r.headD 0, r.tail.headD 0], s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, etaFabArgsL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p k "eta_projs"] <;>
  simp_all [efaW, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]

theorem etaFabArgsE_run (T : NIdx) (targs : List EIdx) (major : EIdx) (nF : Nat) (a a₁ : AState)
    (ps : List EIdx) (h : (etaProjs T major nF).run a = .ok (ps, a₁)) :
    (etaFabArgsE T targs major nF).run a = .ok (targs ++ ps, a₁) := by
  simp only [etaFabArgsE, StateT.run_bind, h, except_ok_bind]; rfl

/-- **`eta_fab_args` refines `etaFabArgsE`.** Statement change: `CoreAfterG`. -/
theorem etaFabArgs_refines' (p : Prog) (hp : IotaProg' p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb T to tn major nF : Word) (targs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW T → HW major → SpineR s₀.mem to tn targs →
    to + tn = spTop s₀.mem →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "eta_fab_args" [T, to, tn, major, nF]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (etaFabArgsE (decI T) targs.toList (decE major) nF.toNat) a₀ ∧
      CoreAfterG dn s₀.mem s'.mem (AM.st (etaFabArgsE (decI T) targs.toList (decE major) nF.toNat) a₀)
        vis fe MM eb ∧
      ∃ xs, AM.res (etaFabArgsE (decI T) targs.toList (decE major) nF.toNat) a₀ = xs ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄ := by
  intro n s₀ a₀ dn vis fe MM eb T to tn major nF targs hS hT hmaj hsp htop
  cases n with
  | zero =>
    apply L.M.triple_of_run
    intro s r s' _ hrun
    exact (invoke_zero_run _ _ _ _ _ _ hrun).elim
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (etaFabArgs_spec p hp.etaFabArgs n s₀ T to tn major nF)
  subst hs0
  refine ⟨hloc, ?_⟩
  simp only [efaW] at hW
  cases hc1 : callW p n "eta_projs" [T, major, nF] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  obtain ⟨t₁, ht₁, hloc1, hok, hca, hhead, htail, ys, hres, hys⟩ := triple_of_callW
    (etaProjs_refines' p hp n ⟨s.mem, Locals.init []⟩ a₀ dn vis fe MM eb T major nF hS hT hmaj) hc1
  rw [ht₁] at hca hys
  obtain ⟨M₁, hS₁, hK₁, hSt₁⟩ := hca
  have hSt₁ : StackGrew s.mem m₁ := hSt₁
  have hspn := hS.spn
  have hsp₁ : SpineR m₁ to tn targs := by
    have hb := hsp.bound
    refine hsp.keep hSt₁.2.1 hSt₁.2.2 ?_ hspn
    have : (to + tn).toNat = to.toNat + tn.toNat := by
      rw [UInt64.toNat_add]; simp; omega
    rw [← this, htop]
    exact Nat.le_refl _
  have hr1 : r.headD 0 = to := by
    have := congrArg (fun l => l.headD 0) hr.symm; simpa using this
  have hr2 : r.tail.headD 0 = tn + r₁.tail.headD 0 := by
    have := congrArg (fun l => l.tail.headD 0) hr.symm; simpa using this
  have hys' : SpineR m₁ (to + tn) (r₁.tail.headD 0) ys.toArray := by
    have : r₁.headD 0 = to + tn := by rw [htop]; exact hhead
    rw [← this]; exact hys
  have happ := hsp₁.append hys' (by rw [hSt₁.2.1]; exact hspn)
  obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _
    (etaFabArgsE_run (decI T) targs.toList (decE major) nF.toNat a₀ _ ys
      (by simpa [etaProjs] using AM.run_of_ok _ _ hok |> fun h => by rw [hres] at h; exact h))
  refine ⟨hokF, ⟨M₁, ?_, hK₁, ?_⟩, targs.toList ++ ys, hresF, ?_⟩
  · rw [hstF, ← hm]; exact hS₁
  · rw [← hm]; exact hSt₁
  · rw [hr1, hr2, ← hm]
    have e : (targs.toList ++ ys).toArray = targs ++ ys.toArray := by
      apply Array.ext'
      simp
    rw [e]; simpa using happ

end L.Arena

