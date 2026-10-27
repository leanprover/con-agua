import ConAgua.Arena.WhnfIota
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Scan.Common
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.WhnfCoreProj
import ConAgua.L.Examples

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
def findRuleW (E : Array Word) (ro rc c : Word) : Nat → Word → Option (List Word)
  | 0, _ => some [0, 0]
  | K + 1, i =>
    if i < rc then
      if h : (ro + 11 * i).toNat < E.size then
        if E[(ro + 11 * i).toNat] = c then some [1, ro + 11 * i] else findRuleW E ro rc c K (i + 1)
      else none
    else some [0, 0]

theorem uint64_succ_toNat (n i : Word) (h : i < n) : (i + 1).toNat = i.toNat + 1 := by
  rw [UInt64.toNat_add]; simp
  have := n.toNat_lt
  have : i.toNat < n.toNat := h
  omega

theorem frW_done (E : Array Word) (ro rc c i : Word) (h : ¬ i < rc) :
    findRuleW E ro rc c (rc.toNat - i.toNat) i = some [0, 0] := by
  cases hK : rc.toNat - i.toNat with
  | zero => rw [findRuleW]
  | succ k => rw [findRuleW]; simp [h]

theorem frW_step (E : Array Word) (ro rc c i : Word) (h : i < rc) :
    findRuleW E ro rc c (rc.toNat - i.toNat) i =
      if h : (ro + 11 * i).toNat < E.size then
        if E[(ro + 11 * i).toNat] = c then some [1, ro + 11 * i]
        else findRuleW E ro rc c (rc.toNat - (i + 1).toNat) (i + 1)
      else none := by
  have h1 := uint64_succ_toNat rc i h
  have : i.toNat < rc.toNat := h
  have hK : rc.toNat - i.toNat = (rc.toNat - (i + 1).toNat) + 1 := by omega
  rw [hK, findRuleW]
  simp [h]

theorem findRuleLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k findRuleLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      findRuleW (s₀.mem.arr64 EREC) (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) ((s₀.loc 1).toNat - (s₀.loc 3).toNat)
        (s₀.loc 3) = some (r.retOr [0, 0]); ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := findRuleLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish [frW_done, frW_step]


theorem findRule_spec (p : Prog) (hp : p.lookup "find_rule" = some findRuleL) (k : Nat)
    (s₀ : St) (ro rc c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p k) "find_rule" [ro, rc, c]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      findRuleW (s₀.mem.arr64 EREC) ro rc c rc.toNat 0 = some r; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, findRuleL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, fun s₀ => Triple.step_exec (findRuleLoop_spec p (k + 1) s₀)] <;>
      finish

/-- **The scan model computes `findRule`.** -/
theorem frW_rel (E : Array Word) (hsz : E.size < 2 ^ 64) (ro rc c : Word) (hc : HW c)
    (rules : List IRecRule) (hlen : rules.length = rc.toNat)
    (hget : ∀ j, j < rc.toNat → decRule E (ro.toNat + 11 * j) = rules[j]?) :
    ∀ (K : Nat) (i : Word) (L : List Word), rc.toNat - i.toNat = K →
      findRuleW E ro rc c K i = some L →
      findRule (rules.drop i.toNat) (decI c) =
        (if L.headD 0 = 0 then none else decRule E (L.tail.headD 0).toNat) := by
  intro K
  induction K with
  | zero =>
    intro i L hK h
    rw [findRuleW] at h
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
    rw [findRuleW] at h
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
@[refines ConRon.Arena.findRule]
theorem findRule_refines (p : Prog) (hp : p.lookup "find_rule" = some findRuleL) (n : Nat)
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
@[refines ConRon.Arena.recRuleK]
theorem recRuleK_refines (p : Prog) (hp : p.lookup "rec_rule_k" = some recRuleKL) (n : Nat)
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

/-- Fuel zero runs nothing, so every triple about a call holds. -/
theorem invoke_zero_triple {p : Prog} {f : FnName} {args : List Word} {P : St → Prop}
    {Q : List Word → St → Prop} : ⦃fun s => P s⦄ invoke p (exec p 0) f args ⦃fun r s => Q r s; ⊤⦄ :=
  L.M.triple_of_run fun _ _ _ _ h => (invoke_zero_run _ _ _ _ _ _ h).elim

/-- **A refinement spec applied to a run**, as the twin's run. -/
theorem CoreSpec.run {α : Type} [Inhabited α] {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {T : AM α} {dec : List Word → α} {s₀ : St} {a₀ : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {ok : List Word → Prop} (h : CoreSpec p n f args T dec s₀ a₀ dn vis fe M eb ok)
    {r : List Word} {m' : Mem} (hc : callW p n f args s₀.mem = some (r, m')) :
    T.run a₀ = .ok (dec r, AM.st T a₀) ∧ CoreAfter dn s₀.mem m' (AM.st T a₀) vis fe M eb ∧ ok r :=
  let ⟨hok, hA, hres, hr⟩ := h.of_callW hc
  ⟨hres ▸ AM.run_of_ok _ _ hok, hA, hr⟩

/-- **A refinement from the twin's run.** -/
theorem CoreRef.of_run {α : Type} [Inhabited α] {T : AM α} {a a' : AState} {v : α}
    {dec : List Word → α} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word} {ok : List Word → Prop}
    (hrun : T.run a = .ok (v, a')) (hA : CoreAfter dn m m' a' vis fe M eb) (hv : v = dec r)
    (hr : ok r) : CoreRef T a dec dn m vis fe M eb r m' ok := by
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hok, hst ▸ hA, hres.trans hv, hr⟩

theorem decH_of (w : Word) (r : List Word) (h : w = r.headD 0) : decE w = decH r := by
  rw [h]; rfl

theorem resH_of_m2c (w : Word) (r : List Word) (h : w = r.headD 0) (hw : HW w) : ResH r := by
  unfold ResH; rw [← h]; exact hw

theorem decBool_f_m2c {r : List Word} (h : r.headD 0 = 0) : decBool r = false := by
  unfold decBool; rw [h]; rfl

theorem decBool_t_m2c {r : List Word} (h : ¬ r.headD 0 = 0) : decBool r = true := by
  unfold decBool; exact bne_iff_ne.mpr h

/-! ## `is_str_lit(h)` -/

/-- Model of `is_str_lit`. -/
def islW (m : Mem) (h : Word) : Option Word :=
  if h >>> 28 ≠ 8 then some 0
  else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m LIT (tierW h) ≤ idxW h then none
  else some (if tfld m LIT (tierW h) (idxW h) 0 = 1 then 1 else 0)

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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
        tcntM, evalE_tierE, evalE_idxE] <;> finish [islW, tierW, idxW]

theorem viewLit_ok (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h LIT) :
    ∃ l, a.store.viewLit (decE h) = some l ∧ RecRel m (tierW h) (idxW h) ⟨l⟩ := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h litCS RecRel (·.lits) _ hR.lit.2 hv.2
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
@[refines ConRon.Arena.isStrLit]
theorem isStrLit_refines (p : Prog) (hp : p.lookup "is_str_lit" = some isStrLitL) :
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
    by_cases hv2 : tcnt s₀.mem LIT (tierW h) ≤ idxW h
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
    (hv : viewOK m h CONST) (hg : h >>> 28 = 3) :
    a.store.view (decE h) = some (.const (decI (tfld m CONST (tierW h) (idxW h) 0))
      (decI (tfld m CONST (tierW h) (idxW h) 1))) ∧
    (tfld m CONST (tierW h) (idxW h) 0).toNat < 2 ^ 32 ∧
    (tfld m CONST (tierW h) (idxW h) 1).toNat < 2 ^ 32 := by
  obtain ⟨k, hk, hn, hu⟩ := node_of m a h constCS CeRecRel (·.consts) _ hR.const hv.2
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
    else if tcnt m₁ CONST (tierW (r₁.headD 0)) ≤ idxW (r₁.headD 0) then none
    else match callW p n "env_find"
        [tfld m₁ CONST (tierW (r₁.headD 0)) (idxW (r₁.headD 0)) 0, vis] m₁ with
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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
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
@[refines ConRon.Arena.isCtorApp]
theorem isCtorApp_refines (p : Prog) (hp : IotaProg' p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb e : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW e →
    CoreSpec p (n + 1) "is_ctor_app" [vis, e] (isCtorApp fe (decE e)) decBool s₀ a₀ dn vis fe MM eb := by
  intro n s₀ a₀ dn vis fe MM eb e hS he
  refine triple_post (isCtorApp_spec p hp n s₀ vis e) fun r s' ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  have hR := hS.arena.1
  simp only [icaW] at hW
  rcases hc : callW p n "get_app_fn" [e] s₀.mem with _ | ⟨r₁, m₁⟩ <;>
    simp only [hc, reduceCtorEq] at hW
  obtain ⟨t₁, ht₁, hm₁, -, hh1, hga⟩ := triple_of_callW
    (getAppFn_refines' p hp.spine.fn n s₀ a₀ hR e he) hc
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
  rw [ite_eq_right h3] at hW
  obtain ⟨hv1, hW⟩ := of_ite_none hW
  obtain ⟨hv2, hW⟩ := of_ite_none hW
  have h3 := h3'
  obtain ⟨hvw, hn32, -⟩ := view_const_f s₀.mem a₀ hR (r₁.headD 0) hh1 ⟨hv1, UInt64.not_le.mp hv2⟩ h3
  generalize tfld s₀.mem CONST (tierW (r₁.headD 0)) (idxW (r₁.headD 0)) 0 = cw at hvw hn32 hW
  rcases hc2 : callW p n "env_find" [cw, vis] s₀.mem with _ | ⟨r₂, m₂⟩ <;>
    simp only [hc2, reduceCtorEq] at hW
  obtain ⟨t₂, ht₂, hm₂, -, hfind⟩ := triple_of_callW
    (envFind_refines p hp.envix hp.envrow hp.envfind n s₀ vis _ hS.env hn32) hc2
  obtain ⟨t₂', ht₂', hm₂', -, hfound⟩ := triple_of_callW
    (envFind_found p hp.envix hp.envrow hp.envfind n s₀ vis _ hn32) hc2
  rw [ht₂] at hm₂
  have htag : (decE (r₁.headD 0)).tag = ETag.const := (decE_tag_eq _ hh1 3 (by decide)).mpr h3
  have hrun1 := isCtorApp_run_const fe a₀ (decE e) _ hga htag _ _ hvw
  subst hm₂
  by_cases h0 : r₂.headD 0 = 0
  · rw [ite_eq_left h0] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    have hnone : fe.find? (decI cw) = none := by rw [hfind]; simp only [decFound, h0, ↓reduceIte]
    rw [hnone] at hrun1
    refine CoreRef.of_pure hS hrun1 hm.symm ?_ ?_
    · simp only [decBool]; rw [← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [ite_eq_right h0] at hW
  obtain ⟨htag2, hrow, hq⟩ := hfound h0
  obtain ⟨ci, hci⟩ := hS.env.found_some cw hn32 htag2 hrow
  have hfind' : fe.find? (decI cw) = some ci := by
    rw [hfind]; simp only [decFound, h0, ↓reduceIte, hq]; exact hci
  rw [← hq] at hci
  have hctor := decCI_ctor hci (erecP_ext _) hS.erec
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  rw [hfind'] at hrun1
  by_cases h4 : rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0) = 4
  · obtain ⟨cv, np, nf, rfl, -⟩ := hctor.1 h4
    rw [ite_eq_left h4] at hr
    refine CoreRef.of_pure hS hrun1 hm.symm ?_ ?_
    · simp only [decBool]; rw [← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  · rw [ite_eq_right h4] at hr
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
    (hc : CoreRM m' c M eb) (hL : c.readLC = a.caches.readLC) (hLs : c.readLsC = a.caches.readLsC)
    (hN : c.readNC = a.caches.readNC := by rfl) :
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
  refine ⟨⟨⟨?_, ?_⟩, hc, ?_, ?_, ?_, ?_, hS.nwf, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (ArenaR.frame_ext [S.arr] [S.cs + 1] (fun b hb => by simp at hb; subst hb; rw [← har]; simp only [ArrId]; omega)
      (fun x hx => by
        simp at hx; subst hx
        have : (S.cs + 1).toNat = S.cs.toNat + 1 := by
          rw [UInt64.toNat_add]; simp; omega
        omega) m m' hf a hS.arena.1).caches_irrel c
  · have := DerR.frameM [S.arr] [S.cs + 1] m m' hf (fun b hb => by simp at hb; subst hb; rw [← har]; simp only [ArrId]; omega) a hS.arena.2
    exact DerR.of_store _ _ _ this rfl
  · exact hS.pins.congr (hf.1 PINS (fun h => by simp at h; simp only [PINS] at h; rw [← har] at h; rw [← h] at n2; exact absurd n2 (by decide))
      (by decide))
  · exact hS.env.frame (aA 129 144 (Or.inr (by omega))) (aC 128 136 (Or.inr (by omega))) hf
      (aA 385 388 (Or.inr (by omega)))
  · intro h l e; exact hS.readL h l (by simpa [hL] using e)
  · intro h l e; exact hS.readLs h l (by simpa [hLs] using e)
  · exact hf.2.2.1 EREC ▸ hS.erec
  · exact hf.2.2.1 SPN ▸ hS.spn
  · exact hS.memos.frame_hi hf
      (fun b hb => by simp at hb; subst hb; rw [← har]; simp only [ArrId]; omega)
      (fun x hx => by
        simp at hx; subst hx
        have : (S.cs + 1).toNat = S.cs.toNat + 1 := by
          rw [UInt64.toNat_add]; simp; omega
        omega)
      (fun b hb => by simp at hb; subst hb; rw [← har]; simp only [ArrId]; omega)
      (fun x hx => by
        simp at hx; subst hx
        have : (S.cs + 1).toNat = S.cs.toNat + 1 := by
          rw [UInt64.toNat_add]; simp; omega
        omega)
  · exact hf.2.2.1 145 ▸ hS.bstk
  · exact (hS.den.frameE (hf.1 EREC (fun h => by
      simp only [List.mem_singleton] at h; have h2' := h2; rw [← h] at h2'
      exact absurd h2' (by decide))
      (by decide))).caches rfl rfl hN
  · have hcs : (S.cs + 1).toNat = S.cs.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    exact hS.mode.frame hf
      (fun h => by simp at h; have h' := congrArg UInt64.toNat h; simp at h'; omega)
      (fun h => by simp at h; have h' := congrArg UInt64.toNat h; simp at h'; omega)
  · refine StackKept.of_frame_range hf (fun b hb => by
      simp only [List.mem_singleton] at hb; subst hb; constructor <;> simp only [ArrId] <;> omega)
      (fun x hx => by
      simp at hx; subst hx
      have : (S.cs + 1).toNat = S.cs.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; omega
      omega)
      (LvlFree.of_ge fun x hx => by
        simp at hx; subst hx
        have : (S.cs + 1).toNat = S.cs.toNat + 1 := by
          rw [UInt64.toNat_add]; simp; omega
        omega)
      (fun h => by simp only [List.mem_singleton] at h; have h1' := h1; rw [← h] at h1'; simp [PT0] at h1')

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

/-- **`const_ty_at` refines `constTyAt`** (`inst_lp` as the hypothesis `InstLPOK`). -/
theorem constTyAt_refines' (p : Prog) (hp : IotaProg' p) (hlp : InstLPOK p) :
    ConstTyAtOK p := by
  intro n s₀ a₀ dn vis fe MM eb nn po pl ty us lps hS hnn hty hus hlps
  cases n with
  | zero => exact invoke_zero_triple
  | succ n =>
  refine triple_post (constTyAt_spec p hp n s₀ nn po pl ty us) fun r s' ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  simp only [ctaW] at hW
  obtain ⟨h0, hW⟩ := of_ite_none hW
  have hf := memoRV_findP hS.core.ct nn us hnn hus h0
  by_cases h1 : (mfindG ctSch s₀.mem nn us).headD 0 ≠ 0
  · rw [ite_eq_left h1] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨hv, hv32⟩ := hf.1 h1
    have hrun1 := constTyAt_run_hit ⟨decI nn, lps, decE ty⟩ (decI us) a₀ _ hv
    refine CoreRef.of_pure hS hrun1 hm.symm ?_ ?_
    · simp only [decH]; rw [← hr]
    · unfold ResH HW; rw [← hr]; exact hv32
  rw [ite_eq_right h1] at hW
  have hmiss := hf.2 (by simpa using h1)
  rcases hc : callW p n "inst_lp" [po, pl, us, ty] s₀.mem with _ | ⟨r₁, m₁⟩ <;>
    simp only [hc, reduceCtorEq] at hW
  obtain ⟨hok, ⟨M', hS₁, hK, hSt⟩, hres, hr₁⟩ :=
    CoreSpec.of_callW (hlp n s₀ a₀ dn vis fe MM eb po pl us ty lps hS hty hus hlps) hc
  have hrunI := AM.run_of_ok _ _ hok
  have hrun2 := constTyAt_run_miss ⟨decI nn, lps, decE ty⟩ (decI us) a₀ _ _ hmiss hrunI
  rw [hres] at hrun2
  obtain ⟨h2, hW⟩ := of_ite_none hW
  cases hp : mputG ctSch m₁ nn us (r₁.headD 0) ((mfindG ctSch m₁ nn us).headD 0)
      ((mfindG ctSch m₁ nn us).tail.headD 0) with
  | none => rw [hp] at hW; cases hW
  | some m₂ =>
  rw [hp] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  have hs : msetG ctSch m₁ nn us (r₁.headD 0) = some m₂ := by rw [msetG_eq _ _ _ _ _ h2]; exact hp
  have hwv : HW (r₁.headD 0) := hr₁
  have hcore := hS₁.core.setCt nn us (r₁.headD 0) hnn hus hwv hs
  obtain ⟨hS₂, hSt₂⟩ := CoreS.setMemo ctSch _ hS₁
    (msetG_frame ctSch (coreSch_wf _ _ (by decide) (by decide)) _ _ _ _ _ hs)
    (by decide) (by decide) (by decide) (by decide) hcore rfl rfl
  refine CoreRef.of_run hrun2 (hm ▸ ⟨M', hS₂, hK, hSt.trans hSt₂⟩) ?_ ?_
  · simp only [decH]; rw [← hr]
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

/-- **`rule_rhs_at` refines `ruleRhsAt`** (`inst_lp` as the hypothesis `InstLPOK`). -/
theorem ruleRhsAt_refines' (p : Prog) (hp : IotaProg' p) (hlp : InstLPOK p) :
    RuleRhsAtOK p := by
  intro n s₀ a₀ dn vis fe MM eb rec ctor po pl rhs us lps hS hrec hctor hrhs hus hlps
  cases n with
  | zero => exact invoke_zero_triple
  | succ n =>
  refine triple_post (ruleRhsAt_spec p hp n s₀ rec ctor po pl rhs us) fun r s' ⟨hloc, hW⟩ => ⟨hloc,
    ?_⟩
  have hdk := rrKey_dk rec ctor us hctor hus
  simp only [rraW] at hW
  obtain ⟨h0, hW⟩ := of_ite_none hW
  have hf := memoRV_findR hS.core.rr rec (ctor ||| (us <<< 32)) hrec h0
  rw [hdk] at hf
  by_cases h1 : (mfindG rrSch s₀.mem rec (ctor ||| (us <<< 32))).headD 0 ≠ 0
  · rw [ite_eq_left h1] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨hv, hv32⟩ := hf.1 h1
    have hrun1 := ruleRhsAt_run_hit (decI rec) (decI ctor) lps (decE rhs) (decI us) a₀ _ hv
    refine CoreRef.of_pure hS hrun1 hm.symm ?_ ?_
    · simp only [decH]; rw [← hr]
    · unfold ResH HW; rw [← hr]; exact hv32
  rw [ite_eq_right h1] at hW
  have hmiss := hf.2 (by simpa using h1)
  rcases hc : callW p n "inst_lp" [po, pl, us, rhs] s₀.mem with _ | ⟨r₁, m₁⟩ <;>
    simp only [hc, reduceCtorEq] at hW
  obtain ⟨hok, ⟨M', hS₁, hK, hSt⟩, hres, hr₁⟩ :=
    CoreSpec.of_callW (hlp n s₀ a₀ dn vis fe MM eb po pl us rhs lps hS hrhs hus hlps) hc
  have hrunI := AM.run_of_ok _ _ hok
  have hrun2 := ruleRhsAt_run_miss (decI rec) (decI ctor) lps (decE rhs) (decI us) a₀ _ _ hmiss hrunI
  rw [hres] at hrun2
  obtain ⟨h2, hW⟩ := of_ite_none hW
  cases hp : mputG rrSch m₁ rec (ctor ||| (us <<< 32)) (r₁.headD 0)
      ((mfindG rrSch m₁ rec (ctor ||| (us <<< 32))).headD 0)
      ((mfindG rrSch m₁ rec (ctor ||| (us <<< 32))).tail.headD 0) with
  | none => rw [hp] at hW; cases hW
  | some m₂ =>
  rw [hp] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  have hs : msetG rrSch m₁ rec (ctor ||| (us <<< 32)) (r₁.headD 0) = some m₂ := by
    rw [msetG_eq _ _ _ _ _ h2]; exact hp
  have hwv : HW (r₁.headD 0) := hr₁
  have hcore := hS₁.core.setRr rec (ctor ||| (us <<< 32)) (r₁.headD 0) hrec hwv hs
  rw [hdk] at hcore
  obtain ⟨hS₂, hSt₂⟩ := CoreS.setMemo rrSch _ hS₁
    (msetG_frame rrSch (coreSch_wf _ _ (by decide) (by decide)) _ _ _ _ _ hs)
    (by decide) (by decide) (by decide) (by decide) hcore rfl rfl
  refine CoreRef.of_run hrun2 (hm ▸ ⟨M', hS₂, hK, hSt.trans hSt₂⟩) ?_ ?_
  · simp only [decH]; rw [← hr]
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
      else if tcnt m FORALL (tierW e) ≤ idxW e then none
      else match callW p k "inst_entry"
          [tfld m FORALL (tierW e) (idxW e) 1, rdW (m.arr64 SPN) (ao + i), 0] m with
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
    (h2 : tcnt m FORALL (tierW e) ≤ idxW e) :
    pirW p (k + 1) m e ao an i = none := by
  simp only [pirW, h, h6, h1, h2]; simp

theorem pirW_cont (p : Prog) (k : Nat) (m m₁ : Mem) (e ao an i : Word) (r : List Word)
    (h : i < an) (h6 : ¬ e >>> 28 ≠ 6) (h1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (h2 : ¬ tcnt m FORALL (tierW e) ≤ idxW e)
    (hc : callW p k "inst_entry"
          [tfld m FORALL (tierW e) (idxW e) 1, rdW (m.arr64 SPN) (ao + i), 0] m =
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
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM,
        evalE_tierE, evalE_idxE,
        callW_spec p k "inst_entry", ih] <;>
      finish [pirW_end, pirW_exit, pirW_ab1, pirW_ab2, pirW_cont, tierW, idxW]


theorem piResidual_spec (p : Prog) (hp : p.lookup "pi_residual" = some piResidualL) (k : Nat)
    (s₀ : St) (e ao an : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "pi_residual" [e, ao, an]
    ⦃fun r s' => LocEq s' s₀ ∧ pirW p (k + 1) s₀.mem e ao an 0 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, piResidualL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, fun s₀ => Triple.step_exec (piResidualLoop_spec p (k + 1) s₀)] <;>
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
    by_cases hv2 : tcnt m FORALL (tierW e) ≤ idxW e
    · rw [pirW_ab2 p k m e ao an i hlt h6 hv1 hv2] at hL; cases hL
    rcases hc : callW p k "inst_entry"
        [tfld m FORALL (tierW e) (idxW e) 1, rdW (m.arr64 SPN) (ao + i), 0] m with _ | ⟨r₁, m₁⟩
    · simp [pirW, hlt, h6, hv1, hv2, hc] at hL
    rw [pirW_cont p k m m₁ e ao an i r₁ hlt h6 hv1 hv2 hc] at hL
    obtain ⟨hvb, hbw, -⟩ := view_forall m a hS.arena.1 e he ⟨hv1, UInt64.not_le.mp hv2⟩ h6'
    have hvb' := viewBind_forall m a hS.arena.1 e he ⟨hv1, UInt64.not_le.mp hv2⟩ h6'
    obtain ⟨hrunT, ⟨M₁, hS₁, hK₁, hSt₁⟩, hr₁⟩ := CoreSpec.run
      (hinst k ⟨m, Locals.init []⟩ a dn vis fe M eb _ (rdW (m.arr64 SPN) (ao + i)) 0 hS (by
        have := (view_forall m a hS.arena.1 e he ⟨hv1, UInt64.not_le.mp hv2⟩ h6').2.2
        exact this)) hc
    have hsp₁ : SpineR m₁ ao an args := hsp.keep hSt₁.size hSt₁.below htop hS.spn
    have htop₁ : ao.toNat + an.toNat ≤ (spTop m₁).toNat := by rw [hSt₁.1]; exact htop
    have h1 : (i + 1).toNat = i.toNat + 1 := uint64_succ_toNat an i hlt
    obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hL1, hL2⟩ :=
      ih k m₁ (AM.st (instantiate1Fast coreWalkFuel (decE (tfld m FORALL (tierW e) (idxW e) 1))
        (decE (rdW (m.arr64 SPN) (ao + i))) (UInt64.toNat 0)) a) M₁ (r₁.headD 0) (i + 1) L m'
        (by omega) (by omega) hS₁ hr₁ hsp₁ htop₁ hL
    have hget : args[i.toNat] = decE (rdW (m.arr64 SPN) (ao + i)) := by
      have := hsp.get i.toNat hsz
      simpa [spW] using this
    have hrunR := AM.run_of_ok _ _ hok2
    rw [h1] at hrunR
    have hrun := piResidual_cons_run (decE e) args[i.toNat] (decE (tfld m FORALL (tierW e) (idxW e) 1))
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
theorem piResidual_refines (p : Prog) (hp : IotaProg' p) (hi1 : IotaInst1OK p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb e ao an : Word) (args : Array EIdx), CoreS dn s₀.mem a₀ vis fe MM eb →
    HW e → SpineR s₀.mem ao an args → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p n "pi_residual" [e, ao, an] (piResidual (decE e) args.toList) decOptR s₀ a₀ dn vis fe
      MM eb ResW := by
  intro n s₀ a₀ dn vis fe MM eb e ao an args hS he hsp htop
  cases n with
  | zero => exact invoke_zero_triple
  | succ n =>
  refine triple_post (piResidual_spec p hp.piResidual n s₀ e ao an) fun r s' ⟨hloc, hW⟩ => ⟨hloc,
    ?_⟩
  obtain ⟨hok, hca, hres, hL1, hL2⟩ := pirW_ok p hi1 dn vis fe eb ao an args
    (an.toNat - (0 : Word).toNat) (n + 1) s₀.mem a₀ MM e 0 r s'.mem rfl (by simp) hS he hsp htop hW
  refine ⟨hok, ?_, ?_, ⟨hL1, hL2⟩⟩
  · simpa using hca
  · simpa using hres

end L.Arena
