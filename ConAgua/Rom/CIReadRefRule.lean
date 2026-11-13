module

import ConAgua.Rom.CIReadRefCaps
import ConAgua.L.WordOff
import ConAgua.Rom.CIReadRefNames
public import ConAgua.Arena.RecLayout.RuleDec
public import ConAgua.Rom.CIReadRefBase
public import ConAgua.Rom.CIReadSpec
import ConAgua.Rom.ReadScr
import ConAgua.Arena.DeclNatCv

@[expose] public section

/-!
# The ROM constant readers: recursor rules (helper `decls4-rom`)

`rci_rule(q, r)` refines `Frontend.internRule` for a plain rule or one firing at levels (no pinned
constant ROM rule is nested), into the `Rule.size`-word record at `r` (`decRule`, through the
record's words `RuleRecW`); `rci_rules_to(q, o, k)` refines
`Frontend.internRules` into consecutive records (`decRules`).
-/


open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-- A record's field word as a number: the field's offset is a layout offset (at most `64`) and the
record is in a pool (below `2 ^ 41`). -/
theorem fld_toNat {b f : Word} (hf : f.toNat ≤ 64) (hb : b.toNat < 2 ^ 41) :
    (b + f).toNat = b.toNat + f.toNat := by
  rw [UInt64.toNat_add]; omega

/-- `omega` after the goal's field words `(b + f).toNat` are rewritten to `b.toNat + f.toNat`
(`fld_toNat`, the bounds discharged by `omega` from the layout's order facts in context). -/
macro "fld_omega" : tactic => `(tactic| ((try simp (disch := omega) only [L.Rom.fld_toNat]) <;> omega))

/-- A list decoded index by index. -/
theorem holds_mapM_range {α : Type} [Inhabited α] {SE SI : Nat → Prop} {g : Mem → Nat → Option α} {m : Mem}
    (xs : List α) (h : ∀ j (hj : j < xs.length), Holds SE SI (fun m => g m j) m xs[j]) :
    Holds SE SI (fun m => (List.range xs.length).mapM (g m)) m xs := by
  intro m' h1 h2
  show List.mapM (g m') (List.range xs.length) = some xs
  rw [L.Arena.mapM_some_of _ (fun j => xs.getD j default) _ (fun j hj => by
    have hj' := List.mem_range.mp hj
    have := h j hj' m' h1 h2
    simp only at this
    rw [this]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'])]
  congr 1
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h2)]

/-- `decRule` of a plain rule from its words (`RuleRecW`, the fire's kind word `0`). -/
theorem holds_decRule {m : Mem} {q : Nat} {c nf fk lo ll po pl rhs : Word}
    (h : RuleRecW (erA m) q c nf fk lo ll po pl rhs) (hc : c.toNat < 2 ^ 32) (hr : rhs.toNat < 2 ^ 32)
    (hk : fk = 0) :
    Holds (fun i => q ≤ i ∧ i < q + Rule.size.toNat) (fun _ => False) (fun m => decRule (erA m) q) m
      ⟨decI c, nf.toNat, .plain, decI rhs⟩ := by
  intro m' hE _
  have h' : RuleRecW (erA m') q c nf fk lo ll po pl rhs := h.shift fun j hj => hE _ ⟨by omega, by omega⟩
  exact decRule_of_words h' hc hr (h'.plain hk)

/-- A plain rule that fits its encoding. -/
def ruleFits (rl : ConLeche.RecRule) : Bool :=
  nameFits rl.ctor && decide (rl.nfields < 2 ^ 64) &&
    (match rl.fire with
     | .plain => true
     | .levels lvls => lvls.all levelFits && decide (lvls.length < 2 ^ 40)
     | _ => false) && exprFits rl.rhs

theorem encRule_eq (seen : List ConLeche.Expr) (rl : ConLeche.RecRule) (hp : rl.fire = .plain)
    (rest : List UInt8) :
    (encRule seen rl).1 ++ rest = encName rl.ctor ++ (u64B rl.nfields ++ (u64B 0 ++
      ((encExprM seen rl.rhs).1 ++ rest))) ∧ (encRule seen rl).2 = (encExprM seen rl.rhs).2 := by
  simp [encRule, hp, List.append_assoc]

theorem encRule_eqL (seen : List ConLeche.Expr) (rl : ConLeche.RecRule) (lvls : List ConLeche.Level)
    (hp : rl.fire = .levels lvls) (rest : List UInt8) :
    (encRule seen rl).1 ++ rest = encName rl.ctor ++ (u64B rl.nfields ++ (u64B 2 ++
      (u64B lvls.length ++ (encLevelList lvls ++ ((encExprM seen rl.rhs).1 ++ rest))))) ∧
      (encRule seen rl).2 = (encExprM seen rl.rhs).2 := by
  simp [encRule, hp, encLevels, List.append_assoc]

/-- `decRule` of a rule firing at levels, from its words (`RuleRecW`, the fire's kind word `2`)
and the level slice's words. -/
theorem holds_decRuleL {m : Mem} {q : Nat} {c nf fk lo ll po pl rhs : Word} (ws : List Word)
    (h : RuleRecW (erA m) q c nf fk lo ll po pl rhs) (hc : c.toNat < 2 ^ 32) (hr : rhs.toNat < 2 ^ 32)
    (hk : fk = 2) (hll : ll.toNat = ws.length)
    (hw : ∀ j (hj : j < ws.length), erA m (lo.toNat + j) = some ws[j]) (hlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) :
    Holds (fun i => (q ≤ i ∧ i < q + Rule.size.toNat) ∨ (lo.toNat ≤ i ∧ i < lo.toNat + ws.length))
      (fun _ => False) (fun m => decRule (erA m) q) m ⟨decI c, nf.toNat, .levels (ws.map decI), decI rhs⟩ := by
  intro m' hE _
  have h' : RuleRecW (erA m') q c nf fk lo ll po pl rhs :=
    h.shift fun j hj => hE _ (.inl ⟨by omega, by omega⟩)
  refine decRule_of_words h' hc hr (h'.levels hk ?_)
  rw [hll]
  exact hslice_of _ _ ws (fun j hj => (hE _ (.inr ⟨by omega, by omega⟩)).trans (hw j hj)) hlt

section rule
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

/-- `rci_rule` for a plain rule, into the `Rule.size` words at `rr`. -/
theorem rule_relP {m₀ : Mem} {a₀ : AState} {T : Nat} (seen : List ConLeche.Expr) (memo : EMemo)
    (rl : ConLeche.RecRule) (hfit : ruleFits rl = true) (hp : rl.fire = .plain) (k : Nat) (m : Mem) (a : AState)
    (q rr : Word) (rest : List UInt8) (r : List Word) (m' : Mem) (hI : RInv m₀ a₀ T m a)
    (hM : MemoR m seen memo) (hst : stkTop m = 0) (hd : rom.drop q.toNat = (encRule seen rl).1 ++ rest)
    (hc0 : erT m₀ ≤ rr.toNat) (hcS : rr.toNat + Rule.size.toNat ≤ erT m)
    (hc : callW p (k + 1) "rci_rule" [q, rr] m = some (r, m')) :
    ∃ (memo' : EMemo) (irl : IRecRule) (a' : AState),
      (Frontend.internRule memo rl).run a = .ok ((memo', irl), a') ∧
      RInv m₀ a₀ T m' a' ∧ MemoR m' (encRule seen rl).2 memo' ∧ stkTop m' = 0 ∧
      (r.headD 0).toNat = q.toNat + (encRule seen rl).1.length ∧
      EKeep (fun i => rr.toNat ≤ i ∧ i < rr.toNat + Rule.size.toNat) m m' ∧ erT m ≤ erT m' ∧
      m'.arr64 IW = m.arr64 IW ∧
      Holds (fun i => (rr.toNat ≤ i ∧ i < rr.toNat + Rule.size.toNat) ∨ (erT m ≤ i ∧ i < erT m')) (fun _ => False)
        (fun m => decRule (erA m) rr.toNat) m' irl := by
  simp only [ruleFits, Bool.and_eq_true, decide_eq_true_eq] at hfit
  obtain ⟨⟨⟨hfn, hnf⟩, -⟩, hfe⟩ := hfit
  obtain ⟨hd', hs2⟩ := encRule_eq seen rl hp rest
  rw [hd'] at hd
  have hlt := hI.er_lt
  have hgo := hI.erT_mono
  have hrom := hr; simp only [RomOK] at hrom
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := Rule.order
  have := Rule.size_le
  have hoff : ∀ f : Word, f.toNat < Rule.size.toNat → (rr + f).toNat = rr.toNat + f.toNat :=
    fun f hf => fld_toNat (by omega) (by omega)
  have hw := callW_model (M := fun mq => ruleW p k mq q rr) (rule_specW rom p hL k · q rr) hc
  unfold ruleW at hw
  -- the constructor's name
  obtain ⟨r1, m1, h1, hw⟩ := L.Ind.ntBW_some hw
  obtain ⟨a1, hrun1, hA1, hk1, hlt1, hq1, hf1, hmo1⟩ := nameCall hL hr _ hfn hI.arena hI.mode hd h1
  obtain ⟨hI1, -, -, hIW1, ht1, -, hE1⟩ := hI.expr hA1 hmo1 (hf1.mono (fun b hb => by simp [ExprA, RomA, hb])
    (fun x hx => by simp [ExprC, RomC, hx])) hk1 (L.Arena.internName_ks _ _ _ _ hrun1)
  have hM1 := hM.frameG hf1 (by decide) (by decide)
  have hs1 : stkTop m1 = stkTop m := hf1.ctl 131 (by decide)
  have hd1 : rom.drop (r1.tail.headD 0).toNat = u64B rl.nfields ++ (u64B 0 ++
      ((encExprM seen rl.rhs).1 ++ rest)) :=
    drop_shift rom q (encName rl.ctor) _ _ (by rw [hd, List.append_assoc]) _ hq1
  have hlen := drop_len rom _ (u64B rl.nfields ++ u64B 0) _ (by rw [hd1, List.append_assoc]) (by simp [u64B])
  simp only [u64B, List.length_append, List.length_cons, List.length_nil] at hlen
  have e1 := u64_at hr (r1.tail.headD 0) 0 [] rl.nfields _ (by rw [hd1]; rfl) (by simp) hnf
  simp only [UInt64.add_zero] at e1
  have e2 := u64_at hr (r1.tail.headD 0) 8 (u64B rl.nfields) 0 _ (by rw [hd1]) (by simp [u64B]) (by decide)
  replace hw := u64_some hL (putE_some hL hw)
  replace hw := u64_some hL (putE_some hL hw)
  rw [e1, e2] at hw
  replace hw := putE_some hL (putE_some hL (putE_some hL (putE_some hL (putE_some hL hw))))
  change (if (0 : Word) = 1 ∨ (0 : Word) = 2 then _ else
    ruleW.j1 p k (r1.tail.headD 0 + 16) rr 0 (putERs m1 [(rr, r1.headD 0), (rr + Rule.nfields, UInt64.ofNat rl.nfields),
      (rr + Rule.fire, 0), (rr + Rule.lvlsOff, 0), (rr + Rule.lvlsLen, 0), (rr + Rule.pinsOff, 0), (rr + Rule.pinsLen, 0)])) = some (r, m') at hw
  generalize hws : [(rr, r1.headD 0), (rr + Rule.nfields, UInt64.ofNat rl.nfields), ((rr + Rule.fire : Word), (0 : Word)),
    (rr + Rule.lvlsOff, 0), (rr + Rule.lvlsLen, 0), (rr + Rule.pinsOff, 0), (rr + Rule.pinsLen, 0)] = ws at hw
  have hwsB : ∀ jw ∈ ws, erT m₀ ≤ jw.1.toNat ∧ jw.1.toNat < erT m1 := by
    intro jw hjw; rw [← hws] at hjw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
    rcases hjw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> fld_omega
  have hws41 : ∀ jw ∈ ws, jw.1.toNat < 2 ^ 41 := fun jw h => by have := (hwsB jw h).2; omega
  obtain ⟨hI2, hM2, hs2', ht2, hIW2⟩ := putERs_facts ws m1 hI1 hM1 hwsB
  have hget : ∀ j w, (j, w) ∈ ws → erA (putERs m1 ws) j.toNat = some w := by
    intro j w hjw
    refine putERs_get ws m1 j w hI1 hwsB ?_ hjw
    rw [← hws]; simp (disch := omega) only [fld_toNat, List.map_cons, List.map_nil, List.nodup_cons,
      List.mem_cons, List.mem_nil_iff, List.nodup_nil, or_false, and_true, not_or, not_false_eq_true]
    repeat' apply And.intro
    all_goals omega
  -- the right-hand side
  rw [ite_eq_right (show ¬ ((0 : Word) = 1 ∨ (0 : Word) = 2) by decide)] at hw
  unfold ruleW.j1 at hw
  rw [ite_eq_right (show ¬ ((0 : Word) = 1) by decide)] at hw
  unfold ruleW.j2 at hw
  obtain ⟨r4, m4, h4, hw⟩ := L.Ind.ntBW_some hw
  have hq16 : (r1.tail.headD 0 + 16).toNat = (r1.tail.headD 0).toNat + 16 := by
    have := hq1; rw [UInt64.toNat_add]; simp at this ⊢; omega
  have hdr : rom.drop (r1.tail.headD 0 + 16).toNat = (encExprM seen rl.rhs).1 ++ rest := by
    rw [hq16, ← List.drop_drop, hd1]; simp [u64B]
  obtain ⟨memo', a4, hrun4, hA4, hk4, hM4, hlt4, hq4, hf4, hs4, hmo4⟩ :=
    exprCall hL hr rl.rhs hfe hI2.arena hI2.mode hM2 hdr (by rw [hs2', hs1, hst]; decide)
      (by have := hI2.ok.ctl; omega) h4
  obtain ⟨hI4, -, -, hIW4, ht4, -, hE4⟩ := hI2.expr hA4 hmo4 hf4 hk4
    (L.Arena.internExprGo_ks _ _ _ _ _ hrun4)
  obtain ⟨rb, m5, hb, hw⟩ := L.Ind.ntBW_some hw
  rw [putCall hL hb] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨hI5, hM5, hs5, ht5, hIW5, hg5, hn5⟩ :=
    putER_facts hI4 hM4 (rr + Rule.rhs) (r4.headD 0) (by fld_omega) (by fld_omega)
  -- the record's words: the first seven fields from `ws`, the right-hand side last
  have hrw : RuleRecW (erA (erecPutMem m4 (rr + Rule.rhs) (r4.headD 0))) rr.toNat (r1.headD 0)
      (UInt64.ofNat rl.nfields) 0 0 0 0 0 (r4.headD 0) := by
    have hword : ∀ (j w : Word), (j, w) ∈ ws → j.toNat ≠ (rr + Rule.rhs).toNat →
        erA (erecPutMem m4 (rr + Rule.rhs) (r4.headD 0)) j.toNat = some w := fun j w hjw hj => by
      have : j.toNat < erT m1 := (hwsB _ hjw).2
      rw [hn5 _ hj (by omega), hE4]; exact hget j w hjw
    have hR := hoff _ Rule.rhs_lt
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [← hR]; exact hg5⟩
    · rw [ctor_add]; exact hword rr _ (by rw [← hws]; simp) (by omega)
    · rw [← hoff _ Rule.nfields_lt]
      exact hword _ _ (by rw [← hws]; simp) (by rw [hoff _ Rule.nfields_lt, hR]; omega)
    · rw [← hoff _ Rule.fire_lt]
      exact hword _ _ (by rw [← hws]; simp) (by rw [hoff _ Rule.fire_lt, hR]; omega)
    · rw [← hoff _ Rule.lvlsOff_lt]
      exact hword _ _ (by rw [← hws]; simp) (by rw [hoff _ Rule.lvlsOff_lt, hR]; omega)
    · rw [← hoff _ Rule.lvlsLen_lt]
      exact hword _ _ (by rw [← hws]; simp) (by rw [hoff _ Rule.lvlsLen_lt, hR]; omega)
    · rw [← hoff _ Rule.pinsOff_lt]
      exact hword _ _ (by rw [← hws]; simp) (by rw [hoff _ Rule.pinsOff_lt, hR]; omega)
    · rw [← hoff _ Rule.pinsLen_lt]
      exact hword _ _ (by rw [← hws]; simp) (by rw [hoff _ Rule.pinsLen_lt, hR]; omega)
  refine ⟨memo', ⟨decI (r1.headD 0), rl.nfields, .plain, decI (r4.headD 0)⟩, a4, ?_, hI5, ?_,
    by rw [hs5, hs4, hs2', hs1, hst], ?_, ?_, by rw [ht5, ht4, ht2, ht1]; exact Nat.le_refl _,
    by rw [hIW5, hIW4, hIW2, hIW1], ?_⟩
  · simp only [Frontend.internRule]
    rw [run_bind_of _ _ _ _ _ hrun1, hp]
    simp only [Frontend.internFire, pure_bind]
    rw [run_bind_of _ _ _ _ _ hrun4]
    rfl
  · rw [hs2]; exact hM5
  · simp only [List.headD_cons]; rw [hq4, hq16, hq1]
    have := congrArg List.length hd'
    simp [u64B] at this ⊢; omega
  · refine ⟨by omega, fun i hi hR => ?_⟩
    rw [hn5 i (by fld_omega) (by fld_omega), hE4, putERs_ne ws m1 i (by
        intro jw hjw; rw [← hws] at hjw
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
        rcases hjw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> fld_omega) (by omega) hws41, hE1]
  · have hH := holds_decRule hrw hlt1 hlt4 rfl
    rw [L.toNat_ofNat_of_lt hnf] at hH
    exact hH.mono (fun i hi => .inl hi) (fun _ h => h)

set_option maxHeartbeats 1000000 in
/-- `rci_rule` for a rule firing at levels: the record at `rr`, the level slice allocated. -/
theorem rule_relL {m₀ : Mem} {a₀ : AState} {T : Nat} (seen : List ConLeche.Expr) (memo : EMemo)
    (rl : ConLeche.RecRule) (lvls : List ConLeche.Level) (hfit : ruleFits rl = true)
    (hp : rl.fire = .levels lvls) (k : Nat) (m : Mem) (a : AState)
    (q rr : Word) (rest : List UInt8) (r : List Word) (m' : Mem) (hI : RInv m₀ a₀ T m a)
    (hM : MemoR m seen memo) (hst : stkTop m = 0) (hd : rom.drop q.toNat = (encRule seen rl).1 ++ rest)
    (hc0 : erT m₀ ≤ rr.toNat) (hcS : rr.toNat + Rule.size.toNat ≤ erT m)
    (hc : callW p (k + 1) "rci_rule" [q, rr] m = some (r, m')) :
    ∃ (memo' : EMemo) (irl : IRecRule) (a' : AState),
      (Frontend.internRule memo rl).run a = .ok ((memo', irl), a') ∧
      RInv m₀ a₀ T m' a' ∧ MemoR m' (encRule seen rl).2 memo' ∧ stkTop m' = 0 ∧
      (r.headD 0).toNat = q.toNat + (encRule seen rl).1.length ∧
      EKeep (fun i => rr.toNat ≤ i ∧ i < rr.toNat + Rule.size.toNat) m m' ∧ erT m ≤ erT m' ∧
      m'.arr64 IW = m.arr64 IW ∧
      Holds (fun i => (rr.toNat ≤ i ∧ i < rr.toNat + Rule.size.toNat) ∨ (erT m ≤ i ∧ i < erT m')) (fun _ => False)
        (fun m => decRule (erA m) rr.toNat) m' irl := by
  simp only [ruleFits, Bool.and_eq_true, decide_eq_true_eq] at hfit
  obtain ⟨⟨⟨hfn, hnf⟩, hpl⟩, hfe⟩ := hfit
  rw [hp] at hpl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpl
  obtain ⟨hlf, hll⟩ := hpl
  obtain ⟨hd', hs2⟩ := encRule_eqL seen rl lvls hp rest
  rw [hd'] at hd
  have hlt := hI.er_lt
  have hgo := hI.erT_mono
  have hrom := hr; simp only [RomOK] at hrom
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := Rule.order
  have := Rule.size_le
  have hoff : ∀ f : Word, f.toNat < Rule.size.toNat → (rr + f).toNat = rr.toNat + f.toNat :=
    fun f hf => fld_toNat (by omega) (by omega)
  have hw := callW_model (M := fun mq => ruleW p k mq q rr) (rule_specW rom p hL k · q rr) hc
  unfold ruleW at hw
  -- the constructor's name
  obtain ⟨r1, m1, h1, hw⟩ := L.Ind.ntBW_some hw
  obtain ⟨a1, hrun1, hA1, hk1, hlt1, hq1, hf1, hmo1⟩ := nameCall hL hr _ hfn hI.arena hI.mode hd h1
  obtain ⟨hI1, -, -, hIW1, ht1, -, hE1⟩ := hI.expr hA1 hmo1 (hf1.mono (fun b hb => by simp [ExprA, RomA, hb])
    (fun x hx => by simp [ExprC, RomC, hx])) hk1 (L.Arena.internName_ks _ _ _ _ hrun1)
  have hM1 := hM.frameG hf1 (by decide) (by decide)
  have hs1 : stkTop m1 = stkTop m := hf1.ctl 131 (by decide)
  have hd1 : rom.drop (r1.tail.headD 0).toNat = u64B rl.nfields ++ (u64B 2 ++
      (u64B lvls.length ++ (encLevelList lvls ++ ((encExprM seen rl.rhs).1 ++ rest)))) :=
    drop_shift rom q (encName rl.ctor) _ _ (by rw [hd, List.append_assoc]) _ hq1
  have hlen := drop_len rom _ (u64B rl.nfields ++ u64B 2 ++ u64B lvls.length) _
    (by rw [hd1]; repeat rw [List.append_assoc]) (by simp [u64B])
  simp only [u64B, List.length_append, List.length_cons, List.length_nil] at hlen
  have e1 := u64_at hr (r1.tail.headD 0) 0 [] rl.nfields _ (by rw [hd1]; rfl) (by simp) hnf
  simp only [UInt64.add_zero] at e1
  have e2 := u64_at hr (r1.tail.headD 0) 8 (u64B rl.nfields) 2 _ (by rw [hd1]) (by simp [u64B]) (by decide)
  replace hw := u64_some hL (putE_some hL hw)
  replace hw := u64_some hL (putE_some hL hw)
  rw [e1, e2] at hw
  replace hw := putE_some hL (putE_some hL (putE_some hL (putE_some hL (putE_some hL hw))))
  change (if UInt64.ofNat 2 = 1 ∨ UInt64.ofNat 2 = 2 then
    ntBW (callW p k "rom_u64_c" [r1.tail.headD 0 + 16] (putERs m1 [(rr, r1.headD 0),
      (rr + Rule.nfields, UInt64.ofNat rl.nfields), (rr + Rule.fire, UInt64.ofNat 2), (rr + Rule.lvlsOff, 0), (rr + Rule.lvlsLen, 0), (rr + Rule.pinsOff, 0),
      (rr + Rule.pinsLen, 0)])) _ else _) = some (r, m') at hw
  generalize hws : [(rr, r1.headD 0), (rr + Rule.nfields, UInt64.ofNat rl.nfields), ((rr + Rule.fire : Word), UInt64.ofNat 2),
    (rr + Rule.lvlsOff, (0 : Word)), (rr + Rule.lvlsLen, 0), (rr + Rule.pinsOff, 0), (rr + Rule.pinsLen, 0)] = ws at hw
  have hwsB : ∀ jw ∈ ws, erT m₀ ≤ jw.1.toNat ∧ jw.1.toNat < erT m1 := by
    intro jw hjw; rw [← hws] at hjw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
    rcases hjw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> fld_omega
  have hws41 : ∀ jw ∈ ws, jw.1.toNat < 2 ^ 41 := fun jw h => by have := (hwsB jw h).2; omega
  obtain ⟨hI2, hM2, hs2', ht2, hIW2⟩ := putERs_facts ws m1 hI1 hM1 hwsB
  have hget : ∀ j w, (j, w) ∈ ws → erA (putERs m1 ws) j.toNat = some w := by
    intro j w hjw
    refine putERs_get ws m1 j w hI1 hwsB ?_ hjw
    rw [← hws]; simp (disch := omega) only [fld_toNat, List.map_cons, List.map_nil, List.nodup_cons,
      List.mem_cons, List.mem_nil_iff, List.nodup_nil, or_false, and_true, not_or, not_false_eq_true]
    repeat' apply And.intro
    all_goals omega
  -- the level slice
  rw [ite_eq_left (show (UInt64.ofNat 2 = 1 ∨ UInt64.ofNat 2 = 2) by decide)] at hw
  replace hw := u64_some hL hw
  simp only [List.headD_cons] at hw
  have hq16 : (r1.tail.headD 0 + 16).toNat = (r1.tail.headD 0).toNat + 16 := by
    have := hq1; rw [UInt64.toNat_add]; simp at this ⊢; omega
  have e3 := u64_at hr (r1.tail.headD 0) 16 (u64B rl.nfields ++ u64B 2) lvls.length _
    (by rw [hd1]; repeat rw [List.append_assoc]) (by simp [u64B]) (by omega)
  rw [e3] at hw
  have hlN : (UInt64.ofNat lvls.length).toNat = lvls.length := L.toNat_ofNat_of_lt (by omega)
  cases ha : callW p k "erec_alloc" [UInt64.ofNat lvls.length] (putERs m1 ws) with
  | none => rw [ha] at hw; simp at hw
  | some ta =>
  obtain ⟨ra, ma⟩ := ta
  rw [ha, bW_some] at hw
  obtain ⟨hIa, hoa, hta, -, -, hIWa, -, -, hka⟩ := hI2.erAlloc (erAllocCall hL ha)
  rw [hlN] at hta
  have hfa : MemFrame [] [129, 130] (putERs m1 ws) ma := (erAllocW_spec (erAllocCall hL ha) hI2.ok).2.1
  have hMa := hM2.frameG hfa (by simp) (by decide)
  have hsa : stkTop ma = stkTop (putERs m1 ws) := hfa.ctl 131 (by decide)
  replace hw := putE_some hL (putE_some hL hw)
  change ntBW (callW p k "rci_lvls_to" [r1.tail.headD 0 + 16 + 8, ra.headD 0, UInt64.ofNat lvls.length]
    (putERs ma [(rr + Rule.lvlsOff, ra.headD 0), (rr + Rule.lvlsLen, UInt64.ofNat lvls.length)])) _ = _ at hw
  generalize hws2 : [(rr + Rule.lvlsOff, ra.headD 0), (rr + Rule.lvlsLen, UInt64.ofNat lvls.length)] = ws2 at hw
  have hwsB2 : ∀ jw ∈ ws2, erT m₀ ≤ jw.1.toNat ∧ jw.1.toNat < erT ma := by
    intro jw hjw; rw [← hws2] at hjw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
    rcases hjw with rfl | rfl <;> constructor <;> fld_omega
  have hlta := hIa.er_lt
  have hws41' : ∀ jw ∈ ws2, jw.1.toNat < 2 ^ 41 := fun jw h => by have := (hwsB2 jw h).2; omega
  obtain ⟨hIb, hMb, hsb, htb, hIWb⟩ := putERs_facts ws2 ma hIa hMa hwsB2
  have hget2 : ∀ j w, (j, w) ∈ ws2 → erA (putERs ma ws2) j.toNat = some w := by
    intro j w hjw
    refine putERs_get ws2 ma j w hIa hwsB2 ?_ hjw
    rw [← hws2]; simp (disch := omega) only [fld_toNat, List.map_cons, List.map_nil, List.nodup_cons,
      List.mem_cons, List.mem_nil_iff, List.nodup_nil, or_false, and_true, not_false_eq_true]
    repeat' apply And.intro
    all_goals omega
  cases hl : callW p k "rci_lvls_to" [r1.tail.headD 0 + 16 + 8, ra.headD 0, UInt64.ofNat lvls.length]
      (putERs ma ws2) with
  | none => rw [hl] at hw; simp at hw
  | some tl =>
  obtain ⟨r2, m2⟩ := tl
  rw [hl, bW_some] at hw
  unfold ruleW.j1 at hw
  rw [ite_eq_right (show ¬ (UInt64.ofNat 2 = 1) by decide)] at hw
  unfold ruleW.j2 at hw
  have hq24 : (r1.tail.headD 0 + 16 + 8).toNat = (r1.tail.headD 0).toNat + 24 := by
    have := hq1; rw [UInt64.toNat_add, hq16]; simp at this ⊢; omega
  have hdl : rom.drop (r1.tail.headD 0 + 16 + 8).toNat = encLevelList lvls ++ ((encExprM seen rl.rhs).1 ++ rest) := by
    rw [hq24, ← List.drop_drop, hd1]; simp [u64B]
  obtain ⟨wl, a3, hrun3, hwl, hwlt, hwd, hI3, hM3, hs3, hq3, hek3, ht3, hiw3⟩ :=
    lvlsTo_rel hL hr seen memo lvls hlf k _ a1 _ (ra.headD 0) _ _ r2 m2 hIb hMb hdl hlN (by omega)
      (by omega) hl
  -- the right-hand side
  obtain ⟨r4, m4, h4, hw⟩ := L.Ind.ntBW_some hw
  have hdr : rom.drop (r2.headD 0).toNat = (encExprM seen rl.rhs).1 ++ rest :=
    drop_shift rom _ (encLevelList lvls) _ _ (by rw [hdl, List.append_assoc]) _ hq3
  obtain ⟨memo', a4, hrun4, hA4, hk4, hM4, hlt4, hq4, hf4, hs4, hmo4⟩ :=
    exprCall hL hr rl.rhs hfe hI3.arena hI3.mode hM3 hdr (by rw [hs3, hsb, hsa, hs2', hs1, hst]; decide)
      (by have := hI3.ok.ctl; omega) h4
  obtain ⟨hI4, -, -, hIW4, ht4, -, hE4⟩ := hI3.expr hA4 hmo4 hf4 hk4
    (L.Arena.internExprGo_ks _ _ _ _ _ hrun4)
  obtain ⟨rb, m5, hb, hw⟩ := L.Ind.ntBW_some hw
  rw [putCall hL hb] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨hI5, hM5, hs5, ht5, hIW5, hg5, hn5⟩ :=
    putER_facts hI4 hM4 (rr + Rule.rhs) (r4.headD 0) (by fld_omega) (by fld_omega)
  -- below the slice, the record's words through the slice and the rhs
  have hR := hoff _ Rule.rhs_lt
  have hLo := hoff _ Rule.lvlsOff_lt
  have hLl := hoff _ Rule.lvlsLen_lt
  have hthrough : ∀ i, i < erT m → i ≠ rr.toNat + Rule.rhs.toNat →
      erA (erecPutMem m4 (rr + Rule.rhs) (r4.headD 0)) i = erA (putERs ma ws2) i := fun i hi h8 => by
    rw [hn5 i (by rw [hR]; exact h8) (by omega), hE4, hek3.2 i (by omega) (by omega)]
  have hne2 : ∀ i, i < erT m → i ≠ rr.toNat + Rule.lvlsOff.toNat → i ≠ rr.toNat + Rule.lvlsLen.toNat →
      erA (putERs ma ws2) i = erA (putERs m1 ws) i := fun i hi h4' h5' => by
    rw [putERs_ne ws2 ma i (by
      intro jw hjw; rw [← hws2] at hjw
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
      rcases hjw with rfl | rfl <;> fld_omega) (by omega) hws41', hka i (by omega)]
  -- the record's words: the fields from `ws` (the level slice's from `ws2`), the right-hand side last
  have hrw : RuleRecW (erA (erecPutMem m4 (rr + Rule.rhs) (r4.headD 0))) rr.toNat (r1.headD 0)
      (UInt64.ofNat rl.nfields) (UInt64.ofNat 2) (ra.headD 0) (UInt64.ofNat lvls.length) 0 0 (r4.headD 0) := by
    have hword : ∀ (j w : Word), (j, w) ∈ ws → j.toNat ≠ rr.toNat + Rule.rhs.toNat →
        j.toNat ≠ rr.toNat + Rule.lvlsOff.toNat → j.toNat ≠ rr.toNat + Rule.lvlsLen.toNat →
        erA (erecPutMem m4 (rr + Rule.rhs) (r4.headD 0)) j.toNat = some w := fun j w hjw h1 h2 h3 => by
      have : j.toNat < erT m1 := (hwsB _ hjw).2
      rw [hthrough _ (by omega) h1, hne2 _ (by omega) h2 h3]; exact hget j w hjw
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [← hR]; exact hg5⟩
    · rw [ctor_add]; exact hword rr _ (by rw [← hws]; simp) (by omega) (by omega) (by omega)
    · rw [← hoff _ Rule.nfields_lt]
      exact hword _ _ (by rw [← hws]; simp) (by fld_omega) (by fld_omega) (by fld_omega)
    · rw [← hoff _ Rule.fire_lt]
      exact hword _ _ (by rw [← hws]; simp) (by fld_omega) (by fld_omega) (by fld_omega)
    · rw [hthrough _ (by omega) (by omega), ← hLo]
      exact hget2 _ _ (by rw [← hws2]; simp)
    · rw [hthrough _ (by omega) (by omega), ← hLl]
      exact hget2 _ _ (by rw [← hws2]; simp)
    · rw [← hoff _ Rule.pinsOff_lt]
      exact hword _ _ (by rw [← hws]; simp) (by fld_omega) (by fld_omega) (by fld_omega)
    · rw [← hoff _ Rule.pinsLen_lt]
      exact hword _ _ (by rw [← hws]; simp) (by fld_omega) (by fld_omega) (by fld_omega)
  refine ⟨memo', ⟨decI (r1.headD 0), rl.nfields, .levels (wl.map decI), decI (r4.headD 0)⟩, a4, ?_, hI5, ?_,
    by rw [hs5, hs4, hs3, hsb, hsa, hs2', hs1, hst], ?_, ?_, by omega,
    by rw [hIW5, hIW4, hiw3, hIWb, hIWa, hIW2, hIW1], ?_⟩
  · simp only [Frontend.internRule]
    rw [run_bind_of _ _ _ _ _ hrun1, hp]
    simp only [Frontend.internFire, bind_assoc, pure_bind]
    rw [run_bind_of _ _ _ _ _ hrun3, run_bind_of _ _ _ _ _ hrun4]
    rfl
  · rw [hs2]; exact hM5
  · simp only [List.headD_cons]; rw [hq4, hq3, hq24, hq1]
    have := congrArg List.length hd'
    simp [u64B] at this ⊢; omega
  · refine ⟨by omega, fun i hi hR => ?_⟩
    rw [hthrough i hi (by omega), hne2 i hi (by omega) (by omega), putERs_ne ws m1 i (by
        intro jw hjw; rw [← hws] at hjw
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
        rcases hjw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> fld_omega) (by omega) hws41, hE1]
  · have hWs : ∀ j (hj : j < wl.length), erA (erecPutMem m4 (rr + Rule.rhs) (r4.headD 0))
        ((ra.headD 0).toNat + j) = some wl[j] := fun j hj => by
      have := hwlt; have := hwl; have := hI3.er_lt
      rw [hn5 _ (by fld_omega) (by omega), hE4]; exact hwd j hj
    have hH := holds_decRuleL wl hrw hlt1 hlt4 (by decide) (by rw [hlN, hwl]) hWs hwlt
    rw [L.toNat_ofNat_of_lt hnf] at hH
    refine hH.mono (fun i hi => ?_) (fun _ h => h)
    rcases hi with hi | hi
    · left; exact hi
    · right; omega

/-- **`rci_rule` refines `Frontend.internRule`** for the rules `ruleFits` admits (plain, or firing
at levels), into the `Rule.size` words at `rr`. -/
@[refines_part ConRon.Arena.Frontend.internRule "plain rules and rules firing at levels"]
theorem rule_rel {m₀ : Mem} {a₀ : AState} {T : Nat} (seen : List ConLeche.Expr) (memo : EMemo)
    (rl : ConLeche.RecRule) (hfit : ruleFits rl = true) (k : Nat) (m : Mem) (a : AState)
    (q rr : Word) (rest : List UInt8) (r : List Word) (m' : Mem) (hI : RInv m₀ a₀ T m a)
    (hM : MemoR m seen memo) (hst : stkTop m = 0) (hd : rom.drop q.toNat = (encRule seen rl).1 ++ rest)
    (hc0 : erT m₀ ≤ rr.toNat) (hcS : rr.toNat + Rule.size.toNat ≤ erT m)
    (hc : callW p (k + 1) "rci_rule" [q, rr] m = some (r, m')) :
    ∃ (memo' : EMemo) (irl : IRecRule) (a' : AState),
      (Frontend.internRule memo rl).run a = .ok ((memo', irl), a') ∧
      RInv m₀ a₀ T m' a' ∧ MemoR m' (encRule seen rl).2 memo' ∧ stkTop m' = 0 ∧
      (r.headD 0).toNat = q.toNat + (encRule seen rl).1.length ∧
      EKeep (fun i => rr.toNat ≤ i ∧ i < rr.toNat + Rule.size.toNat) m m' ∧ erT m ≤ erT m' ∧
      m'.arr64 IW = m.arr64 IW ∧
      Holds (fun i => (rr.toNat ≤ i ∧ i < rr.toNat + Rule.size.toNat) ∨ (erT m ≤ i ∧ i < erT m')) (fun _ => False)
        (fun m => decRule (erA m) rr.toNat) m' irl := by
  have hf := hfit
  simp only [ruleFits, Bool.and_eq_true] at hf
  cases e : rl.fire with
  | plain => exact rule_relP hL hr seen memo rl hfit e k m a q rr rest r m' hI hM hst hd hc0 hcS hc
  | levels lvls => exact rule_relL hL hr seen memo rl lvls hfit e k m a q rr rest r m' hI hM hst hd hc0 hcS hc
  | nested lvls pins => rw [e] at hf; simp at hf

end rule

section rules
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

/-- **`rci_rules_to` refines `Frontend.internRules`**, into the `Rule.size`-word records at `o`,
`o + Rule.size`, …. -/
@[refines_part ConRon.Arena.Frontend.internRules "plain rules"]
theorem rulesTo_rel {m₀ : Mem} {a₀ : AState} {T : Nat} :
    ∀ (rs : List ConLeche.RecRule), rs.all ruleFits = true → ∀ (seen : List ConLeche.Expr) (memo : EMemo)
      (k : Nat) (m : Mem) (a : AState) (q o kw : Word) (rest : List UInt8) (r : List Word) (m' : Mem),
      RInv m₀ a₀ T m a → MemoR m seen memo → stkTop m = 0 →
      rom.drop q.toNat = (encRules seen rs).1 ++ rest → kw.toNat = rs.length →
      erT m₀ ≤ o.toNat → o.toNat + Rule.size.toNat * rs.length ≤ erT m →
      callW p k "rci_rules_to" [q, o, kw] m = some (r, m') →
      ∃ (memo' : EMemo) (irs : List IRecRule) (a' : AState),
        (Frontend.internRules memo rs).run a = .ok ((memo', irs), a') ∧ irs.length = rs.length ∧
        RInv m₀ a₀ T m' a' ∧ MemoR m' (encRules seen rs).2 memo' ∧ stkTop m' = 0 ∧
        (r.headD 0).toNat = q.toNat + (encRules seen rs).1.length ∧
        EKeep (fun i => o.toNat ≤ i ∧ i < o.toNat + Rule.size.toNat * rs.length) m m' ∧ erT m ≤ erT m' ∧
        m'.arr64 IW = m.arr64 IW ∧
        ∀ j (hj : j < irs.length), Holds (fun i => (o.toNat + Rule.size.toNat * j ≤ i ∧
          i < o.toNat + Rule.size.toNat * j + Rule.size.toNat) ∨
          (erT m ≤ i ∧ i < erT m'))
          (fun _ => False) (fun m => decRule (erA m) (o.toNat + Rule.size.toNat * j)) m' irs[j] := by
  intro rs
  induction rs with
  | nil =>
    intro _ seen memo k m a q o kw rest r m' hI hM hst hd hk ho hot hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mq => rulesToW p k mq q o kw) (rulesTo_specW rom p hL k · q o kw) hc
    have hk0 : kw = 0 := by apply UInt64.toNat_inj.mp; simpa using hk
    simp only [rulesToW, hk0, ite_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨memo, [], a, rfl, rfl, hI, hM, hst, by simp [encRules], EKeep.refl _ _, Nat.le_refl _, rfl,
      fun j hj => by simp at hj⟩
  | cons rl rs ih =>
    intro hfit seen memo k m a q o kw rest r m' hI hM hst hd hk ho hot hc
    simp only [List.all_cons, Bool.and_eq_true] at hfit
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mq => rulesToW p k mq q o kw) (rulesTo_specW rom p hL k · q o kw) hc
    have hk0 : kw ≠ 0 := fun h => by subst h; simp at hk
    simp only [rulesToW, hk0, ite_false] at hw
    cases k with
    | zero => rw [callW_zero] at hw; simp at hw
    | succ k =>
    obtain ⟨r1, m1, h1, hw⟩ := L.Ind.ntBW_some hw
    simp only [List.length_cons, Nat.mul_add_one] at hot hk ⊢
    have hd0 : rom.drop q.toNat = (encRule seen rl).1 ++ ((encRules (encRule seen rl).2 rs).1 ++ rest) := by
      rw [hd]; simp [encRules, List.append_assoc]
    obtain ⟨memo1, irl, a1, hrun1, hI1, hM1, hs1, hq1, hek1, ht1, hIW1, hH1⟩ :=
      rule_rel hL hr seen memo rl hfit.1 k m a q o _ _ m1 hI hM hst hd0 ho (by omega) h1
    have hlt := hI.er_lt
    have := Rule.size_le
    have ho11 : (o + Rule.size).toNat = o.toNat + Rule.size.toNat := fld_toNat (by omega) (by omega)
    have hk1' : (kw - 1).toNat = rs.length := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    obtain ⟨r2, m2, h2, hw⟩ := L.Ind.ntBW_some hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hd1 : rom.drop (r1.headD 0).toNat = (encRules (encRule seen rl).2 rs).1 ++ rest :=
      drop_shift rom q _ _ _ (by rw [hd0, List.append_assoc]) _ hq1
    obtain ⟨memo2, irs, a2, hrun2, hlen2, hI2, hM2, hs2, hq2, hek2, ht2, hIW2, hH2⟩ :=
      ih hfit.2 _ memo1 (k + 1) m1 a1 _ (o + Rule.size) (kw - 1) rest r2 m2 hI1 hM1 hs1 hd1 hk1'
        (by omega) (by omega) h2
    refine ⟨memo2, irl :: irs, a2, ?_, by simp [hlen2], hI2, ?_, hs2, ?_, ?_, by omega,
      by rw [hIW2, hIW1], ?_⟩
    · simp only [Frontend.internRules]
      rw [run_bind_of _ _ _ _ _ hrun1, run_bind_of _ _ _ _ _ hrun2]
      rfl
    · simpa [encRules] using hM2
    · simp only [List.headD_cons]; rw [hq2, hq1]; simp [encRules]; omega
    · rw [ho11] at hek2
      exact (hek1.mono fun i hi => ⟨by omega, by omega⟩).trans
        (hek2.mono fun i hi => ⟨by omega, by omega⟩)
    · intro j hj
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero]
        exact (hH1.ekeep hek2 (fun i hi => ⟨by omega, by omega⟩) hIW2).mono (fun i hi => by omega)
          (fun _ h => h)
      | succ j =>
        simp only [List.getElem_cons_succ]
        have := hH2 j (by simp at hj; omega)
        rw [ho11] at this
        have e : o.toNat + Rule.size.toNat + Rule.size.toNat * j = o.toNat + Rule.size.toNat * (j + 1) := by
          rw [Nat.mul_add_one]; omega
        rw [e] at this
        exact this.mono (fun i hi => by omega) (fun _ h => h)

end rules

end L.Rom
