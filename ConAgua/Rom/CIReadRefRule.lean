import ConAgua.Rom.CIReadRefCaps
import ConAgua.Census.Attr

/-!
# The ROM constant readers: recursor rules (helper `decls4-rom`)

`rci_rule(q, r)` refines `Frontend.internRule` for a plain rule (no pinned constant ROM rule is
nested), into the 11-word record at `r` (`decRule`); `rci_rules_to(q, o, k)` refines
`Frontend.internRules` into consecutive records (`decRules`).
-/


open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-- A list decoded index by index. -/
theorem holds_mapM_range {α : Type} [Inhabited α] {SE SI : Nat → Prop} {g : Mem → Nat → Option α} {m : Mem}
    (xs : List α) (h : ∀ j (hj : j < xs.length), Holds SE SI (fun m => g m j) m xs[j]) :
    Holds SE SI (fun m => (List.range xs.length).mapM (g m)) m xs := by
  intro m' h1 h2
  show List.mapM (g m') (List.range xs.length) = some xs
  rw [rmapM_some_of _ (fun j => xs.getD j default) _ (fun j hj => by
    have hj' := List.mem_range.mp hj
    have := h j hj' m' h1 h2
    simp only at this
    rw [this]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'])]
  congr 1
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h2)]

/-- `decRule` of a plain rule from its words. -/
theorem holds_decRule {m : Mem} {q : Nat} (irl : IRecRule) (wc wnf wcp wf wrhs wk weta : Word)
    (h0 : (erA m)[q]? = some wc) (h1 : (erA m)[q + 1]? = some wnf) (h2 : (erA m)[q + 2]? = some wcp)
    (h3 : (erA m)[q + 3]? = some wf) (h8 : (erA m)[q + 8]? = some wrhs)
    (h9 : (erA m)[q + 9]? = some wk) (h10 : (erA m)[q + 10]? = some weta)
    (hc : wc.toNat < 2 ^ 32) (hr : wrhs.toNat < 2 ^ 32) (hf : wf.toNat = 0)
    (ec : irl.ctor = decI wc) (enf : irl.nfields = wnf.toNat) (ecp : irl.ctorParams = wcp.toNat)
    (efi : irl.fire = .plain) (er : irl.rhs = decI wrhs) (ek : irl.k = (wk != 0))
    (eeta : irl.eta = (weta != 0)) :
    Holds (fun i => q ≤ i ∧ i < q + 11) (fun _ => False) (fun m => decRule (erA m) q) m irl := by
  intro m' hE _
  have g : ∀ i, i < 11 → (erA m')[q + i]? = (erA m)[q + i]? := fun i hi => hE _ ⟨by omega, by omega⟩
  have e0 := (g 0 (by omega)).trans h0
  have e1 := (g 1 (by omega)).trans h1
  have e2 := (g 2 (by omega)).trans h2
  have e3 := (g 3 (by omega)).trans h3
  have e8 := (g 8 (by omega)).trans h8
  have e9 := (g 9 (by omega)).trans h9
  have e10 := (g 10 (by omega)).trans h10
  simp only [Nat.add_zero] at e0
  have : irl = ⟨decI wc, wnf.toNat, wcp.toNat, .plain, decI wrhs, wk != 0, weta != 0⟩ := by
    cases irl; simp_all
  rw [this]
  simp [decRule, nat?_of e3, hf, hd?, e0, hc, nat?_of e1, nat?_of e2, e8, hr, bool?_of e9,
    bool?_of e10]

/-- A plain rule that fits its encoding. -/
def ruleFits (rl : ConLeche.RecRule) : Bool :=
  nameFits rl.ctor && decide (rl.nfields < 2 ^ 64) && decide (rl.ctorParams < 2 ^ 64) &&
    (match rl.fire with | .plain => true | .nested _ _ => false) && exprFits rl.rhs

theorem encRule_eq (seen : List ConLeche.Expr) (rl : ConLeche.RecRule) (hp : rl.fire = .plain)
    (rest : List UInt8) :
    (encRule seen rl).1 ++ rest = encName rl.ctor ++ (u64B rl.nfields ++ (u64B rl.ctorParams ++
      (u64B (if rl.k then 1 else 0) ++ (u64B (if rl.eta then 1 else 0) ++ (u64B 0 ++
      ((encExprM seen rl.rhs).1 ++ rest)))))) ∧ (encRule seen rl).2 = (encExprM seen rl.rhs).2 := by
  simp [encRule, hp, bw, List.append_assoc]

section rule
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

set_option maxHeartbeats 8000000 in
/-- **`rci_rule` refines `Frontend.internRule`** for a plain rule, into the 11 words at `rr`. -/
@[refines_part ConRon.Arena.Frontend.internRule "plain rules"]
theorem rule_rel {m₀ : Mem} {a₀ : AState} {T : Nat} (seen : List ConLeche.Expr) (memo : EMemo)
    (rl : ConLeche.RecRule) (hfit : ruleFits rl = true) (k : Nat) (m : Mem) (a : AState)
    (q rr : Word) (rest : List UInt8) (r : List Word) (m' : Mem) (hI : RInv m₀ a₀ T m a)
    (hM : MemoR m seen memo) (hst : stkTop m = 0) (hd : rom.drop q.toNat = (encRule seen rl).1 ++ rest)
    (hc0 : erTop m₀ ≤ rr.toNat) (hc11 : rr.toNat + 11 ≤ erTop m)
    (hc : callW p (k + 1) "rci_rule" [q, rr] m = some (r, m')) :
    ∃ (memo' : EMemo) (irl : IRecRule) (a' : AState),
      (Frontend.internRule memo rl).run a = .ok ((memo', irl), a') ∧
      RInv m₀ a₀ T m' a' ∧ MemoR m' (encRule seen rl).2 memo' ∧ stkTop m' = 0 ∧
      (r.headD 0).toNat = q.toNat + (encRule seen rl).1.length ∧
      EKeep (fun i => rr.toNat ≤ i ∧ i < rr.toNat + 11) m m' ∧ erTop m' = erTop m ∧
      m'.arr64 IW = m.arr64 IW ∧
      Holds (fun i => rr.toNat ≤ i ∧ i < rr.toNat + 11) (fun _ => False)
        (fun m => decRule (erA m) rr.toNat) m' irl := by
  simp only [ruleFits, Bool.and_eq_true, decide_eq_true_eq] at hfit
  obtain ⟨⟨⟨⟨hfn, hnf⟩, hcp⟩, hfp⟩, hfe⟩ := hfit
  have hp : rl.fire = .plain := by revert hfp; cases rl.fire <;> simp
  obtain ⟨hdeq, hseen⟩ := encRule_eq seen rl hp rest
  have hd' := hd.trans hdeq
  have hlt := hI.er_lt
  have hgo := hI.grow.2.1
  have hrom := hr; simp only [RomOK] at hrom
  have hc1 : (rr + 1).toNat = rr.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hc2 : (rr + 2).toNat = rr.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have hc3 : (rr + 3).toNat = rr.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have hc4 : (rr + 4).toNat = rr.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have hc5 : (rr + 5).toNat = rr.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
  have hc6 : (rr + 6).toNat = rr.toNat + 6 := by rw [UInt64.toNat_add]; simp; omega
  have hc7 : (rr + 7).toNat = rr.toNat + 7 := by rw [UInt64.toNat_add]; simp; omega
  have hc8 : (rr + 8).toNat = rr.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have hc9 : (rr + 9).toNat = rr.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have hc10 : (rr + 10).toNat = rr.toNat + 10 := by rw [UInt64.toNat_add]; simp; omega
  have hw := callW_model (M := fun mq => ruleW p k mq q rr) (rule_specW rom p hL k · q rr) hc
  unfold ruleW at hw
  obtain ⟨r1, m1, h1, hw⟩ := ntBW_inv hw
  obtain ⟨a1, hrun1, hA1, hk1, hlt1, hq1, hf1, hmo1⟩ := nameCall hL hr _ hfn hI.arena hI.mode hd' h1
  obtain ⟨hI1, hE1, hIW1, ht1, -⟩ := hI.expr hA1 hmo1 (hf1.mono (fun b hb => by simp [ExprA, RomA, hb])
    (fun x hx => by simp [ExprC, RomC, hx])) hk1
  have hM1 := hM.frameG hf1 (by decide) (by decide)
  have hs1 : stkTop m1 = stkTop m := hf1.2.1 131 (by decide)
  replace hw := rdU_some hL hw; replace hw := rdU_some hL hw; replace hw := rdU_some hL hw
  replace hw := rdU_some hL hw; replace hw := rdU_some hL hw
  have hd1 : rom.drop (r1.tail.headD 0).toNat = u64B rl.nfields ++ (u64B rl.ctorParams ++
      (u64B (if rl.k then 1 else 0) ++ (u64B (if rl.eta then 1 else 0) ++ (u64B 0 ++
      ((encExprM seen rl.rhs).1 ++ rest))))) :=
    by rw [hq1, ← List.drop_drop, hd', List.drop_left]
  have hb : ∀ b : Bool, (if b then 1 else 0) < 2 ^ 64 := fun b => by cases b <;> decide
  have e1 := u64_at hr (r1.tail.headD 0) 0 [] _ _ (by rw [hd1]; rfl) (by simp) hnf
  simp only [UInt64.add_zero] at e1
  have e2 := u64_at hr (r1.tail.headD 0) 8 (u64B rl.nfields) _ _ (by rw [hd1]) (by simp [u64B]) hcp
  have e3 := u64_at hr (r1.tail.headD 0) 16 (u64B rl.nfields ++ u64B rl.ctorParams)
    (if rl.k then 1 else 0) _ (by rw [hd1]; repeat rw [List.append_assoc]) (by simp [u64B]) (hb _)
  have e4 := u64_at hr (r1.tail.headD 0) 24 (u64B rl.nfields ++ u64B rl.ctorParams ++
    u64B (if rl.k then 1 else 0)) (if rl.eta then 1 else 0) _ (by rw [hd1]; repeat rw [List.append_assoc])
    (by simp [u64B]) (hb _)
  have e5 := u64_at hr (r1.tail.headD 0) 32 (u64B rl.nfields ++ u64B rl.ctorParams ++
    u64B (if rl.k then 1 else 0) ++ u64B (if rl.eta then 1 else 0)) 0 _
    (by rw [hd1]; repeat rw [List.append_assoc]) (by simp [u64B]) (by decide)
  rw [e1, e2, e3, e4, e5] at hw
  generalize hvk : UInt64.ofNat (if rl.k then 1 else 0) = vk at hw
  generalize hve : UInt64.ofNat (if rl.eta then 1 else 0) = ve at hw
  change ruleW.ruleTailW p k (setERs m1 [(rr, r1.headD 0), (rr + 1, UInt64.ofNat rl.nfields),
    (rr + 2, UInt64.ofNat rl.ctorParams), (rr + 9, vk), (rr + 10, ve), (rr + 3, UInt64.ofNat 0),
    (rr + 4, 0), (rr + 5, 0), (rr + 6, 0), (rr + 7, 0)]) (r1.tail.headD 0 + 40) rr (UInt64.ofNat 0) =
    some (r, m') at hw
  generalize hws : [(rr, r1.headD 0), (rr + 1, UInt64.ofNat rl.nfields),
    (rr + 2, UInt64.ofNat rl.ctorParams), (rr + 9, vk), (rr + 10, ve), (rr + 3, UInt64.ofNat 0),
    (rr + 4, (0 : Word)), (rr + 5, 0), (rr + 6, 0), (rr + 7, 0)] = ws at hw
  have hmemws : ∀ jw ∈ ws, ∃ i, i < 11 ∧ i ≠ 8 ∧ jw.1.toNat = rr.toNat + i := by
    intro jw hjw; rw [← hws] at hjw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
    rcases hjw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by omega, by omega, by simp⟩
    · exact ⟨1, by omega, by omega, hc1⟩
    · exact ⟨2, by omega, by omega, hc2⟩
    · exact ⟨9, by omega, by omega, hc9⟩
    · exact ⟨10, by omega, by omega, hc10⟩
    · exact ⟨3, by omega, by omega, hc3⟩
    · exact ⟨4, by omega, by omega, hc4⟩
    · exact ⟨5, by omega, by omega, hc5⟩
    · exact ⟨6, by omega, by omega, hc6⟩
    · exact ⟨7, by omega, by omega, hc7⟩
  obtain ⟨hI2, hM2, hs2, ht2, hIW2, -, hsz2⟩ := setERs_facts ws m1 hI1 hM1 (fun jw hjw => by
    obtain ⟨i, -, -, h⟩ := hmemws jw hjw; omega)
  unfold ruleW.ruleTailW at hw
  rw [ite_eq_right (by decide), bW_some] at hw
  simp only [List.headD_cons] at hw
  have hq40 : (r1.tail.headD 0 + 40).toNat = (r1.tail.headD 0).toNat + 40 := by
    have := drop_len rom (r1.tail.headD 0).toNat (u64B rl.nfields) _ hd1 (by simp [u64B])
    simp only [u64B, List.length_cons, List.length_nil] at this
    rw [UInt64.toNat_add, show (40 : Word).toNat = 40 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨r3, m3, h3, hw⟩ := ntBW_inv hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hd3 : rom.drop (r1.tail.headD 0 + 40).toNat = (encExprM seen rl.rhs).1 ++ rest := by
    rw [hq40, ← List.drop_drop, hd1]; simp [u64B]
  obtain ⟨memo', a3, hrun3, hA3, hk3, hM3, hlt3, hq3, hf3, hs3, hmo3⟩ :=
    exprCall hL hr rl.rhs hfe hI2.arena hI2.mode hM2 hd3 (by rw [hs2, hs1, hst]; decide)
      (by have := hI2.ok.2.2.2.2; omega) h3
  obtain ⟨hI4, hE4, hIW4, ht4, -⟩ := hI2.expr hA3 hmo3 hf3 hk3
  obtain ⟨hI5, hM5, hs5, ht5, hIW5⟩ := setER_facts hI4 hM3 (rr + 8) (r3.headD 0) (by omega)
  have hsz : erTop m ≤ (m.arr64 EREC).size := hI.ok.2.1
  have hE1' : ∀ i : Nat, (erA m1)[i]? = (erA m)[i]? := fun i => by unfold erA; rw [hE1]
  have hE4' : ∀ i : Nat, (erA m3)[i]? = (erA (setERs m1 ws))[i]? := fun i => by unfold erA; rw [hE4]
  have hword : ∀ (j w : Word) (i : Nat), (j, w) ∈ ws → j.toNat = rr.toNat + i → i < 11 → i ≠ 8 →
      (erA (m3.set64 EREC (rr + 8) (r3.headD 0)))[rr.toNat + i]? = some w := by
    intro j w i hjw hj h11 h8
    rw [er_set_ne _ _ _ _ (by rw [hc8]; omega), hE4', ← hj]
    refine setERs_get ws m1 j w ?_ hjw (by rw [hE1]; omega)
    rw [← hws]; simp [hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc9, hc10]
  have hW0 := hword rr (r1.headD 0) 0 (by rw [← hws]; simp) (by simp) (by omega) (by omega)
  have hW1 := hword (rr + 1) (UInt64.ofNat rl.nfields) 1 (by rw [← hws]; simp) hc1 (by omega) (by omega)
  have hW2 := hword (rr + 2) (UInt64.ofNat rl.ctorParams) 2 (by rw [← hws]; simp) hc2 (by omega) (by omega)
  have hW3 := hword (rr + 3) (UInt64.ofNat 0) 3 (by rw [← hws]; simp) hc3 (by omega) (by omega)
  have hW9 := hword (rr + 9) vk 9 (by rw [← hws]; simp) hc9 (by omega) (by omega)
  have hW10 := hword (rr + 10) ve 10 (by rw [← hws]; simp) hc10 (by omega) (by omega)
  simp only [Nat.add_zero] at hW0
  have hW8 : (erA (m3.set64 EREC (rr + 8) (r3.headD 0)))[rr.toNat + 8]? = some (r3.headD 0) := by
    rw [← hc8]; exact er_set_get m3 _ _ (by rw [hE4, hsz2, hE1]; omega)
  have hlenR := congrArg List.length hdeq
  simp only [List.length_append, u64B, List.length_cons, List.length_nil] at hlenR
  refine ⟨memo', ⟨decI (r1.headD 0), rl.nfields, rl.ctorParams, .plain, decI (r3.headD 0), rl.k, rl.eta⟩,
    a3, ?_, hI5, hseen ▸ hM5, by rw [hs5, hs3, hs2, hs1, hst], ?_,
    ⟨by omega, fun i hi hR => ?_⟩, by omega, by rw [hIW5, hIW4, hIW2, hIW1], ?_⟩
  · simp only [Frontend.internRule]
    rw [run_bind_of _ _ _ _ _ hrun1, hp]
    simp only [Frontend.internFire, pure_bind]
    rw [run_bind_of _ _ _ _ _ hrun3]
    rfl
  · simp only [List.headD_cons]; rw [hq3, hq40, hq1]; omega
  · rw [er_set_ne _ _ _ _ (by rw [hc8]; omega), hE4', setERs_ne ws m1 i (fun jw hjw => by
      obtain ⟨i', h1, -, h2⟩ := hmemws jw hjw; omega), hE1']
  · refine holds_decRule _ _ _ _ _ _ _ _ hW0 hW1 hW2 hW3 hW8 hW9 hW10 hlt1 hlt3 (by simp) rfl
      (ofNat_toNat_lt hnf).symm (ofNat_toNat_lt hcp).symm rfl rfl ?_ ?_
    · rw [← hvk]; exact (bw_ne _).symm
    · rw [← hve]; exact (bw_ne _).symm

end rule

section rules
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

/-- **`rci_rules_to` refines `Frontend.internRules`**, into the 11-word records at `o`, `o + 11`, …. -/
@[refines_part ConRon.Arena.Frontend.internRules "plain rules"]
theorem rulesTo_rel {m₀ : Mem} {a₀ : AState} {T : Nat} :
    ∀ (rs : List ConLeche.RecRule), rs.all ruleFits = true → ∀ (seen : List ConLeche.Expr) (memo : EMemo)
      (k : Nat) (m : Mem) (a : AState) (q o kw : Word) (rest : List UInt8) (r : List Word) (m' : Mem),
      RInv m₀ a₀ T m a → MemoR m seen memo → stkTop m = 0 →
      rom.drop q.toNat = (encRules seen rs).1 ++ rest → kw.toNat = rs.length →
      erTop m₀ ≤ o.toNat → o.toNat + 11 * rs.length ≤ erTop m →
      callW p k "rci_rules_to" [q, o, kw] m = some (r, m') →
      ∃ (memo' : EMemo) (irs : List IRecRule) (a' : AState),
        (Frontend.internRules memo rs).run a = .ok ((memo', irs), a') ∧ irs.length = rs.length ∧
        RInv m₀ a₀ T m' a' ∧ MemoR m' (encRules seen rs).2 memo' ∧ stkTop m' = 0 ∧
        (r.headD 0).toNat = q.toNat + (encRules seen rs).1.length ∧
        EKeep (fun i => o.toNat ≤ i ∧ i < o.toNat + 11 * rs.length) m m' ∧ erTop m' = erTop m ∧
        m'.arr64 IW = m.arr64 IW ∧
        ∀ j (hj : j < irs.length), Holds (fun i => o.toNat + 11 * j ≤ i ∧ i < o.toNat + 11 * j + 11)
          (fun _ => False) (fun m => decRule (erA m) (o.toNat + 11 * j)) m' irs[j] := by
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
    exact ⟨memo, [], a, rfl, rfl, hI, hM, hst, by simp [encRules], EKeep.refl _ _, rfl, rfl,
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
    obtain ⟨r1, m1, h1, hw⟩ := ntBW_inv hw
    simp only [List.length_cons] at hot hk
    have hd0 : rom.drop q.toNat = (encRule seen rl).1 ++ ((encRules (encRule seen rl).2 rs).1 ++ rest) := by
      rw [hd]; simp [encRules, List.append_assoc]
    obtain ⟨memo1, irl, a1, hrun1, hI1, hM1, hs1, hq1, hek1, ht1, hIW1, hH1⟩ :=
      rule_rel hL hr seen memo rl hfit.1 k m a q o _ _ m1 hI hM hst hd0 ho (by omega) h1
    have hlt := hI.er_lt
    have ho11 : (o + 11).toNat = o.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
    have hk1' : (kw - 1).toNat = rs.length := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    obtain ⟨r2, m2, h2, hw⟩ := ntBW_inv hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hd1 : rom.drop (r1.headD 0).toNat = (encRules (encRule seen rl).2 rs).1 ++ rest :=
      drop_shift rom hr q _ _ _ (by rw [hd0, List.append_assoc]) _ hq1
    obtain ⟨memo2, irs, a2, hrun2, hlen2, hI2, hM2, hs2, hq2, hek2, ht2, hIW2, hH2⟩ :=
      ih hfit.2 _ memo1 (k + 1) m1 a1 _ (o + 11) (kw - 1) rest r2 m2 hI1 hM1 hs1 hd1 hk1'
        (by omega) (by omega) h2
    refine ⟨memo2, irl :: irs, a2, ?_, by simp [hlen2], hI2, ?_, hs2, ?_, ?_, by rw [ht2, ht1],
      by rw [hIW2, hIW1], ?_⟩
    · simp only [Frontend.internRules]
      rw [run_bind_of _ _ _ _ _ hrun1, run_bind_of _ _ _ _ _ hrun2]
      rfl
    · simpa [encRules] using hM2
    · simp only [List.headD_cons]; rw [hq2, hq1]; simp [encRules]; omega
    · rw [ho11] at hek2
      exact (hek1.mono fun i hi => ⟨by omega, by simp; omega⟩).trans
        (hek2.mono fun i hi => ⟨by omega, by simp; omega⟩)
    · intro j hj
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero]
        exact hH1.ekeep hek2 (fun i hi => ⟨by omega, by omega⟩) hIW2
      | succ j =>
        simp only [List.getElem_cons_succ]
        have := hH2 j (by simp at hj; omega)
        rw [ho11] at this
        have e : o.toNat + 11 + 11 * j = o.toNat + 11 * (j + 1) := by omega
        rw [e] at this
        exact this

end rules

end L.Rom
