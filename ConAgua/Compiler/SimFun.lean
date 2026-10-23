module

public import ConAgua.Compiler.SimCall
public import ConAgua.L.Logic

@[expose] public section

/-!
# Function bodies

`funSim`: from `ExecSim p G n` (statements under `exec p n`), every function of `p` simulates its
calls (`FunSim p G n`): stack check, frame, parameter copy, zeroed locals, body, epilogue.
-/

namespace L.Compiler

open L

attribute [local simp] Reg64s.set64_rax Reg64s.set64_rcx Reg64s.set64_rdx Reg64s.set64_rsi
  Reg64s.set64_rsp Reg64s.set64_r14

theorem int64_ofInt_toBitVec (n : Nat) : (Int64.ofInt n).toBitVec = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp [Int64.toBitVec_ofInt]

theorem copyParams_length (i m : Nat) : (copyParams i m).length = 2 * m := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih => simp [copyParams, ih]; omega

theorem zeroLocals_length (ctx : Ctx) (j m : Nat) : (zeroLocals ctx j m).length = m := by
  induction m generalizing j with
  | zero => rfl
  | succ m ih => simp [zeroLocals, ih]

section
variable [Host]

theorem sim_copy (vs : List Word) (sp ap : Nat) (Q : MachineState → Prop) :
    ∀ (m i k : Nat) (s : MachineData), Code (copyParams i m) k → i + m ≤ vs.length → 8 * (i + m) < 2 ^ 31 →
    s.regs.rsp.toNat = sp → s.regs.rsi.toNat = ap →
    (∀ j (h : j < vs.length), i ≤ j → rdW s.dmem (A (ap + 8 * j)) = some vs[j]) →
    (vs.length = 0 ∨ sp + 8 * (i + m) ≤ ap ∨ ap + 8 * vs.length ≤ sp) → ap + 8 * vs.length ≤ 2 ^ 64 →
    sp + 8 * (i + m) ≤ 2 ^ 64 →
    (∀ j, i ≤ j → j < i + m → (rdW s.dmem (A (sp + 8 * j))).isSome) →
    (∀ s', s'.regs.rsp = s.regs.rsp → s'.regs.rsi = s.regs.rsi → s'.regs.r15 = s.regs.r15 →
      s'.regs.rbp = s.regs.rbp → s'.regs.r14 = s.regs.r14 →
      Only (sp + 8 * i) (sp + 8 * (i + m)) s.dmem s'.dmem →
      (∀ j (h : j < vs.length), i ≤ j → j < i + m → rdW s'.dmem (A (sp + 8 * j)) = some vs[j]) →
      Ev Q s' (at_ (k + 2 * m))) →
    Ev Q s (at_ k) := by
  intro m
  induction m with
  | zero =>
    intro i k s _ _ _ _ _ _ _ _ _ _ hK
    exact hK s rfl rfl rfl rfl rfl (Only.refl _ _ _) (fun j _ h1 h2 => absurd h2 (by omega))
  | succ m ih =>
    intro i k s hc hlen hoff hsp hsi hargs hsa hap hspov hmap hK
    simp only [copyParams, List.cons_append, List.nil_append] at hc
    have hi : i < vs.length := by omega
    refine ev_movRM hc.head ⟨by omega, by omega⟩ (v := vs[i]) ?_ ?_
    · rw [Reg64s.get64_rsi, UInt64.toNat_toBitVec, hsi, toNat_eight_mul]; exact hargs i hi (Nat.le_refl _)
    refine ev_movMR hc.tail.head ⟨by omega, by omega⟩ ?_ ?_
    · simp only [Reg64s.set64_rax, Reg64s.get64_rsp, UInt64.toNat_toBitVec, toNat_eight_mul]
      rw [hsp]; exact hmap i (Nat.le_refl _) (by omega)
    simp only [Reg64s.set64_rax, Reg64s.get64_rsp, Reg64s.get64_rax, UInt64.toNat_toBitVec, toNat_eight_mul]
    rw [hsp]
    refine ih (i + 1) _ _ hc.tail.tail (by omega) (by omega) (by simp [hsp]) (by simp [hsi]) ?_ (by omega) hap
      (by omega) ?_ ?_
    · intro j hj hij
      simp only
      rw [rdW_wrW_A (by omega) (by omega) (by omega)]
      exact hargs j hj (by omega)
    · intro j h1 h2
      simp only
      rw [rdW_wrW_A (by omega) (by omega) (by omega)]
      exact hmap j (by omega) (by omega)
    · intro s' h1 h2 h3 h4 h5 hO hsl
      refine ev_congr (hK s' (by simp [h1]) (by simp [h2]) (by simp [h3]) (by simp [h4]) (by simp [h5])
        ((Only.wrW (by omega)).union hO (by omega) (by omega) (by omega) (by omega)) ?_) (by omega)
      intro j hj h1j h2j
      by_cases hji : j = i
      · subst hji
        rw [hO.rdW_eq (by omega) (by omega)]
        simp [rdW_wrW_same]
      · exact hsl j hj (by omega) (by omega)

omit [Host] in
theorem storeParams_length_le (ctx : Ctx) : ∀ (rs : List Reg64) (i : Nat), (storeParams ctx i rs).length ≤ rs.length
  | [], _ => by simp [storeParams]
  | r :: rs, i => by
    have := storeParams_length_le ctx rs (i + 1)
    simp only [storeParams, List.length_append, List.length_cons]
    split <;> simp <;> omega

/-- The parameters passed in registers `rs`: those not kept in registers into their slots. -/
theorem sim_storeParams (ctx : Ctx) (sp : Nat) (Q : MachineState → Prop) :
    ∀ (rs : List Reg64) (i k : Nat) (s : MachineData), Code (storeParams ctx i rs) k →
    s.regs.rsp.toNat = sp → 8 * (i + rs.length) < 2 ^ 31 → sp + 8 * (i + rs.length) ≤ 2 ^ 64 →
    (∀ y, sp + 8 * i ≤ y → y < sp + 8 * (i + rs.length) → (s.dmem.get? (A y)).isSome) →
    (∀ s', s'.regs = s.regs → Only (sp + 8 * i) (sp + 8 * (i + rs.length)) s.dmem s'.dmem →
      ((∀ x, i ≤ x → x < i + rs.length → (ctx.alloc.lookup x).isSome) → s'.dmem = s.dmem) →
      (∀ x, i ≤ x → x < i + rs.length → ctx.alloc.lookup x = none →
        rdW s'.dmem (A (sp + 8 * x)) = some (UInt64.ofBitVec (s.regs.get64 (rs.getD (x - i) .rax)))) →
      Ev Q s' (at_ (k + (storeParams ctx i rs).length))) →
    Ev Q s (at_ k) := by
  intro rs
  induction rs with
  | nil =>
    intro i k s _ _ _ _ _ hK
    exact ev_congr (hK s rfl (Only.refl _ _ _) (fun _ => rfl) (fun x h1 h2 => absurd h2 (by simp; omega)))
      (by simp [storeParams])
  | cons r rs ih =>
    intro i k s hc hsp hoff hov hmap hK
    simp only [List.length_cons] at hoff hov hmap hK
    have hc0 := hc
    simp only [storeParams] at hc
    -- the rest, from a state that agrees with `s` but for slot `i`
    have hrest : ∀ (m : Nat) (s1 : MachineData), Code (storeParams ctx (i + 1) rs) (k + m) →
        (storeParams ctx i (r :: rs)).length = m + (storeParams ctx (i + 1) rs).length →
        s1.regs = s.regs → Only (sp + 8 * i) (sp + 8 * (i + 1)) s.dmem s1.dmem →
        ((ctx.alloc.lookup i).isSome → s1.dmem = s.dmem) →
        (ctx.alloc.lookup i = none → rdW s1.dmem (A (sp + 8 * i)) = some (UInt64.ofBitVec (s.regs.get64 r))) →
        Ev Q s1 (at_ (k + m)) := by
      intro m s1 hc1 hm hr1 hO1 hs1 hv1
      refine ih (i + 1) (k + m) s1 hc1 (by rw [hr1]; exact hsp) (by omega) (by omega) ?_ ?_
      · intro y h1 h2
        exact hO1.grows _ (hmap y (by omega) (by omega))
      · intro s' hr' hO' hs' hv'
        refine ev_congr (hK s' (hr'.trans hr1) (hO1.union hO' (by omega) (by omega) (by omega) (by omega)) ?_ ?_) ?_
        · intro hall
          rw [hs' fun x h1 h2 => hall x (by omega) (by omega)]
          exact hs1 (hall i (Nat.le_refl _) (by omega))
        · intro x h1 h2 hn
          by_cases hxi : x = i
          · subst hxi
            rw [hO'.rdW_eq (by omega) (by omega), hv1 hn]; simp
          · rw [hv' x (by omega) (by omega) hn, hr1]
            congr 3
            rw [show x - i = (x - (i + 1)) + 1 by omega]; rfl
        · rw [hm]; omega
    cases hl : ctx.alloc.lookup i with
    | some r' =>
      simp only [hl, List.nil_append] at hc
      exact ev_congr (hrest 0 s (by simpa using hc) (by simp [storeParams, hl]) rfl (Only.refl _ _ _)
        (fun _ => rfl) (fun h => by simp [hl] at h)) (by simp)
    | none =>
      simp only [hl, List.singleton_append] at hc
      refine ev_movMR hc.head ⟨by omega, by omega⟩ ?_ ?_
      · rw [slot_addr _ i _ (by omega), hsp]
        exact isSome_rdW fun t ht => by rw [A_add]; exact hmap _ (by omega) (by omega)
      rw [slot_addr _ i _ (by omega), hsp]
      exact hrest 1 _ hc.tail (by simp [storeParams, hl]; omega) rfl
        (Only.wrW (by omega) |>.mono (by omega) (by omega))
        (fun h => by simp [hl] at h) (fun _ => by rw [rdW_wrW_same])

/-- Zeroing locals `j, …, j + m - 1`: in their registers or slots. -/
theorem sim_zeroLocals (ctx : Ctx) (hal : ∀ x r, ctx.alloc.lookup x = some r → r ∈ allocRegs)
    (hinj : ∀ x y r, ctx.alloc.lookup x = some r → ctx.alloc.lookup y = some r → x = y) (sp : Nat) (Q : MachineState → Prop) :
    ∀ (m j k : Nat) (s : MachineData), Code (zeroLocals ctx j m) k → s.regs.rsp.toNat = sp →
    8 * (j + m) < 2 ^ 31 → sp + 8 * (j + m) ≤ 2 ^ 64 →
    (∀ y, sp + 8 * j ≤ y → y < sp + 8 * (j + m) → (s.dmem.get? (A y)).isSome) →
    (∀ s', Only (sp + 8 * j) (sp + 8 * (j + m)) s.dmem s'.dmem →
      ((∀ x, j ≤ x → x < j + m → (ctx.alloc.lookup x).isSome) → s'.dmem = s.dmem) →
      (∀ x, j ≤ x → x < j + m → ctx.alloc.lookup x = none → rdW s'.dmem (A (sp + 8 * x)) = some 0) →
      (∀ x r, j ≤ x → x < j + m → ctx.alloc.lookup x = some r → s'.regs.get64 r = 0) →
      (∀ r, (∀ x, j ≤ x → x < j + m → ctx.alloc.lookup x ≠ some r) → s'.regs.get64 r = s.regs.get64 r) →
      Ev Q s' (at_ (k + m))) →
    Ev Q s (at_ k) := by
  intro m
  induction m with
  | zero =>
    intro j k s _ _ _ _ _ hK
    exact hK s (Only.refl _ _ _) (fun _ => rfl) (fun x h1 h2 => absurd h2 (by omega))
      (fun x r h1 h2 => absurd h2 (by omega)) (fun _ _ => rfl)
  | succ m ih =>
    intro j k s hc hsp hoff hov hmap hK
    simp only [zeroLocals] at hc
    have hrest : ∀ s1 : MachineData, s1.regs.rsp = s.regs.rsp → Only (sp + 8 * j) (sp + 8 * (j + 1)) s.dmem s1.dmem →
        ((ctx.alloc.lookup j).isSome → s1.dmem = s.dmem) →
        (ctx.alloc.lookup j = none → rdW s1.dmem (A (sp + 8 * j)) = some 0) →
        (∀ r, ctx.alloc.lookup j = some r → s1.regs.get64 r = 0) →
        (∀ r, ctx.alloc.lookup j ≠ some r → s1.regs.get64 r = s.regs.get64 r) →
        Ev Q s1 (at_ (k + 1)) := by
      intro s1 hr1 hO1 hs1 hz1 hzr1 hk1
      refine ih (j + 1) (k + 1) s1 hc.tail (by rw [hr1]; exact hsp) (by omega) (by omega) ?_ ?_
      · intro y h1 h2
        exact hO1.grows _ (hmap y (by omega) (by omega))
      · intro s' hO' hs' hz' hzr' hk'
        refine ev_congr (hK s' (hO1.union hO' (by omega) (by omega) (by omega) (by omega)) ?_ ?_ ?_ ?_) (by omega)
        · intro hall
          rw [hs' fun x h1 h2 => hall x (by omega) (by omega)]
          exact hs1 (hall j (Nat.le_refl _) (by omega))
        · intro x h1 h2 hn
          by_cases hxj : x = j
          · subst hxj; rw [hO'.rdW_eq (by omega) (by omega)]; exact hz1 hn
          · exact hz' x (by omega) (by omega) hn
        · intro x r h1 h2 hr
          by_cases hxj : x = j
          · rw [hxj] at hr
            rw [hk' r (fun y (hy1 : j + 1 ≤ y) _ hy => absurd (hinj y j r hy hr) (by lomega))]
            exact hzr1 r hr
          · exact hzr' x r (by omega) (by omega) hr
        · intro r hr
          rw [hk' r fun x h1 h2 => hr x (by omega) (by omega), hk1 r (hr j (Nat.le_refl _) (by omega))]
    cases hl : ctx.alloc.lookup j with
    | some r =>
      simp only [hl] at hc
      have hr := hal j r hl
      obtain ⟨h1, h2, h3, h4⟩ := set64_alloc_fields (R := s.regs) hr (0 : Word).toBitVec
      refine ev_movRI hc.head (hrest _ h1 (Only.refl _ _ _) (fun _ => rfl) (fun h => by simp [hl] at h)
        (fun r' h => ?_) (fun r' h => ?_))
      · rw [hl] at h; cases h; simp [rget_set]
      · rw [rget_set, if_neg (fun e => h (by rw [hl, e]))]
    | none =>
      simp only [hl] at hc
      refine ev_movMI hc.head ⟨by omega, by omega⟩ ?_ ?_
      · rw [slot_addr _ j _ (by omega), hsp]
        exact isSome_rdW fun t ht => by rw [A_add]; exact hmap _ (by omega) (by omega)
      rw [slot_addr _ j _ (by omega), hsp]
      exact hrest _ rfl ((Only.wrW (by omega)).mono (by omega) (by omega)) (fun h => by simp [hl] at h)
        (fun _ => by rw [rdW_wrW_same]; rfl) (fun r h => by simp [hl] at h) (fun _ _ => rfl)

end

/-- Every `return` fits the result registers and area. -/
theorem Stmt.nret_le_of_wf {p : Prog} {nl : Nat} {tab : Tab} :
    ∀ {s : Stmt}, Stmt.wf p nl tab s = true → Stmt.nret s ≤ tab.nres
  | .skip, _ | .brk, _ | .abort, _ | .set .., _ | .st8 .., _ | .st64 .., _ | .call .., _ | .gset .., _ =>
    Nat.zero_le _
  | .seq s u, h => by
    simp only [Stmt.wf, Bool.and_eq_true] at h
    have h1 := Stmt.nret_le_of_wf h.1
    have h2 := Stmt.nret_le_of_wf h.2
    simp only [Stmt.nret]; omega
  | .ite _ s u, h => by
    simp only [Stmt.wf, Bool.and_eq_true] at h
    have h1 := Stmt.nret_le_of_wf h.1.2
    have h2 := Stmt.nret_le_of_wf h.2
    simp only [Stmt.nret]; omega
  | .while _ s, h => by
    simp only [Stmt.wf, Bool.and_eq_true] at h
    exact Stmt.nret_le_of_wf (s := s) h.2
  | .ret es, h => by
    simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2

section
variable [Host] {G : Layout} (hG : G.Ok) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff) (p : Prog)
include hG hTab

theorem funSim_todo : True := trivial

end

end L.Compiler
