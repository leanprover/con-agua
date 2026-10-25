module

public import ConAgua.Compiler.SimCall
public import ConAgua.L.Logic
public import ConAgua.L.DefAssignSim

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

/-- The parameters passed in registers `rs`: those not kept in registers into their slots. -/
theorem sim_storeParams (ctx : Ctx) (sp : Nat) (Q : MachineState → Prop) :
    ∀ (rs : List Reg64) (i k : Nat) (s : MachineData), Code (storeParams ctx i rs) k →
    s.regs.rsp.toNat = sp →
    (∀ x, i ≤ x → x < i + rs.length → ctx.alloc.lookup x = none → 8 * x < 2 ^ 31 ∧ sp + 8 * x + 8 ≤ 2 ^ 64 ∧
      ∀ t < 8, (s.dmem.get? (A (sp + 8 * x + t))).isSome) →
    (∀ s', s'.regs = s.regs → Only (sp + 8 * i) (sp + 8 * (i + rs.length)) s.dmem s'.dmem →
      ((∀ x, i ≤ x → x < i + rs.length → (ctx.alloc.lookup x).isSome) → s'.dmem = s.dmem) →
      (∀ x, i ≤ x → x < i + rs.length → ctx.alloc.lookup x = none →
        rdW s'.dmem (A (sp + 8 * x)) = some (UInt64.ofBitVec (s.regs.get64 (rs.getD (x - i) .rax)))) →
      Ev Q s' (at_ (k + (storeParams ctx i rs).length))) →
    Ev Q s (at_ k) := by
  intro rs
  induction rs with
  | nil =>
    intro i k s _ _ _ hK
    exact ev_congr (hK s rfl (Only.refl _ _ _) (fun _ => rfl) (fun x h1 h2 => absurd h2 (by simp; omega)))
      (by simp [storeParams])
  | cons r rs ih =>
    intro i k s hc hsp hmap hK
    simp only [List.length_cons] at hmap hK
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
      refine ih (i + 1) (k + m) s1 hc1 (by rw [hr1]; exact hsp) ?_ ?_
      · intro x h1 h2 hn
        obtain ⟨a1, a2, a3⟩ := hmap x (by omega) (by omega) hn
        exact ⟨a1, a2, fun t ht => hO1.grows _ (a3 t ht)⟩
      · intro s' hr' hO' hs' hv'
        refine ev_congr (hK s' (hr'.trans hr1) (hO1.union hO' (by omega) (by omega) (by omega) (by omega)) ?_ ?_) ?_
        · intro hall
          rw [hs' fun x h1 h2 => hall x (by omega) (by omega)]
          exact hs1 (hall i (Nat.le_refl _) (by omega))
        · intro x h1 h2 hn
          by_cases hxi : x = i
          · subst hxi
            have := (hmap x (Nat.le_refl _) (by omega) hn).2.1
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
      obtain ⟨a1, a2, a3⟩ := hmap i (Nat.le_refl _) (by omega) hl
      refine ev_movMR hc.head ⟨by omega, by omega⟩ ?_ ?_
      · rw [slot_addr _ i _ (by omega), hsp]
        exact isSome_rdW fun t ht => by rw [A_add]; exact a3 t ht
      rw [slot_addr _ i _ (by omega), hsp]
      exact hrest 1 _ hc.tail (by simp [storeParams, hl]; omega) rfl
        (Only.wrW (by omega) |>.mono (by omega) (by omega))
        (fun h => by simp [hl] at h) (fun _ => by rw [rdW_wrW_same])

/-- Zeroing those of the locals `j, …, j + m - 1` that `need` lists: in their registers or slots. -/
theorem sim_zeroLocals (ctx : Ctx) (need : List Var) (hal : ∀ x r, ctx.alloc.lookup x = some r → r ∈ allocRegs)
    (hinj : ∀ x y r, ctx.alloc.lookup x = some r → ctx.alloc.lookup y = some r → x = y) (sp : Nat) (Q : MachineState → Prop) :
    ∀ (m j k : Nat) (s : MachineData), Code (zeroLocals ctx need j m) k → s.regs.rsp.toNat = sp →
    (∀ x, j ≤ x → x < j + m → ctx.alloc.lookup x = none → 8 * x < 2 ^ 31 ∧ sp + 8 * x + 8 ≤ 2 ^ 64 ∧
      ∀ t < 8, (s.dmem.get? (A (sp + 8 * x + t))).isSome) →
    (∀ s', Only (sp + 8 * j) (sp + 8 * (j + m)) s.dmem s'.dmem →
      ((∀ x, j ≤ x → x < j + m → (ctx.alloc.lookup x).isSome) → s'.dmem = s.dmem) →
      (∀ x, j ≤ x → x < j + m → need.contains x = true → ctx.alloc.lookup x = none →
        rdW s'.dmem (A (sp + 8 * x)) = some 0) →
      (∀ x r, j ≤ x → x < j + m → need.contains x = true → ctx.alloc.lookup x = some r →
        s'.regs.get64 r = 0) →
      (∀ r, (∀ x, j ≤ x → x < j + m → need.contains x = true → ctx.alloc.lookup x ≠ some r) →
        s'.regs.get64 r = s.regs.get64 r) →
      Ev Q s' (at_ (k + (zeroLocals ctx need j m).length))) →
    Ev Q s (at_ k) := by
  intro m
  induction m with
  | zero =>
    intro j k s _ _ _ hK
    exact ev_congr (hK s (Only.refl _ _ _) (fun _ => rfl) (fun x h1 h2 => absurd h2 (by omega))
      (fun x r h1 h2 => absurd h2 (by omega)) (fun _ _ => rfl)) (by simp [zeroLocals])
  | succ m ih =>
    intro j k s hc hsp hmap hK
    by_cases hnd : need.contains j = true
    case neg =>
      simp only [zeroLocals, hnd, Bool.false_eq_true, ite_false, List.nil_append] at hc hK
      refine ih (j + 1) k s hc hsp (fun x h1 h2 hn => hmap x (by omega) (by omega) hn) ?_
      have hne : ∀ x : Nat, need.contains x = true → x ≠ j := fun x hx e => hnd (e ▸ hx)
      intro s' hO' hs' hz' hzr' hk'
      refine hK s' (Only.mono hO' (by omega) (by omega)) (fun hall => hs' fun x h1 h2 => hall x (by omega) (by omega))
        (fun x h1 h2 hx hn => hz' x (by have := hne x hx; omega) (by omega) hx hn)
        (fun x r h1 h2 hx hr => hzr' x r (by have := hne x hx; omega) (by omega) hx hr)
        (fun r hr => hk' r fun x h1 h2 hx => hr x (by omega) (by omega) hx)
    simp only [zeroLocals, hnd, ite_true, List.singleton_append] at hc hK
    have hrest : ∀ s1 : MachineData, s1.regs.rsp = s.regs.rsp → Only (sp + 8 * j) (sp + 8 * (j + 1)) s.dmem s1.dmem →
        ((ctx.alloc.lookup j).isSome → s1.dmem = s.dmem) →
        (ctx.alloc.lookup j = none → rdW s1.dmem (A (sp + 8 * j)) = some 0) →
        (∀ r, ctx.alloc.lookup j = some r → s1.regs.get64 r = 0) →
        (∀ r, ctx.alloc.lookup j ≠ some r → s1.regs.get64 r = s.regs.get64 r) →
        Ev Q s1 (at_ (k + 1)) := by
      intro s1 hr1 hO1 hs1 hz1 hzr1 hk1
      refine ih (j + 1) (k + 1) s1 hc.tail (by rw [hr1]; exact hsp) ?_ ?_
      · intro x h1 h2 hn
        obtain ⟨a1, a2, a3⟩ := hmap x (by omega) (by omega) hn
        exact ⟨a1, a2, fun t ht => hO1.grows _ (a3 t ht)⟩
      · intro s' hO' hs' hz' hzr' hk'
        refine ev_congr (hK s' (hO1.union hO' (by omega) (by omega) (by omega) (by omega)) ?_ ?_ ?_ ?_) (by simp; omega)
        · intro hall
          rw [hs' fun x h1 h2 => hall x (by omega) (by omega)]
          exact hs1 (hall j (Nat.le_refl _) (by omega))
        · intro x h1 h2 hx hn
          by_cases hxj : x = j
          · subst hxj
            have := (hmap x (Nat.le_refl _) (by omega) hn).2.1
            rw [hO'.rdW_eq (by omega) (by omega)]; exact hz1 hn
          · exact hz' x (by omega) (by omega) hx hn
        · intro x r h1 h2 hx hr
          by_cases hxj : x = j
          · rw [hxj] at hr
            rw [hk' r (fun y (hy1 : j + 1 ≤ y) _ _ hy => absurd (hinj y j r hy hr) (by lomega))]
            exact hzr1 r hr
          · exact hzr' x r (by omega) (by omega) hx hr
        · intro r hr
          rw [hk' r fun x h1 h2 hx => hr x (by omega) (by omega) hx, hk1 r (hr j (Nat.le_refl _) (by omega) hnd)]
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
      obtain ⟨a1, a2, a3⟩ := hmap j (Nat.le_refl _) (by omega) hl
      refine ev_movMI hc.head ⟨by omega, by omega⟩ ?_ ?_
      · rw [slot_addr _ j _ (by omega), hsp]
        exact isSome_rdW fun t ht => by rw [A_add]; exact a3 t ht
      rw [slot_addr _ j _ (by omega), hsp]
      exact hrest _ rfl ((Only.wrW (by omega)).mono (by omega) (by omega)) (fun h => by simp [hl] at h)
        (fun _ => by rw [rdW_wrW_same]; rfl) (fun r h => by simp [hl] at h) (fun _ _ => rfl)

end

/-! ## The register allocation, checked -/

theorem reg64_beq_iff {a b : Reg64} : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

instance : LawfulBEq Reg64 where
  eq_of_beq h := reg64_beq_iff.mp h
  rfl {a} := reg64_beq_iff.mpr rfl

theorem nodupB_cons {α} [BEq α] [LawfulBEq α] {a : α} {l : List α} :
    nodupB (a :: l) = true ↔ a ∉ l ∧ nodupB l = true := by
  simp [nodupB]

theorem lookup_mem {al : List (Var × Reg64)} {x : Var} {r : Reg64} (h : al.lookup x = some r) :
    (x, r) ∈ al := by
  induction al with
  | nil => simp at h
  | cons a al ih =>
    obtain ⟨y, r'⟩ := a
    simp only [List.lookup_cons] at h
    split at h
    · rename_i he; cases h; simp only [beq_iff_eq] at he; simp [he]
    · exact List.mem_cons_of_mem _ (ih h)

theorem lookup_mem_snd {al : List (Var × Reg64)} {x : Var} {r : Reg64} (h : al.lookup x = some r) :
    r ∈ al.map (·.2) := by
  induction al with
  | nil => simp at h
  | cons a al ih =>
    obtain ⟨y, r'⟩ := a
    simp only [List.lookup_cons] at h
    split at h
    · cases h; simp
    · simp [ih h]

/-- What `allocOk` checks. -/
structure AllocSpec (np : Nat) (al : List (Var × Reg64)) : Prop where
  reg : ∀ x r, al.lookup x = some r → r ∈ allocRegs
  arg : ∀ x r, al.lookup x = some r → x < np → argRegs.getD x .rax = r
  inj : ∀ x y r, al.lookup x = some r → al.lookup y = some r → x = y
  np : al ≠ [] → np ≤ argRegs.length

theorem AllocSpec.nil (np : Nat) : AllocSpec np [] :=
  ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h, fun _ _ _ h => by simp at h, fun h => absurd rfl h⟩

theorem allocOk_spec {np : Nat} {al : List (Var × Reg64)} (h : allocOk np al = true) : AllocSpec np al := by
  simp only [allocOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨hall, hn2⟩, -⟩, hnp⟩ := h
  have hmem : ∀ x r, al.lookup x = some r → (x, r) ∈ al := fun x r => lookup_mem
  refine ⟨fun x r hl => ?_, fun x r hl hx => ?_, fun x y r hx hy => ?_, fun hne => ?_⟩
  · have := hall _ (hmem x r hl)
    simp only [List.contains_iff_mem] at this
    exact this.1
  · have := (hall _ (hmem x r hl)).2
    rcases this with h1 | h1
    · simp only [L.Var] at *; omega
    · simp only [beq_iff_eq] at h1
      simp [List.getD_eq_getElem?_getD, h1]
  · clear hall hnp hmem
    induction al with
    | nil => simp at hx
    | cons a al ih =>
      obtain ⟨z, r'⟩ := a
      have hnd := nodupB_cons.mp hn2
      simp only [List.lookup_cons] at hx hy
      split at hx <;> split at hy
      · simp_all
      · cases hx; exact absurd (lookup_mem_snd hy) hnd.1
      · cases hy; exact absurd (lookup_mem_snd hx) hnd.1
      · exact ih hnd.2 hx hy
  · rcases hnp with h1 | h1
    · exact absurd h1 hne
    · exact h1

theorem tempsEs_le : ∀ (es : List Expr) (i : Nat), tempsEs es ≤ tempsArgs i es
  | [], _ => Nat.le_refl _
  | e :: es, i => by
    have := tempsEs_le es (i + 1)
    simp only [tempsEs, tempsArgs]; omega

theorem tempsS_le (al : List (Var × Reg64)) (nr : Nat) : ∀ s, tempsS al nr s ≤ tempsSB s
  | .skip | .brk | .abort => Nat.le_refl _
  | .set _ _ | .st8 .. | .st64 .. | .gset .. | .st64t .. | .copy64 .. | .copy8w .. | .scan8 .. => by
    simp [tempsS, tempsSB]
  | .seq s t | .ite _ s t => by
    have := tempsS_le al nr s; have := tempsS_le al nr t; simp only [tempsS, tempsSB]; omega
  | .while _ s => by have := tempsS_le al nr s; simp only [tempsS, tempsSB]; omega
  | .ret es => by
    have := tempsEs_le es 0; simp only [tempsS, tempsSB]; split <;> omega
  | .call _ _ es => by
    have := tempsEs_le es 0; simp only [tempsS, tempsSB]; split <;> omega

/-- Every `return` fits the result registers and area. -/
theorem Stmt.nret_le_of_wf {p : Prog} {nl : Nat} {tab : Tab} :
    ∀ {s : Stmt}, Stmt.wf p nl tab s = true → Stmt.nret s ≤ tab.nres
  | .skip, _ | .brk, _ | .abort, _ | .set .., _ | .st8 .., _ | .st64 .., _ | .call .., _ | .gset .., _
  | .st64t .., _ | .copy64 .., _ | .copy8w .., _ | .scan8 .., _ =>
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

theorem fnCtx_spec (tab : Tab) (t : NTree) (f : FnName) (fd : FunDecl) :
    AllocSpec fd.nparams (fnCtx tab t f fd).alloc := by
  simp only [fnCtx]
  split
  · rename_i h; simp only [Bool.and_eq_true] at h; exact allocOk_spec h.1.2
  · exact AllocSpec.nil _

theorem fnCtx_allocOk (tab : Tab) (t : NTree) (f : FnName) (fd : FunDecl) :
    AllocOk (fnCtx tab t f fd) := by
  have h := fnCtx_spec tab t f fd
  refine ⟨h.reg, h.inj, fun hl => ?_, fun hl => ?_, fun x hx => ?_, fun ht y => ?_⟩
  · simp only [fnCtx] at hl ⊢
    rw [if_neg (by simp [hl])]
  · simp only [fnCtx, Bool.not_eq_false'] at hl ⊢
    simp [tregOf, hl]
  · simp only [fnCtx] at hx ⊢
    split
    · rename_i hc
      simp only [Bool.and_eq_true, tregFree, hx] at hc
      simpa using hc.2.1
    · rfl
  · simp only [fnCtx] at ht ⊢
    split
    · rename_i hc
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp ht
      simp only [Bool.and_eq_true, tregFree, hx, List.all_eq_true] at hc
      intro hy
      have := hc.2.2 (y, .rsi) (lookup_mem hy)
      simp at this
    · simp

theorem bestTier_lt (u : Array Nat) : ∀ n b x, bestTier u n b = some x → x < n ∨ b = some x
  | 0, _, _, h => .inr h
  | n + 1, b, x, h => by
    simp only [bestTier] at h
    rcases bestTier_lt u n _ x h with h1 | h1
    · exact .inl (Nat.lt_succ_of_lt h1)
    · by_cases hb : betterTier u n b = true
      · rw [if_pos hb] at h1; cases h1; exact .inl (Nat.lt_succ_self _)
      · rw [if_neg hb] at h1; exact .inr h1

/-- The tier local is a parameter of a leaf with at most 6 parameters. -/
theorem tregOf_spec (fd : FunDecl) (x : Var) (h : tregOf fd = some x) :
    x < fd.nparams ∧ fd.nparams < argRegs.length ∧ fd.nparams ≤ fd.nlocals ∧ Stmt.calls fd.body = false := by
  unfold tregOf at h
  split at h
  · cases h
  · rename_i hc
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt, Nat.not_le] at hc
    rcases bestTier_lt _ _ _ x h with h1 | h1
    · exact ⟨h1, hc.1.2, hc.2, by simpa using hc.1.1⟩
    · cases h1

theorem not_lookup_fixed {ctx : Ctx} (h : AllocOk ctx) {r : Reg64} (hr : r ∉ allocRegs) :
    ∀ x, ctx.alloc.lookup x ≠ some r := fun x hx => hr (h.reg x r hx)

section
variable [Host] {G : Layout} (hG : G.Ok) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff) (p : Prog)
include hG hTab

/-- A function's body after the tier entry (`fnBody0`) from the state `s4`, with an `F'`-word
frame at `rsp` (none for a frameless leaf): parameters, zeroed locals, the body, the results. -/
theorem sim_fnBody0 (t : NTree)
    (hTree : ∀ g fd, p.lookup g = some fd → nrOf t G.tab g = Stmt.nret fd.body) (n : Nat)
    (hE : ExecSim p G n) (f : FnName) (fd : FunDecl) (hlk : p.lookup f = some fd)
    (hnp : fd.nparams ≤ fd.nlocals) (hbody : Stmt.wf p fd.nlocals G.tab fd.body = true)
    (vs : List Word) (σ : St) (hvl : vs.length = fd.nparams)
    (F' : Nat) (hF'off : 8 * F' + 8 < maxOff)
    (htmp : TmpFit fd.nlocals F' 0 (tempsS (fnCtx G.tab t f fd).alloc (Stmt.nret fd.body) fd.body))
    (hslot : ∀ x < fd.nlocals, (fnCtx G.tab t f fd).alloc.lookup x = none → x < F')
    (hframe : (∀ x < fd.nlocals, ((fnCtx G.tab t f fd).alloc.lookup x).isSome) ∨ fd.nlocals ≤ F')
    (s4 : MachineData) (k4 : Nat) (hc : Code (fnBody0 (fnCtx G.tab t f fd) fd) k4)
    (htr : ∀ x, (fnCtx G.tab t f fd).treg = some x → s4.regs.rsi = vs.getD x 0 &&& 1)
    (hlo : G.lo ≤ s4.regs.rsp.toNat) (hlo8 : Stmt.calls fd.body = true → G.lo + 8 ≤ s4.regs.rsp.toNat)
    (hhi : s4.regs.rsp.toNat + 8 * F' + 8 ≤ G.hi) (h15 : s4.regs.r15.toNat = G.T)
    (hmem : MemRel G σ.mem s4.dmem) (hfuel : s4.regs.r14.toNat < n)
    (hregs : fd.nparams ≤ argRegs.length → ∀ i (h : i < vs.length),
      s4.regs.get64 (argRegs.getD i .rax) = vs[i].toBitVec)
    (hmargs : argRegs.length < fd.nparams →
      (∀ i (h : i < vs.length), rdW s4.dmem (A (s4.regs.rsi.toNat + 8 * i)) = some vs[i]) ∧
      (s4.regs.rsp.toNat + 8 * fd.nlocals ≤ s4.regs.rsi.toNat ∨
        s4.regs.rsi.toNat + 8 * vs.length ≤ s4.regs.rsp.toNat) ∧
      s4.regs.rsi.toNat + 8 * vs.length ≤ 2 ^ 64)
    (Q : MachineState → Prop)
    (hepi : ∀ (r : List Word) (σ2 : St) (d2 : MachineData),
      (invoke p (exec p n) f vs).run σ = .ok (r, { σ2 with loc := σ.loc }) →
      MemRel G σ2.mem d2.dmem → SPost G F' s4 d2 → ResOut G (Stmt.nret fd.body) r d2 →
      Ev Q d2 (at_ (k4 + (fnBody0 (fnCtx G.tab t f fd) fd).length)))
    (herr : ∀ d2, (∃ e, (invoke p (exec p n) f vs).run σ = .error e ∧ e ≠ .outOfFuel) →
      GPost G (top s4 F') s4 d2 → Ev Q d2 (label errorL))
    (hexh : ∀ d2, GPost G (top s4 F') s4 d2 → Ev Q d2 (label exhaustedL))
    (htF : ∀ Fw, (fnCtx G.tab t f fd).tailF = some Fw → Fw = F')
    (htail : ∀ (r : List Word) (σ2 : St) (d2 : MachineData) (ra : Word),
      (fnCtx G.tab t f fd).tailF = some F' →
      (invoke p (exec p n) f vs).run σ = .ok (r, { σ2 with loc := σ.loc }) →
      MemRel G σ2.mem d2.dmem → TPost G F' s4 d2 → ResOut G (Stmt.nret fd.body) r d2 →
      rdW d2.dmem (A (top s4 F')) = some ra → Ev Q d2 (Int64.ofBitVec ra.toBitVec)) :
    Ev Q s4 (at_ k4) := by
  have hspec := fnCtx_spec G.tab t f fd
  have hok := fnCtx_allocOk G.tab t f fd
  obtain ⟨ctx, hctx⟩ : ∃ c, c = fnCtx G.tab t f fd := ⟨_, rfl⟩
  rw [← hctx] at hspec hok hslot hframe htmp hc hepi htF htail htr
  have hnl : ctx.nl = fd.nlocals := by rw [hctx]; rfl
  have hT : ctx.tab = G.tab := by rw [hctx]; rfl
  have hnr : ctx.nr = Stmt.nret fd.body := by rw [hctx]; rfl
  have hnrt : ctx.nrt = t := by rw [hctx]; rfl
  have hleaf : ctx.leaf = !Stmt.calls fd.body := by rw [hctx]; rfl
  have hhi2 := hG.hi_le
  simp only [maxOff] at hF'off
  have hTab' := hTab; simp only [maxOff] at hTab'
  have hnr' : Stmt.nret fd.body ≤ G.tab.nres := Stmt.nret_le_of_wf hbody
  simp only [fnBody0, List.append_assoc, List.singleton_append] at hc hepi
  have hbrk : ctx.brk = ctx.endL := by rw [hctx]; rfl
  have hfix : ∀ r, r ∉ allocRegs → ∀ x, ctx.alloc.lookup x ≠ some r := fun r hr => not_lookup_fixed hok hr
  generalize hsp : s4.regs.rsp.toNat = sp at *
  obtain ⟨need, hneed⟩ : ∃ l, l = needZero fd.nparams fd.body := ⟨_, rfl⟩
  rw [← hneed] at hc hepi
  -- the body proper, from the state `s6` with the locals in place
  have H : ∀ (σ0 : St) (s6 : MachineData),
      DaAg (fun x => x ∈ need ∨ fd.nlocals ≤ x) (List.range fd.nparams) σ0 { σ with loc := Locals.init vs } →
      s6.regs.rsp = s4.regs.rsp → s6.regs.rbp = s4.regs.rbp →
      s6.regs.r14 = s4.regs.r14 → s6.regs.r15 = s4.regs.r15 →
      Pres G (top s4 F') s4.dmem s6.dmem →
      Inv G ctx F' σ0 s6 →
      Ev Q s6 (at_ (k4 + (if fd.nparams ≤ argRegs.length then storeParams ctx 0 (argRegs.take fd.nparams)
        else copyParams 0 fd.nparams).length + (zeroLocals ctx need fd.nparams (fd.nlocals - fd.nparams)).length)) := by
    intro σ0 s6 hag r1 r2 r3 r4 hP6 hI6
    have hR : ∀ x ∈ (Stmt.da fd.body (some (List.range fd.nparams)) []).2, x ∈ need ∨ fd.nlocals ≤ x :=
      fun x hx => .inl (by rw [hneed]; exact hx)
    have c2 := hc.right.right
    have c3 := c2.right
    have cR := c3.tail.right
    have htop : top s6 F' = top s4 F' := by simp only [top, r1]
    have S46 : SPost G F' s4 s6 := ⟨r1, r2, r4, by rw [r3]; exact Nat.le_refl _, hP6⟩
    have hrun : ∀ r σ2, (exec p n fd.body).run σ0 = .ok (r, σ2) →
        (invoke p (exec p n) f vs).run σ = .ok (r.retVal, { σ2 with loc := σ.loc }) := by
      intro r σ2 h
      obtain ⟨t2, h2, hm⟩ := exec_da_ok hR hag h
      rw [invoke_eq vs hlk, callFn_run, h2]
      show Except.ok (r.retVal, (⟨t2.mem, σ.loc⟩ : St)) = .ok (r.retVal, ⟨σ2.mem, σ.loc⟩)
      rw [hm]
    have hepi' : ∀ (r : List Word) (σ2 : St) (d2 : MachineData),
        (invoke p (exec p n) f vs).run σ = .ok (r, { σ2 with loc := σ.loc }) →
        MemRel G σ2.mem d2.dmem → SPost G F' s6 d2 → ResOut G (Stmt.nret fd.body) r d2 →
        Ev Q d2 (label ctx.retL) := by
      intro r σ2 d2 hrun hm2 hS2 hrax
      rw [Code.label (i := 0) cR rfl, Nat.add_zero]
      refine ev_label cR.head ?_
      refine ev_congr (hepi r σ2 d2 hrun hm2 (S46.trans hS2) hrax) ?_
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    have hZ : ∀ σ2 d2, ((exec p n fd.body).run σ0 = .ok (.normal, σ2) ∨
        (exec p n fd.body).run σ0 = .ok (.brk, σ2)) →
        Inv G ctx F' σ2 d2 → SPost G F' s6 d2 → Ev Q d2 (label ctx.endL) := by
      intro σ2 d2 hr hI2 hS2
      rw [Code.label (i := 0) c3 rfl, Nat.add_zero]
      refine ev_label c3.head ?_
      refine sim_loadRes hG ctx hT [] [] Q (by omega) ctx.nr 0 _ d2 c3.tail.left (by omega)
        (fun h => absurd h (by simp)) hI2.r15 hI2.lo (fun h => absurd h (by simp))
        (fun x hx => hI2.mem.res x hx) (fun j hj => absurd hj (by simp)) (fun j hj => absurd hj (Nat.not_lt_zero _))
        (fun j _ hj => absurd hj (Nat.not_lt_zero _)) (fun _ _ => rfl) ?_
      intro s3 h1 h2 h3 h4 hO hR hM
      have := hepi' [] σ2 s3 ?_ (hI2.mem.only_res hG hO (fun x a b => Layout.inRes_of a b))
        (hS2.trans ⟨h1, h2, h4, by rw [h3]; exact Nat.le_refl _, Pres.of_res hO fun x a b => Layout.inRes_of a b⟩)
        ⟨fun j hj => hR j (by rw [hnr]; omega), fun j h1 h2 => hM j h1 (by omega), Nat.zero_le _⟩
      · rw [Code.label (i := 0) cR rfl, Nat.add_zero] at this
        exact this
      · rcases hr with hr | hr <;> exact hrun _ _ hr
    refine hE fd.body ctx F' 0 _ hT (by simp only [maxOff]; omega) c2.left (by rw [hnl]; exact hbody)
      ⟨by rw [hnr]; exact Nat.le_refl _, by rw [hnr]; exact hnr', by rw [hnrt]; exact hTree,
        fun hl => by rw [hleaf] at hl; simpa using hl⟩
      (by rw [hnl, hnr]; exact htmp) _ s6 Q hI6 (by rw [r3]; exact hfuel) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro σ2 d2 hr hI2 hS2
      have := hZ σ2 d2 (.inl hr) hI2 hS2
      rw [Code.label (i := 0) c3 rfl, Nat.add_zero] at this
      exact this
    · intro σ2 d2 hr hI2 hS2
      rw [hbrk]; exact hZ σ2 d2 (.inr hr) hI2 hS2
    · exact fun v σ2 d2 hr hm2 hS2 hv => hepi' v σ2 d2 (hrun _ _ hr) hm2 hS2 (by rw [← hnr]; exact hv)
    · intro d2 ⟨e, hr, hne⟩ hG2
      refine herr d2 ⟨e, ?_, hne⟩ ⟨hG2.rbp.trans r2, hP6.trans (htop ▸ hG2.mem)⟩
      rw [invoke_eq vs hlk, callFn_run]
      have : (exec p n fd.body).run σ0 = .error e := hr
      rw [exec_da_error hR hag this]
    · exact fun d2 hG2 => hexh d2 ⟨hG2.rbp.trans r2, hP6.trans (htop ▸ hG2.mem)⟩
    · intro Fw hFw
      have e := htF Fw hFw
      refine ⟨e, fun vs' σ2 d2 ra hr hm2 hT2 hO hra => ?_⟩
      rw [e] at hFw
      exact htail vs' σ2 d2 ra hFw (hrun _ _ hr) hm2 (S46.trans_t hT2) (by rw [← hnr]; exact hO) (htop ▸ hra)
  -- the parameters are in place: the state `s5`
  have hmapped : ∀ x < fd.nlocals, ctx.alloc.lookup x = none → ∀ t < 8,
      (s4.dmem.get? (A (sp + 8 * x + t))).isSome := fun x hx hn t ht => by
    have := hslot x hx hn
    exact hmem.stack _ ⟨by omega, by omega⟩
  have H5 : ∀ s5 : MachineData, s5.regs.rsp = s4.regs.rsp → s5.regs.rbp = s4.regs.rbp →
      s5.regs.r14 = s4.regs.r14 → s5.regs.r15 = s4.regs.r15 →
      (∀ x r, ctx.alloc.lookup x = some r → s5.regs.get64 r = s4.regs.get64 r) →
      (ctx.treg ≠ none → s5.regs.rsi = s4.regs.rsi) →
      (s5.dmem = s4.dmem ∨ (Only sp (sp + 8 * fd.nparams) s4.dmem s5.dmem ∧ fd.nlocals ≤ F')) →
      ((∀ x < fd.nlocals, (ctx.alloc.lookup x).isSome) → s5.dmem = s4.dmem) →
      (∀ x < fd.nparams, ctx.alloc.lookup x = none → rdW s5.dmem (A (sp + 8 * x)) = some (vs.getD x 0)) →
      Ev Q s5 (at_ (k4 + (if fd.nparams ≤ argRegs.length then storeParams ctx 0 (argRegs.take fd.nparams)
        else copyParams 0 fd.nparams).length)) := by
    intro s5 q1 q2 q3 q4 hR5 hbx5 hD5 hall5 hv5
    have c1 := hc.right.left
    refine sim_zeroLocals ctx need hok.reg hok.inj sp Q (fd.nlocals - fd.nparams) fd.nparams _ s5 c1
      (by rw [q1]; exact hsp) ?_ ?_
    · intro x h1 h2 hn
      have hx := hslot x (by omega) hn
      refine ⟨by omega, by omega, fun t ht => ?_⟩
      have h4 := hmapped x (by omega) hn t ht
      rcases hD5 with h | ⟨h, _⟩
      · rw [h]; exact h4
      · exact h.grows _ h4
    intro s6 hO6 hall6 hz6 hzr6 hk6
    have hfx : ∀ r, r ∉ allocRegs → s6.regs.get64 r = s5.regs.get64 r := fun r hr =>
      hk6 r fun x _ _ _ => hfix r hr x
    have e1 : s6.regs.rsp = s4.regs.rsp := (UInt64.toBitVec_inj.mp (hfx .rsp (by decide))).trans q1
    have e2 : s6.regs.rbp = s4.regs.rbp := (UInt64.toBitVec_inj.mp (hfx .rbp (by decide))).trans q2
    have e3 : s6.regs.r14 = s4.regs.r14 := (UInt64.toBitVec_inj.mp (hfx .r14 (by decide))).trans q3
    have e4 : s6.regs.r15 = s4.regs.r15 := (UInt64.toBitVec_inj.mp (hfx .r15 (by decide))).trans q4
    have hD6 : s6.dmem = s4.dmem ∨ (Only sp (sp + 8 * fd.nlocals) s4.dmem s6.dmem ∧ fd.nlocals ≤ F') := by
      rcases hframe with hall | hle
      · left
        rw [hall6 fun x h1 h2 => hall x (by omega), hall5 hall]
      · right
        refine ⟨?_, hle⟩
        rcases hD5 with h | ⟨h, _⟩
        · rw [← h]; exact hO6.mono (by omega) (by omega)
        · exact h.union hO6 (by omega) (by omega) (by omega) (by omega)
    have hm6 : MemRel G σ.mem s6.dmem := by
      rcases hD6 with h | ⟨h, hle⟩
      · rw [h]; exact hmem
      · exact hmem.only hG h fun z h1 h2 => ⟨by omega, by omega⟩
    have hmap6 : ∀ x < fd.nlocals, ctx.alloc.lookup x = none → ∀ t < 8,
        (s6.dmem.get? (A (sp + 8 * x + t))).isSome := fun x hx hn t ht => by
      rcases hD6 with h | ⟨h, _⟩
      · rw [h]; exact hmapped x hx hn t ht
      · exact h.grows _ (hmapped x hx hn t ht)
    -- the L state: a local that is not zeroed holds what its register or slot holds
    obtain ⟨σ0, hσ0d⟩ : ∃ σ0 : St, σ0 = { mem := σ.mem, loc := fun x =>
        (if x < fd.nlocals ∧ fd.nparams ≤ x ∧ need.contains x = false then
          (match ctx.alloc.lookup x with
           | some r => UInt64.ofBitVec (s6.regs.get64 r)
           | none => (rdW s6.dmem (A (sp + 8 * x))).getD 0)
          else Locals.init vs x) } := ⟨_, rfl⟩
    have hσ0 : ∀ x, ¬(x < fd.nlocals ∧ fd.nparams ≤ x ∧ need.contains x = false) →
        σ0.loc x = Locals.init vs x := fun x h => by rw [hσ0d]; exact if_neg h
    have hσr : ∀ x r, (x < fd.nlocals ∧ fd.nparams ≤ x ∧ need.contains x = false) →
        ctx.alloc.lookup x = some r → σ0.loc x = UInt64.ofBitVec (s6.regs.get64 r) := fun x r h hr => by
      rw [hσ0d]; simp only [if_pos h, hr]
    have hσs : ∀ x, (x < fd.nlocals ∧ fd.nparams ≤ x ∧ need.contains x = false) →
        ctx.alloc.lookup x = none → σ0.loc x = (rdW s6.dmem (A (sp + 8 * x))).getD 0 := fun x h hn => by
      rw [hσ0d]; simp only [if_pos h, hn]
    have hσm : σ0.mem = σ.mem := by rw [hσ0d]
    have hzero : ∀ x, x < fd.nlocals → ¬ x < fd.nparams →
        ¬(x < fd.nlocals ∧ fd.nparams ≤ x ∧ need.contains x = false) → need.contains x = true := by
      intro x h1 h2 h3
      cases hc : need.contains x
      · exact absurd ⟨h1, by omega, hc⟩ h3
      · rfl
    have hag : DaAg (fun x => x ∈ need ∨ fd.nlocals ≤ x) (List.range fd.nparams) σ0
        { σ with loc := Locals.init vs } := by
      refine ⟨hσm, fun x hx => hσ0 x ?_⟩
      rintro ⟨h1, h2, h3⟩
      rcases hx with hx | hx | hx
      · simp only [List.mem_range] at hx; omega
      · rw [List.contains_iff_mem.mpr hx] at h3; cases h3
      · omega
    refine ev_congr (H σ0 s6 hag e1 e2 e3 e4 ?_ ⟨?_, ?_, ?_, ?_, ?_, hok, ?_, ?_, hσm ▸ hm6, ?_⟩) ?_
    · rcases hD6 with h | ⟨h, hle⟩
      · rw [h]; exact Pres.refl _ _
      · exact Pres.of_only h (by omega) (by simp only [top]; omega)
    · rw [e4]; exact h15
    · rw [e1, hsp]; exact hlo
    · intro hl; rw [e1, hsp]; rw [hleaf] at hl; exact hlo8 (by simpa using hl)
    · rw [e1, hsp]; exact hhi
    · rw [hnl]; exact hslot
    · intro x hx r hr
      rw [hnl] at hx
      by_cases hc : x < fd.nlocals ∧ fd.nparams ≤ x ∧ need.contains x = false
      · rw [hσr x r hc hr]
      rw [hσ0 x hc]
      by_cases hxp : x < fd.nparams
      · have hne : ctx.alloc ≠ [] := fun h => by simp [h] at hr
        have hnp6 := hspec.np hne
        rw [hk6 r fun y (hy1 : fd.nparams ≤ y) _ _ hy => absurd (hok.inj y x r hy hr) (by lomega), hR5 x r hr,
          ← hspec.arg x r hr hxp, hregs hnp6 x (by omega)]
        simp [Locals.init, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show x < vs.length by omega)]
      · rw [hzr6 x r (by omega) (by omega) (hzero x hx hxp hc) hr]
        simp only [Locals.init, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show vs.length ≤ x by omega)]
        rfl
    · intro x hx hn
      rw [hnl] at hx
      rw [e1, hsp]
      by_cases hc : x < fd.nlocals ∧ fd.nparams ≤ x ∧ need.contains x = false
      · have hx8 := hslot x hx hn
        have hsome : (rdW s6.dmem (A (sp + 8 * x))).isSome :=
          isSome_rdW fun t ht => by rw [A_add]; exact hmap6 x hx hn t ht
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
        rw [hσs x hc hn, hv]; rfl
      rw [hσ0 x hc]
      by_cases hxp : x < fd.nparams
      · have hx8 := hslot x hx hn
        have := hO6.rdW_eq (x := sp + 8 * x) (by omega) (by omega)
        rw [this, hv5 x hxp hn]; rfl
      · rw [hz6 x (by omega) (by omega) (hzero x hx hxp hc) hn]
        simp only [Locals.init, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show vs.length ≤ x by omega)]
        rfl
    · intro x hx
      have hxp : x < fd.nparams := (tregOf_spec fd x (by rw [hctx] at hx; simpa [fnCtx] using hx)).1
      rw [hσ0 x (fun h => Nat.not_lt.mpr h.2.1 hxp)]
      rw [rsi_of_get64 (hk6 .rsi fun y _ _ _ => hok.trsi (by simp [hx]) y), hbx5 (by simp [hx]), htr x hx]
      rfl
    · rfl
  by_cases hnp6 : fd.nparams ≤ argRegs.length
  · have c0 := hc.left
    simp only [hnp6, ite_true] at c0 H5
    have hlen : (argRegs.take fd.nparams).length = fd.nparams := by simp; omega
    refine sim_storeParams ctx sp Q (argRegs.take fd.nparams) 0 k4 s4 c0 hsp ?_ ?_
    · intro x h1 h2 hn
      rw [hlen] at h2
      have hx := hslot x (by omega) hn
      exact ⟨by omega, by omega, hmapped x (by omega) hn⟩
    intro s5 hr5 hO5 hall5 hv5
    rw [hlen] at hO5 hall5 hv5
    refine ev_congr (H5 s5 (by rw [hr5]) (by rw [hr5]) (by rw [hr5]) (by rw [hr5]) (fun x r _ => by rw [hr5])
      (fun _ => by rw [hr5]) ?_ (fun hall => hall5 fun x _ h2 => hall x (by omega)) ?_) rfl
    · rcases hframe with hall | hle
      · left; exact hall5 fun x _ h2 => hall x (by omega)
      · right; exact ⟨by simpa using hO5, hle⟩
    · intro x hx hn
      have htk : (argRegs.take fd.nparams).getD (x - 0) .rax = argRegs.getD x .rax := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_take, hx]
      rw [hv5 x (Nat.zero_le _) (by omega) hn, htk, hregs hnp6 x (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show x < vs.length by omega)]
  · have c0 := hc.left
    simp only [hnp6, ite_false] at c0 H5
    have hal : ctx.alloc = [] := Classical.byContradiction fun h => hnp6 (hspec.np h)
    have hm := hmargs (by omega)
    have hnlF : fd.nlocals ≤ F' := by
      have := hslot (fd.nlocals - 1) (by omega) (by simp [hal])
      omega
    refine sim_copy vs sp s4.regs.rsi.toNat Q fd.nparams 0 k4 s4 c0 (by omega) (by omega) hsp rfl
      (fun j hj _ => hm.1 j hj) (by rcases hm.2.1 with h | h; exact .inr (.inl (by omega)); exact .inr (.inr (by omega)))
      (by omega) (by omega) (fun j _ hj => isSome_rdW fun t ht => by
        rw [A_add]; exact hmapped j (by omega) (by simp [hal]) t ht) ?_
    intro s5 q1 q2 q3 q4 q5 hO5 hsl5
    have htn : ctx.treg = none := by rw [hctx]; simp [fnCtx, tregOf]; omega
    refine ev_congr (H5 s5 q1 q4 q5 q3 (fun x r h => by simp [hal] at h) (fun h => absurd htn h)
      (.inr ⟨by simpa using hO5, hnlF⟩)
      (fun hall => absurd (hall 0 (by omega)) (by simp [hal])) ?_) (by rw [copyParams_length])
    intro x hx _
    rw [hsl5 x (by omega) (Nat.zero_le _) (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show x < vs.length by omega)]

/-- A function's body (`fnBody`) from the state `s4` after its prologue: the tier local's tier
into `rsi` (`tregEntry`), then `fnBody0`. -/
theorem sim_fnBody (t : NTree)
    (hTree : ∀ g fd, p.lookup g = some fd → nrOf t G.tab g = Stmt.nret fd.body) (n : Nat)
    (hE : ExecSim p G n) (f : FnName) (fd : FunDecl) (hlk : p.lookup f = some fd)
    (hnp : fd.nparams ≤ fd.nlocals) (hbody : Stmt.wf p fd.nlocals G.tab fd.body = true)
    (vs : List Word) (σ : St) (hvl : vs.length = fd.nparams)
    (F' : Nat) (hF'off : 8 * F' + 8 < maxOff)
    (htmp : TmpFit fd.nlocals F' 0 (tempsS (fnCtx G.tab t f fd).alloc (Stmt.nret fd.body) fd.body))
    (hslot : ∀ x < fd.nlocals, (fnCtx G.tab t f fd).alloc.lookup x = none → x < F')
    (hframe : (∀ x < fd.nlocals, ((fnCtx G.tab t f fd).alloc.lookup x).isSome) ∨ fd.nlocals ≤ F')
    (s4 : MachineData) (k4 : Nat) (hc : Code (fnBody (fnCtx G.tab t f fd) fd) k4)
    (hlo : G.lo ≤ s4.regs.rsp.toNat) (hlo8 : Stmt.calls fd.body = true → G.lo + 8 ≤ s4.regs.rsp.toNat)
    (hhi : s4.regs.rsp.toNat + 8 * F' + 8 ≤ G.hi) (h15 : s4.regs.r15.toNat = G.T)
    (hmem : MemRel G σ.mem s4.dmem) (hfuel : s4.regs.r14.toNat < n)
    (hregs : fd.nparams ≤ argRegs.length → ∀ i (h : i < vs.length),
      s4.regs.get64 (argRegs.getD i .rax) = vs[i].toBitVec)
    (hmargs : argRegs.length < fd.nparams →
      (∀ i (h : i < vs.length), rdW s4.dmem (A (s4.regs.rsi.toNat + 8 * i)) = some vs[i]) ∧
      (s4.regs.rsp.toNat + 8 * fd.nlocals ≤ s4.regs.rsi.toNat ∨
        s4.regs.rsi.toNat + 8 * vs.length ≤ s4.regs.rsp.toNat) ∧
      s4.regs.rsi.toNat + 8 * vs.length ≤ 2 ^ 64)
    (Q : MachineState → Prop)
    (hepi : ∀ (r : List Word) (σ2 : St) (d2 : MachineData),
      (invoke p (exec p n) f vs).run σ = .ok (r, { σ2 with loc := σ.loc }) →
      MemRel G σ2.mem d2.dmem → SPost G F' s4 d2 → ResOut G (Stmt.nret fd.body) r d2 →
      Ev Q d2 (at_ (k4 + (fnBody (fnCtx G.tab t f fd) fd).length)))
    (herr : ∀ d2, (∃ e, (invoke p (exec p n) f vs).run σ = .error e ∧ e ≠ .outOfFuel) →
      GPost G (top s4 F') s4 d2 → Ev Q d2 (label errorL))
    (hexh : ∀ d2, GPost G (top s4 F') s4 d2 → Ev Q d2 (label exhaustedL))
    (htF : ∀ Fw, (fnCtx G.tab t f fd).tailF = some Fw → Fw = F')
    (htail : ∀ (r : List Word) (σ2 : St) (d2 : MachineData) (ra : Word),
      (fnCtx G.tab t f fd).tailF = some F' →
      (invoke p (exec p n) f vs).run σ = .ok (r, { σ2 with loc := σ.loc }) →
      MemRel G σ2.mem d2.dmem → TPost G F' s4 d2 → ResOut G (Stmt.nret fd.body) r d2 →
      rdW d2.dmem (A (top s4 F')) = some ra → Ev Q d2 (Int64.ofBitVec ra.toBitVec)) :
    Ev Q s4 (at_ k4) := by
  simp only [fnBody] at hc hepi
  cases ht : (fnCtx G.tab t f fd).treg with
  | none =>
    have he : tregEntry (fnCtx G.tab t f fd) = [] := by simp [tregEntry, ht]
    rw [he, List.nil_append] at hc hepi
    exact sim_fnBody0 hG hTab p t hTree n hE f fd hlk hnp hbody vs σ hvl F' hF'off htmp hslot hframe s4 k4 hc
      (fun x hx => by simp [ht] at hx) hlo hlo8 hhi h15 hmem hfuel hregs hmargs Q hepi herr hexh htF htail
  | some x =>
    obtain ⟨hxn, hn6, -, -⟩ := tregOf_spec fd x (by simpa [fnCtx] using ht)
    have he : tregEntry (fnCtx G.tab t f fd) =
        [movRR .rsi (argRegs.getD x .rdi), i64 (.and (.reg (rr .rsi)) (.imm (.int64 (1 : Word).toInt64)))] := by
      simp [tregEntry, ht]
    rw [he] at hc hepi
    have hxv : x < vs.length := hvl ▸ hxn
    have hx6 : x < argRegs.length := Nat.lt_trans hxn hn6
    have hv : s4.regs.get64 (argRegs.getD x .rdi) = vs[x].toBitVec := by
      rw [show argRegs.getD x .rdi = argRegs.getD x .rax by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx6]]
      exact hregs (Nat.le_of_lt hn6) x hxv
    have hnb : ∀ i, i < 5 → argRegs.getD i .rax ≠ .rsi := by decide
    have hl6 : argRegs.length = 6 := rfl
    refine ev_movRR hc.left.head ?_
    refine ev_aluRI (op := .and) (w := 1) rfl hc.left.tail.head fun st => ?_
    simp only [rget_set, ↓reduceIte, set64_set64, hv, UInt64.ofBitVec_toBitVec, BinOp.eval]
    have hS : SPost G F' s4 { s4 with regs := s4.regs.set64 .rsi (vs[x] &&& 1).toBitVec, status := st } :=
      SPost.regs rfl rfl rfl (Nat.le_refl _)
    refine ev_congr (sim_fnBody0 hG hTab p t hTree n hE f fd hlk hnp hbody vs σ hvl F' hF'off htmp hslot hframe
      { s4 with regs := s4.regs.set64 .rsi (vs[x] &&& 1).toBitVec, status := st } (k4 + 2) hc.right ?_
      hlo hlo8 hhi h15 hmem hfuel ?_ (fun h => absurd h (by omega)) Q ?_ ?_ ?_ htF ?_) ?_
    · intro y hy
      rw [ht] at hy; cases hy
      simp [Reg64s.set64, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxv]
    · intro h i hi
      rw [rget_set, if_neg (hnb i (by omega))]
      exact hregs h i hi
    · intro r σ2 d2 h1 h2 h3 h4
      refine ev_congr (hepi r σ2 d2 h1 h2 (hS.trans h3) h4) ?_
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro d2 he hG2
      exact herr d2 he ⟨by simpa [Reg64s.set64] using hG2.rbp, by simpa [top, Reg64s.set64] using hG2.mem⟩
    · intro d2 hG2
      exact hexh d2 ⟨by simpa [Reg64s.set64] using hG2.rbp, by simpa [top, Reg64s.set64] using hG2.mem⟩
    · intro r σ2 d2 ra h0 h1 h2 h3 h4 h5
      exact htail r σ2 d2 ra h0 h1 h2 ⟨by simpa [top, Reg64s.set64] using h3.rsp,
        by simpa [Reg64s.set64] using h3.rbp, by simpa [Reg64s.set64] using h3.r15,
        by simpa [Reg64s.set64] using h3.r14, by simpa [top, Reg64s.set64] using h3.mem⟩ h4
        (by simpa [top, Reg64s.set64] using h5)
    · rfl

theorem funSim (hwfp : ∀ f fd, p.lookup f = some fd → FunDecl.wf p G.tab fd = true) (t : NTree)
    (hTree : ∀ g fd, p.lookup g = some fd → nrOf t G.tab g = Stmt.nret fd.body) (n : Nat)
    (hE : ExecSim p G n) : FunSim p G t n := by
  intro f fd kf hlk hkf vs σ d ra Q hvl hra hargs hlo hhi h15 hmem hfuel hKret hKerr hKexh
  have hwf := hwfp f fd hlk
  simp only [FunDecl.wf_eq, FunDecl.wfSpec, Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨hnp, hbody⟩, hFoff⟩ := hwf
  simp only [maxOff] at hFoff
  have hhi2 := hG.hi_le
  have hspec := fnCtx_spec G.tab t f fd
  have hFle := tempsS_le (fnCtx G.tab t f fd).alloc (Stmt.nret fd.body) fd.body
  simp only [frameWords] at hFoff
  obtain ⟨hregs, hmargs⟩ := hargs
  have hvl' := hvl
  dsimp only [compileFn] at hkf
  split at hkf
  · -- a frameless leaf
    rename_i hfl
    simp only [frameless, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hfl
    obtain ⟨⟨hleaf, hall⟩, ht0⟩ := hfl
    have hleaf' : Stmt.calls fd.body = false := by simpa [fnCtx] using hleaf
    have hnp6 : fd.nparams ≤ argRegs.length := by
      by_cases h0 : fd.nlocals = 0
      · omega
      · have := hall 0 (by omega)
        exact hspec.np fun h => by simp [h] at this
    simp only [List.append_assoc, List.singleton_append] at hkf
    refine ev_label hkf.head ?_
    have cB := hkf.tail
    refine sim_fnBody hG hTab p t hTree n hE f fd hlk hnp hbody vs σ hvl 0 (by simp [maxOff])
      (.inl ht0) (fun x hx hn => by have := hall x hx; simp [hn] at this) (.inl hall) d (kf + 1) cB.left hlo
      (fun hc => by simp [hc] at hleaf') (by omega) h15 hmem hfuel (fun _ => hregs (by omega))
      (fun h => absurd h (by omega)) Q ?_ ?_ ?_ ?_ ?_
    · intro r σ2 d2 hr hm2 hS2 hrax
      have hP2 : Pres G d.regs.rsp.toNat d.dmem d2.dmem := by simpa [top] using hS2.mem
      have hsp2 := congrArg UInt64.toNat hS2.rsp
      refine ev_ret cB.right.head (ra := ra) ?_ ?_
      · rw [hS2.rsp, show d.regs.rsp.toBitVec = A d.regs.rsp.toNat by simp [A],
          rdW_of_pres hG hP2 (by omega) (Nat.le_refl _) (by omega)]; exact hra
      · refine hKret r { σ2 with loc := σ.loc } _ hr hm2 rfl ?_ ?_ ?_ ?_ ?_ hP2
        · simp only [Reg64s.set64_rsp, Reg64s.get64_rsp, UInt64.toNat_ofBitVec, BitVec.toNat_add,
            UInt64.toNat_toBitVec, hsp2, BitVec.toNat_ofNat]
          rw [show BitVec.toNat (8 : BitVec 64) = 8 from rfl]; omega
        · simp [Reg64s.set64_rsp]; exact hS2.rbp
        · simp [Reg64s.set64_rsp]; exact hS2.r15
        · simp [Reg64s.set64_rsp]; exact hS2.r14
        · exact ⟨hrax.1.set64 (r := .rsp) (by simp) _, hrax.2⟩
    · exact fun d2 he hG2 => hKerr d2 he ⟨hG2.rbp, by simpa [top] using hG2.mem⟩
    · exact fun d2 hG2 => hKexh d2 ⟨hG2.rbp, by simpa [top] using hG2.mem⟩
    · intro Fw h; simp [fnCtx, hleaf'] at h
    · intro _ _ _ _ h; simp [fnCtx, hleaf'] at h
  -- a frame of `F` words, after the stack check
  rename_i hfl
  generalize hF : fd.nlocals + tempsS (fnCtx G.tab t f fd).alloc (fnCtx G.tab t f fd).nr fd.body = F at hkf
  have hnrF : (fnCtx G.tab t f fd).nr = Stmt.nret fd.body := rfl
  rw [hnrF] at hF
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hkf
  refine ev_label hkf.head ?_
  have c1 := hkf.tail
  refine ev_movRR c1.head ?_
  refine ev_subRM c1.tail.head ⟨by simp [Tab.stackLimit], by simp [Tab.stackLimit]⟩ (v := UInt64.ofNat G.lo)
    ?_ fun st1 => ?_
  · simp only [Reg64s.set64_rax, Tab.stackLimit]
    rw [h15]; exact hmem.limit
  refine ev_cmpRI c1.tail.tail.head ?_
  refine ev_jcc c1.tail.tail.tail.head (fun hcc => ?_) (fun hcc => ?_)
  · exact hKexh _ ⟨by simp, Pres.refl _ _⟩
  simp only [Reg64s.set64_rax, Reg64s.get64_rax, Reg64s.get64_rsp, CondCode.interp, cmpFlags_cf,
    decide_eq_false_iff_not] at hcc
  have hlo' : (UInt64.ofNat G.lo).toNat = G.lo := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hgap : 8 * F + 8 ≤ d.regs.rsp.toNat - G.lo := by
    simp only [BitVec.toNat_sub, UInt64.toNat_toBitVec, hlo'] at hcc
    have : (Int64.ofInt (8 * ↑F + 8)).toBitVec.toNat = 8 * F + 8 := by
      simp [Int64.toBitVec_ofInt]; omega
    rw [this] at hcc
    omega
  have hnlF : fd.nlocals ≤ F := by omega
  suffices H : ∀ s4 : MachineData, s4.regs.rsp.toNat = d.regs.rsp.toNat - 8 * F →
      s4.regs.rsi = d.regs.rsi → s4.regs.r15 = d.regs.r15 → s4.regs.rbp = d.regs.rbp →
      s4.regs.r14 = d.regs.r14 → s4.dmem = d.dmem → (∀ r ∈ allocRegs, s4.regs.get64 r = d.regs.get64 r) →
      Ev Q s4 (at_ (kf + 1 + 1 + 1 + 1 + 1 + 1)) by
    refine ev_subRI c1.tail.tail.tail.tail.head fun st2 => H _ ?_ (by simp) (by simp) (by simp) (by simp) (by simp)
      (by intro r hr; have hne := allocRegs_ne hr; simp only [rget_set]; simp [hne.1, hne.2.2.2.1])
    simp [Int64.toBitVec_ofInt, BitVec.toNat_sub]
    have hm : ((8 : UInt64) * OfNat.ofNat F).toNat = 8 * F := by
      simp [UInt64.toNat_mul]
      rw [UInt64.toNat_ofNat_of_lt (by simp [UInt64.size]; omega)]
      omega
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hm]; omega), hm]
  intro s4 h4sp h4si h415 h4bp h414 h4m h4r
  have c2 := c1.tail.tail.tail.tail.tail
  refine sim_fnBody hG hTab p t hTree n hE f fd hlk hnp hbody vs σ hvl F (by simp only [maxOff]; omega)
    (.inr (by omega)) (fun x hx _ => by omega) (.inr hnlF) s4 _ c2.left (by omega) (fun _ => by omega)
    (by omega) (by rw [h415]; exact h15) (by rw [h4m]; exact hmem) (by rw [h414]; exact hfuel)
    (fun h i hi => by rw [h4r _ (argRegs_getD_mem i (by omega))]; exact hregs (by omega) i hi)
    (fun h => by
      obtain ⟨m1, m2, m3⟩ := hmargs (by omega)
      refine ⟨fun i hi => by rw [h4m, h4si]; exact m1 i hi, ?_, by rw [h4si]; omega⟩
      rw [h4sp, h4si]; omega) Q ?_ ?_ ?_ ?_ ?_
  · intro r σ2 d2 hr hm2 hS2 hrax
    have hP2 : Pres G d.regs.rsp.toNat d.dmem d2.dmem := by
      have := hS2.mem; rw [h4m] at this; simpa [top, h4sp, show d.regs.rsp.toNat - 8 * F + 8 * F = d.regs.rsp.toNat by omega] using this
    have h2sp : d2.regs.rsp.toNat = d.regs.rsp.toNat - 8 * F := by
      rw [congrArg UInt64.toNat hS2.rsp]; exact h4sp
    have cR := c2.right
    refine ev_addRI cR.head fun st => ?_
    have hadd' : d2.regs.rsp.toBitVec + (Int64.ofInt (8 * ↑F)).toBitVec = A d.regs.rsp.toNat := by
      rw [show (8 * (F : Int)) = ((8 * F : Nat) : Int) by push_cast; rfl, int64_ofInt_toBitVec]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, A]
      omega
    refine ev_ret cR.tail.head (ra := ra) ?_ ?_
    · simp only [Reg64s.set64_rsp, Reg64s.get64_rsp]
      rw [hadd', rdW_of_pres hG hP2 (by omega) (by omega) (by omega)]; exact hra
    · refine hKret r { σ2 with loc := σ.loc } _ hr hm2 rfl ?_ ?_ ?_ ?_ ?_ hP2
      · simp only [Reg64s.set64_rsp, Reg64s.get64_rsp, UInt64.toBitVec_ofBitVec, hadd']
        simp only [UInt64.toNat_ofBitVec, BitVec.toNat_add, A, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
        omega
      · simp; exact hS2.rbp.trans h4bp
      · simp; exact hS2.r15.trans h415
      · simp; have := hS2.r14; rw [h414] at this; exact this
      · exact ⟨(hrax.1.set64 (r := .rsp) (by simp) _).set64 (r := .rsp) (by simp) _, hrax.2⟩
  · intro d2 he hG2
    refine hKerr d2 he ⟨hG2.rbp.trans h4bp, ?_⟩
    have := hG2.mem; rw [h4m] at this; simpa [top, h4sp, show d.regs.rsp.toNat - 8 * F + 8 * F = d.regs.rsp.toNat by omega] using this
  · intro d2 hG2
    refine hKexh d2 ⟨hG2.rbp.trans h4bp, ?_⟩
    have := hG2.mem; rw [h4m] at this; simpa [top, h4sp, show d.regs.rsp.toNat - 8 * F + 8 * F = d.regs.rsp.toNat by omega] using this
  · intro Fw h
    have ht : (fnCtx G.tab t f fd).tailF = if Stmt.calls fd.body then
        some (fd.nlocals + tempsS (fnCtx G.tab t f fd).alloc (Stmt.nret fd.body) fd.body) else none := rfl
    rw [ht] at h
    split at h
    · cases h; exact hF
    · cases h
  · intro r σ2 d2 ra' _ hr hm2 hT2 hO hra'
    have htop : top s4 F = d.regs.rsp.toNat := by simp only [top, h4sp]; omega
    have hP2 : Pres G d.regs.rsp.toNat d.dmem d2.dmem := by
      have := hT2.mem; rw [h4m, htop] at this; exact this
    have hra2 : ra' = ra := by
      rw [htop, rdW_of_pres hG hP2 (by omega) (Nat.le_refl _) (by omega), hra] at hra'
      cases hra'; rfl
    subst hra2
    refine hKret r { σ2 with loc := σ.loc } _ hr hm2 rfl ?_ (hT2.rbp.trans h4bp) (hT2.r15.trans h415)
      (by have := hT2.r14; rw [h414] at this; exact this) hO hP2
    rw [hT2.rsp, htop]

end

end L.Compiler
