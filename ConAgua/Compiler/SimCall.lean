module

public import ConAgua.Compiler.SimStmt

@[expose] public section

/-!
# Calls

`sim_args` evaluates the arguments into temporaries. `FunSim p G n` is the simulation of a call
of a function of `p` under `exec p n`: entered at its label with the return address at `rsp`
and the arguments at `rsi`, the code returns to the return address with L's result in `rax`, or
leaves through `ca_error`/`ca_exhausted`. `sim_ret` and `sim_storeRes` move results into and out
of the result registers.
-/

namespace L.Compiler

open L

attribute [local simp] Reg64s.set64_rax Reg64s.set64_rcx Reg64s.set64_rdx Reg64s.set64_rsi
  Reg64s.set64_rsp Reg64s.set64_r14

theorem callFn_run (K : Stmt → M Sig) (fd : FunDecl) (vs : List Word) (σ : St) :
    (callFn K fd vs).run σ =
      match (K fd.body).run { σ with loc := Locals.init vs } with
      | .ok (r, σ') => .ok (r.retVal, { σ' with loc := σ.loc })
      | .error e => .error e := by
  simp only [callFn, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_modify, pure, Except.pure,
    bind, Except.bind, StateT.bind, StateT.run, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set]
  rcases K fd.body { σ with loc := Locals.init vs } with e | ⟨r, σ'⟩ <;> rfl

theorem GPost.mono {G : Layout} {t t' : Nat} {d d' : MachineData} (h : GPost G t d d') (ht : t ≤ t') :
    GPost G t' d d' := ⟨h.rbp, h.mem.mono ht⟩

theorem GPost.pre {G : Layout} {t : Nat} {d d1 d2 : MachineData} (h1 : d1.regs.rbp = d.regs.rbp)
    (hm : Pres G t d.dmem d1.dmem) (h : GPost G t d1 d2) : GPost G t d d2 :=
  ⟨h.rbp.trans h1, hm.trans h.mem⟩

theorem evalArgsP_length {σ : St} {es : List Expr} {vs : List Word} (h : evalArgsP σ es = .ok vs) :
    vs.length = es.length := by
  induction es generalizing vs with
  | nil => simp [evalArgsP] at h; subst h; rfl
  | cons e es ih =>
    simp only [evalArgsP, bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hes; cases h; simp [ih hes]

/-- The simulation of every call of a function of `p` under `exec p n`, with fewer than `n` units
of machine fuel. -/
def FunSim [Host] (p : Prog) (G : Layout) (n : Nat) : Prop :=
  ∀ (f : FnName) (fd : FunDecl) (kf : Nat), p.lookup f = some fd → Code (compileFn G.tab f fd) kf →
  ∀ (vs : List Word) (σ : St) (d : MachineData) (ra : Word) (Q : MachineState → Prop),
    vs.length = fd.nparams →
    rdW d.dmem (A d.regs.rsp.toNat) = some ra →
    (∀ i (h : i < vs.length), rdW d.dmem (A (d.regs.rsi.toNat + 8 * i)) = some vs[i]) →
    (vs.length = 0 ∨ d.regs.rsp.toNat + 8 ≤ d.regs.rsi.toNat ∨ d.regs.rsi.toNat + 8 * vs.length ≤ G.lo) →
    d.regs.rsi.toNat + 8 * vs.length < 2 ^ 64 →
    G.lo ≤ d.regs.rsp.toNat → d.regs.rsp.toNat + 8 ≤ G.hi →
    d.regs.r15.toNat = G.T → MemRel G σ.mem d.dmem → d.regs.r14.toNat < n →
    (∀ r σ' d', (invoke p (exec p n) f vs).run σ = .ok (r, σ') → MemRel G σ'.mem d'.dmem →
      σ'.loc = σ.loc → d'.regs.rsp.toNat = d.regs.rsp.toNat + 8 → d'.regs.rbp = d.regs.rbp →
      d'.regs.r15 = d.regs.r15 → d'.regs.r14.toNat ≤ d.regs.r14.toNat → ResRel G.tab.nres r d'.regs →
      Pres G d.regs.rsp.toNat d.dmem d'.dmem → Ev Q d' (Int64.ofBitVec ra.toBitVec)) →
    (∀ d', (∃ x, (invoke p (exec p n) f vs).run σ = .error x ∧ x ≠ .outOfFuel) →
      GPost G d.regs.rsp.toNat d d' → Ev Q d' (label errorL)) →
    (∀ d', GPost G d.regs.rsp.toNat d d' → Ev Q d' (label exhaustedL)) →
    Ev Q d (at_ kf)

theorem bv_sub8 (x : UInt64) (h : 8 ≤ x.toNat) : x.toBitVec - 8 = A (x.toNat - 8) := by
  apply BitVec.eq_of_toNat_eq
  simp [A, BitVec.toNat_sub]
  omega

theorem toNat_sub8 (x : UInt64) (h : 8 ≤ x.toNat) : (UInt64.ofBitVec (x.toBitVec - 8)).toNat = x.toNat - 8 := by
  have := congrArg BitVec.toNat (bv_sub8 x h)
  simp only [A, BitVec.toNat_ofNat] at this
  simp only [UInt64.toNat_ofBitVec, this]
  have := x.toBitVec.isLt
  simp only [UInt64.toNat_toBitVec] at this
  omega

theorem UInt64.toNat_mk' (b : BitVec 64) : ({ toBitVec := b } : UInt64).toNat = b.toNat := rfl

/-- Arithmetic on machine addresses. -/
macro "addr_omega" : tactic => `(tactic| (simp only [UInt64.toNat_mk', BitVec.toNat_sub, A, BitVec.toNat_ofNat,
  UInt64.toNat_toBitVec, UInt64.toNat_ofBitVec] at *; omega))

theorem tempsArgs_ge (i : Nat) (args : List Expr) : i + args.length ≤ max i (tempsArgs i args) := by
  induction args generalizing i with
  | nil => simp [tempsArgs]
  | cons e es ih => simp only [tempsArgs, List.length_cons]; have := ih (i + 1); omega

theorem storeRes_length (xs : List Var) (i : Nat) : (storeRes xs i).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simp [storeRes, ih]

theorem loadRes_length (ctx : Ctx) (k i n : Nat) : (loadRes ctx k i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [loadRes, ih]

theorem resReg_keeps (R : Reg64s) (i : Nat) (v : BitVec 64) :
    (R.set64 (resReg i) v).rsp = R.rsp ∧ (R.set64 (resReg i) v).rbp = R.rbp ∧
    (R.set64 (resReg i) v).r14 = R.r14 ∧ (R.set64 (resReg i) v).r15 = R.r15 := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | _ + 5 => exact ⟨rfl, rfl, rfl, rfl⟩

theorem rres_eq_get64 (R : Reg64s) {i : Nat} (hi : i < maxRes) :
    (rres R i).toBitVec = R.get64 (resReg i) := by
  simp only [maxRes] at hi
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

section
variable [Host]

/-- Setting the result registers `i, …, i + n - 1` from the temporaries holding `vs` (and `0`
past the end of `vs`). -/
theorem sim_loadRes (ctx : Ctx) (vs : List Word) (Q : MachineState → Prop) :
    ∀ (n i k : Nat) (s : MachineData), Code (loadRes ctx vs.length i n) k → i + n ≤ maxRes →
    8 * (ctx.nl + i + n) < 2 ^ 31 →
    (∀ j (h : j < vs.length), rdW s.dmem (A (s.regs.rsp.toNat + 8 * (ctx.nl + j))) = some vs[j]) →
    (∀ j < i, rres s.regs j = vs.getD j 0) →
    (∀ R : Reg64s, R.rsp = s.regs.rsp → R.rbp = s.regs.rbp → R.r14 = s.regs.r14 → R.r15 = s.regs.r15 →
      (∀ j < i + n, rres R j = vs.getD j 0) → Ev Q { s with regs := R } (at_ (k + n))) →
    Ev Q s (at_ k) := by
  intro n
  induction n with
  | zero =>
    intro i k s _ _ _ _ hpre h
    exact h s.regs rfl rfl rfl rfl (by simpa using hpre)
  | succ n ih =>
    intro i k s hc hn hoff hsl hpre h
    simp only [loadRes] at hc
    have hstep : ∀ v : Word, v = vs.getD i 0 →
        Ev Q { s with regs := s.regs.set64 (resReg i) v.toBitVec } (at_ (k + 1)) := by
      intro v hv
      obtain ⟨h1, h2, h3, h4⟩ := resReg_keeps s.regs i v.toBitVec
      refine ih (i + 1) (k + 1) _ hc.tail (by omega) (by omega) (fun j hj => by rw [h1]; exact hsl j hj) ?_ ?_
      · intro j hj
        rw [rres_set64_resReg _ (by omega) (by omega)]
        split
        · subst_vars; simp
        · exact hpre j (by omega)
      · intro R r1 r2 r3 r4 hR
        exact ev_congr (h R (r1.trans h1) (r2.trans h2) (r3.trans h3) (r4.trans h4)
          fun j hj => hR j (by omega)) (by omega)
    by_cases hi : i < vs.length
    · simp only [hi, if_true] at hc
      refine ev_movRM hc.head ⟨by omega, by omega⟩ (v := vs[i]) ?_ (hstep _ (by simp [hi]))
      rw [slot_addr _ (ctx.nl + i) _ (by omega)]; exact hsl i hi
    · simp only [hi, if_false] at hc
      exact ev_movRI hc.head (hstep 0 (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi)]; rfl))

/-- Storing the result registers `i, i + 1, …` into the locals `xs`. -/
theorem sim_storeRes {G : Layout} (hG : G.Ok) (nl F : Nat) (Q : MachineState → Prop) :
    ∀ (xs : List Var) (i k : Nat) (σ : St) (rs : List Word) (s : MachineData),
    Code (storeRes xs i) k → xs.all (· < nl) = true → i + xs.length ≤ maxRes → 8 * nl < 2 ^ 31 →
    Inv G nl F σ s → (∀ j < xs.length, rres s.regs (i + j) = rs.getD j 0) →
    (∀ s', Inv G nl F (σ.setLocs xs rs) s' → s'.regs = s.regs → s'.status = s.status →
      Pres G (top s F) s.dmem s'.dmem → Ev Q s' (at_ (k + xs.length))) →
    Ev Q s (at_ k) := by
  intro xs
  induction xs with
  | nil =>
    intro i k σ rs s _ _ _ _ hI _ h
    exact h s hI rfl rfl (Pres.refl _ _)
  | cons x xs ih =>
    intro i k σ rs s hc hxs hn hoff hI hres h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hxs
    simp only [storeRes] at hc
    have hx := hxs.1
    have := hI.nlF
    refine ev_movMR hc.head ⟨by lomega, by lomega⟩ ?_ ?_
    · rw [slot_addr _ x _ (by omega)]; exact hI.mapped (by lomega)
    rw [slot_addr _ x _ (by omega)]
    have hv : s.regs.get64 (resReg i) = (rs.headD 0).toBitVec := by
      have h0 := hres 0 (by simp)
      rw [Nat.add_zero] at h0
      rw [← rres_eq_get64 _ (by simp at hn; omega), h0]
      cases rs <;> rfl
    rw [hv]
    have hI1 := hI.setLoc hG hx (rs.headD 0)
    refine ih (i + 1) (k + 1) _ rs.tail _ hc.tail hxs.2 (by simp at hn; omega) hoff hI1 ?_ ?_
    · intro j hj
      have := hres (j + 1) (by simp; omega)
      rw [show i + 1 + j = i + (j + 1) by omega]
      simp only at this ⊢
      rw [this]
      cases rs <;> simp
    · intro s' hI' hr hst hP
      refine ev_congr (h s' (by simpa [St.setLocs] using hI') hr hst ?_) (by simp; omega)
      refine (Pres.of_only (Only.wrW ?_) ?_ ?_).trans (by simpa [top] using hP)
      · have := hI.hi; have := hG.hi_le; lomega
      · have := hI.lo; omega
      · have := hI.hi; simp only [top]; lomega

end

section
variable [Host] {G : Layout} (hG : G.Ok) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords < maxOff) (p : Prog)
include hG hTab

theorem sim_args (ctx : Ctx) (hT : ctx.tab = G.tab) (F : Nat) (hF : 8 * F + 8 < maxOff) :
    ∀ (args : List Expr) (i k : Nat), Code (compileArgs ctx i args) k →
    args.all (Expr.wf ctx.nl G.tab) = true → ctx.nl + tempsArgs i args ≤ F →
    ∀ (σ : St) (s : MachineData) (Q : MachineState → Prop), Inv G ctx.nl F σ s →
    (∀ vs s', evalArgsP σ args = .ok vs → EPost ctx.nl F i s s' →
      (∀ j (h : j < vs.length), rdW s'.dmem (A (s.regs.rsp.toNat + 8 * (ctx.nl + i + j))) = some vs[j]) →
      Ev Q s' (at_ (k + (compileArgs ctx i args).length))) →
    (∀ s', (∃ x, evalArgsP σ args = .error x) → EPost ctx.nl F i s s' → Ev Q s' (label errorL)) →
    Ev Q s (at_ k) := by
  intro args
  induction args with
  | nil =>
    intro i k _ _ _ σ s Q _ hok _
    exact ev_congr (hok [] s rfl (EPost.refl _ _ _ _) (fun j h => absurd h (by simp))) (by simp [compileArgs])
  | cons e es ih =>
    intro i k hc hwf htmp σ s Q hI hok herr
    simp only [List.all_cons, Bool.and_eq_true] at hwf
    simp only [tempsArgs] at htmp
    simp only [compileArgs, List.append_assoc, List.singleton_append] at hc hok
    have hF' := hF; simp only [maxOff] at hF'
    have hsp := hI.hi
    have hhi := hG.hi_le
    refine sim_expr hG ctx hT hTab F hF e i k hc.left hwf.1 (by omega) σ s Q hI ?_ ?_
    · intro v s1 hv hrax1 hE1
      have hI1 : Inv G ctx.nl F σ s1 :=
        hI.only hG (hE1.mem.mono (by omega) (Nat.le_refl _)) hE1.rsp hE1.r15
      have hoff : SmallOff (8 * ((ctx.nl : Int) + (i : Int))) := ⟨by omega, by omega⟩
      refine ev_movMR hc.right.head hoff ?_ ?_
      · rw [slot_addr _ (ctx.nl + i) _ (by omega)]; exact hI1.mapped (by omega)
      rw [slot_addr _ (ctx.nl + i) _ (by omega)]
      have hE2 := hE1.trans (EPost.store (v := s1.regs.get64 .rax) (j := ctx.nl + i) (s := s1)
        (by omega) (by omega) (by rw [hE1.rsp]; omega)) (Nat.le_refl _)
      have hI2 := hI.only hG (hE2.mem.mono (by omega) (Nat.le_refl _)) hE2.rsp hE2.r15
      refine ih (i + 1) _ hc.right.tail hwf.2 (by omega) σ _ Q hI2 ?_ ?_
      · intro vs s3 hvs hE3 hslots
        have h1rsp := congrArg UInt64.toNat hE1.rsp
        have h2rsp := congrArg UInt64.toNat hE2.rsp
        refine ev_congr (hok (v :: vs) s3 (by simp [evalArgsP, hv, hvs]; rfl) (hE2.trans hE3 (by omega)) ?_) ?_
        · intro j hj
          cases j with
          | zero =>
            simp only [List.getElem_cons_zero]
            rw [hE3.mem.rdW_eq (by omega) (by rw [h2rsp]; omega)]
            simp [h1rsp, rdW_wrW_same, hrax1]
          | succ j =>
            simp only [List.getElem_cons_succ]
            have := hslots j (by simpa using hj)
            rw [h2rsp] at this
            rw [← this]; congr 2; omega
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · intro s3 herr3 hE3
        obtain ⟨x, hx⟩ := herr3
        exact herr s3 ⟨x, by simp [evalArgsP, hv, hx]; rfl⟩ (hE2.trans hE3 (by omega))
    · intro s1 herr1 hE1
      obtain ⟨x, hx⟩ := herr1
      exact herr s1 ⟨x, by simp [evalArgsP, hx]; rfl⟩ hE1

omit hTab in
theorem rdW_of_pres {t x : Nat} {d d' : DataMem} (hP : Pres G t d d') (hlo : G.lo ≤ t) (hx : t ≤ x)
    (hxs : x + 8 ≤ G.hi) : rdW d' (A x) = rdW d (A x) :=
  rdW_congr fun j hj => by
    have := hG.hi_le
    rw [A_add]
    exact hP.same _ (by omega) (by omega) (hG.notStack_of_arr' ⟨by omega, by omega⟩)

theorem sim_ret (K : Stmt → M Sig) (P : Nat → Prop) (es : List Expr) :
    SimS p G (stepRun p K) P (.ret es) := by
  intro ctx F path k hT hF hc hwf htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨hargs, hlen⟩, hres⟩ := hwf
  simp only [compileS, List.append_assoc] at hc hK
  simp only [tempsS] at htmp
  have hF' := hF; simp only [maxOff] at hF'
  have hlenT := tempsArgs_ge 0 es
  refine sim_args hG hTab ctx hT F hF es 0 k hc.left hargs htmp σ d Q hI ?_ ?_
  · intro vs s1 hvs hE1 hslots
    have hvl := evalArgsP_length hvs
    have hI1 := hI.only hG (hE1.mem.mono (by omega) (Nat.le_refl _)) hE1.rsp hE1.r15
    have hc2 := hc.right
    rw [hT, ← hvl] at hc2
    refine sim_loadRes ctx vs Q G.tab.nres 0 _ s1 hc2.left (by omega) (by simp only [maxRes] at hres; omega)
      (fun j hj => by rw [hE1.rsp]; simpa using hslots j hj) (fun j hj => absurd hj (Nat.not_lt_zero _)) ?_
    intro R h1 h2 h3 h4 hR
    have hj := hc2.right
    rw [loadRes_length] at hj
    refine ev_jmp hj.head (hK.ret vs σ _ (by simp [step_ret_run, hvs]; rfl)
      (hI1.of_regs rfl h1 h4) ((hE1.spost hI.lo).trans ?_) fun j hj => hR j (by omega))
    exact ⟨h1, h2, h4, by rw [h3]; exact Nat.le_refl _, Pres.refl _ _⟩
  · intro s1 herr hE1
    obtain ⟨y, hy⟩ := herr
    refine hK.err s1 ⟨y, by simp [step_ret_run, hy]; rfl, by rw [evalArgsP_error hy]; simp⟩
      (hE1.spost hI.lo).gpost

theorem sim_call (n : Nat) (hFun : FunSim p G n)
    (hProg : ∀ f fd, p.lookup f = some fd → ∃ kf, Code (compileFn G.tab f fd) kf)
    (xs : List Var) (f : FnName) (args : List Expr) :
    SimS p G (stepRun p (exec p n)) (· ≤ n) (.call xs f args) := by
  intro ctx F path k hT hF hc hwf htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨⟨⟨hxs, hxl⟩, hres⟩, hargs⟩, hfd⟩ := hwf
  cases hlk : p.lookup f with
  | none => simp [hlk] at hfd
  | some fd =>
  simp only [hlk, beq_iff_eq] at hfd
  obtain ⟨kf, hkf⟩ := hProg f fd hlk
  have hlf := Code.label (i := 0) hkf rfl
  simp only [compileS, burnFuel, List.append_assoc, List.cons_append, List.nil_append,
    List.singleton_append] at hc hK
  simp only [tempsS] at htmp
  have hF' := hF; simp only [maxOff] at hF'
  have hsp := hI.hi
  have hhi := hG.hi_le
  have hlo8 := hI.lo8
  have hnlF := hI.nlF
  have hlen := tempsArgs_ge 0 args
  have hcR := hc.right
  refine sim_args hG hTab ctx hT F hF args 0 k hc.left hargs htmp σ d Q hI ?_ ?_
  · intro vs s1 hvs hE1 hslots
    have hvl := evalArgsP_length hvs
    have h1rsp := congrArg UInt64.toNat hE1.rsp
    have hI1 := hI.only hG (hE1.mem.mono (by omega) (Nat.le_refl _)) hE1.rsp hE1.r15
    refine ev_lea hcR.head ⟨by omega, by omega⟩ ?_
    refine ev_sub1 hcR.tail.head fun st hst => ?_
    refine ev_jcc hcR.tail.tail.head (fun hcc => ?_) (fun hcc => ?_)
    · refine hK.exh _ ((hE1.spost hI.lo).trans_g ⟨by simp, Pres.refl _ _⟩)
    · simp only [CondCode.interp] at hcc
      rw [hst] at hcc
      have h0 : s1.regs.r14 ≠ 0 := by intro h; simp [h] at hcc
      have hpos : 0 < s1.regs.r14.toNat := by
        rcases Nat.eq_zero_or_pos s1.regs.r14.toNat with h | h
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) h0
        · exact h
      have hsp8 : 8 ≤ s1.regs.rsp.toNat := by omega
      refine ev_call hcR.tail.tail.tail.head ?_ ?_
      · simp only [Reg64s.set64_r14, Reg64s.set64_rsi]
        rw [bv_sub8 _ hsp8]
        refine isSome_rdW fun j hj => ?_
        rw [A_add]
        exact hI1.mem.stack _ ⟨by omega, by omega⟩
      rw [hlf, Nat.add_zero]
      refine hFun f fd kf hlk hkf vs σ _
        (UInt64.ofBitVec (at_ (k + (compileArgs ctx 0 args).length + 1 + 1 + 1 + 1)).toBitVec) Q
        (by rw [hvl, hfd]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals simp only [Reg64s.set64_rsp, Reg64s.set64_r14, Reg64s.set64_rsi, Reg64s.get64_rsp,
        Reg64s.get64_r14]
      · rw [bv_sub8 _ hsp8]
        rw [show (({ toBitVec := A (s1.regs.rsp.toNat - 8) } : UInt64).toNat) = s1.regs.rsp.toNat - 8 by
          addr_omega, rdW_wrW_same]
      · intro i hi
        have hsl := hslots i hi
        rw [bv_sub8 _ hsp8, rdW_wrW_A (by omega) (by addr_omega) (by addr_omega), ← hsl]
        congr 2; addr_omega
      · right; left; rw [bv_sub8 _ hsp8]; addr_omega
      · addr_omega
      · rw [bv_sub8 _ hsp8]; addr_omega
      · rw [bv_sub8 _ hsp8]; addr_omega
      · exact hI1.r15
      · rw [bv_sub8 _ hsp8]
        exact hI1.mem.only hG (Only.wrW (by omega)) fun z h1 h2 => ⟨by omega, by omega⟩
      · have := congrArg UInt64.toNat hE1.r14
        have h1 : ({ toBitVec := s1.regs.r14.toBitVec - 1 } : UInt64).toNat = s1.regs.r14.toNat - 1 :=
          u64_sub_one_toNat hpos
        rw [h1]; omega
      · intro r σ' d' hinv hmem hloc hrsp hrbp hr15 hr14 hrax hpres
        rw [Int64.ofBitVec_toBitVec]
        rw [bv_sub8 _ hsp8] at hpres hrsp
        have hlo1 := hI1.lo8
        have hhi1 := hI1.hi
        have hrsp' : d'.regs.rsp.toNat = s1.regs.rsp.toNat := by addr_omega
        have hrsp'' : d'.regs.rsp = d.regs.rsp := UInt64.toNat_inj.mp (by omega)
        have h4 : ({ toBitVec := A (s1.regs.rsp.toNat - 8) } : UInt64).toNat = s1.regs.rsp.toNat - 8 := by
          addr_omega
        rw [h4] at hpres
        have hpres1 : Pres G s1.regs.rsp.toNat s1.dmem
            (wrW s1.dmem (A (s1.regs.rsp.toNat - 8)) (at_ (k + (compileArgs ctx 0 args).length + 4)).toBitVec) :=
          Pres.of_only (Only.wrW (by omega)) (by omega) (by omega)
        have hId : Inv G ctx.nl F σ' d' := by
          refine ⟨by rw [hr15]; exact hI1.r15, by rw [hrsp']; exact hI1.lo8, by rw [hrsp']; exact hI1.hi,
            hI1.nlF, fun y hy => ?_, hmem⟩
          rw [hrsp', rdW_of_pres hG hpres (by omega) (by omega) (by omega),
            rdW_of_pres hG hpres1 (by omega) (by omega) (by omega), hloc]
          exact hI1.frame y hy
        refine sim_storeRes hG ctx.nl F Q xs 0 _ σ' r d' hcR.tail.tail.tail.tail hxs (by omega) (by omega)
          hId (fun j hj => by rw [Nat.zero_add]; exact hrax j (by omega)) ?_
        intro s' hI' hregs hst hP'
        refine ev_congr (hK.normal (σ'.setLocs xs r) _ ?_ hI' ?_) ?_
        · rw [step_call_run, hvs]; simp only [hinv]
        · refine ⟨by rw [hregs]; exact hrsp'', by rw [hregs]; exact hrbp.trans hE1.rbp,
            by rw [hregs]; exact hr15.trans hE1.r15, ?_, ?_⟩
          · show s'.regs.r14.toNat ≤ d.regs.r14.toNat
            rw [hregs]
            have := congrArg UInt64.toNat hE1.r14
            have h1 : ({ toBitVec := s1.regs.r14.toBitVec - 1 } : UInt64).toNat = s1.regs.r14.toNat - 1 :=
              u64_sub_one_toNat hpos
            rw [h1] at hr14; omega
          · refine (Pres.of_only hE1.mem (by have := hI.lo; omega) (by simp only [top]; omega)).trans ?_
            refine (hpres1.mono (by simp only [top]; omega)).trans ?_
            refine (hpres.mono (by simp only [top]; omega)).trans ?_
            exact hP'.mono (by simp only [top]; rw [hrsp']; omega)
        · simp only [List.length_append, List.length_cons, List.length_nil, storeRes_length]; omega
      all_goals
        intro d'
        have hlo1 := hI1.lo8
        have hhi1 := hI1.hi
        have h4 : ({ toBitVec := A (s1.regs.rsp.toNat - 8) } : UInt64).toNat = s1.regs.rsp.toNat - 8 := by
          addr_omega
        have hchain : Pres G (top d F) d.dmem
            (wrW s1.dmem (A (s1.regs.rsp.toNat - 8)) (at_ (k + (compileArgs ctx 0 args).length + 4)).toBitVec) :=
          (Pres.of_only hE1.mem (by have := hI.lo; omega) (by simp only [top]; omega)).trans
            (Pres.of_only (Only.wrW (by omega)) (by omega) (by simp only [top]; omega))
      · intro ⟨y, hy, hne⟩ hG'
        rw [bv_sub8 _ hsp8, h4] at hG'
        refine hK.err d' ⟨y, by rw [step_call_run, hvs]; simp only [hy], hne⟩
          ⟨hG'.rbp.trans hE1.rbp, hchain.trans (hG'.mem.mono (by simp only [top]; omega))⟩
      · intro hG'
        rw [bv_sub8 _ hsp8, h4] at hG'
        refine hK.exh d' ⟨hG'.rbp.trans hE1.rbp, hchain.trans (hG'.mem.mono (by simp only [top]; omega))⟩
  · intro s1 herr1 hE1
    obtain ⟨y, hy⟩ := herr1
    exact hK.err s1 ⟨y, by simp [step_call_run, hy] <;> rfl, by rw [evalArgsP_error hy]; simp⟩
      (hE1.spost hI.lo).gpost

end

end L.Compiler
