module

public import ConAgua.Compiler.SimStmt

@[expose] public section

/-!
# Calls

`sim_args` evaluates the arguments into temporaries. `FunSim p G n` is the simulation of a call
of a function of `p` under `exec p n`: entered at its label with the return address at `rsp`
and the arguments at `rsi`, the code returns to the return address with L's result in `rax`, or
leaves through `ca_error`/`ca_exhausted`.
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
      d'.regs.r15 = d.regs.r15 → d'.regs.r14.toNat ≤ d.regs.r14.toNat → d'.regs.rax = r →
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

section
variable [Host] {G : Layout} (hG : G.Ok) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) < maxOff) (p : Prog)
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

theorem sim_call (n : Nat) (hFun : FunSim p G n)
    (hProg : ∀ f fd, p.lookup f = some fd → ∃ kf, Code (compileFn G.tab f fd) kf)
    (x : Var) (f : FnName) (args : List Expr) :
    SimS p G (stepRun p (exec p n)) (· ≤ n) (.call x f args) := by
  intro ctx F path k hT hF hc hwf htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨hx, hargs⟩, hfd⟩ := hwf
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
        refine ev_movMR hcR.tail.tail.tail.tail.head ⟨by lomega, by lomega⟩ ?_ ?_
        · rw [slot_addr _ x _ (by omega)]; exact hId.mapped (by lomega)
        rw [slot_addr _ x _ (by omega)]
        have hv' : d'.regs.get64 .rax = r.toBitVec := by simp [hrax]
        rw [hv']
        refine ev_congr (hK.normal (σ'.setLoc x r) _ ?_ (hId.setLoc hG hx r) ?_) ?_
        · rw [step_call_run, hvs]; simp only [hinv]
        · refine ⟨hrsp'', hrbp.trans hE1.rbp, hr15.trans hE1.r15, ?_, ?_⟩
          · show d'.regs.r14.toNat ≤ d.regs.r14.toNat
            have := congrArg UInt64.toNat hE1.r14
            have h1 : ({ toBitVec := s1.regs.r14.toBitVec - 1 } : UInt64).toNat = s1.regs.r14.toNat - 1 :=
              u64_sub_one_toNat hpos
            rw [h1] at hr14; omega
          · refine (Pres.of_only hE1.mem (by have := hI.lo; omega) (by simp only [top]; omega)).trans ?_
            refine (hpres1.mono (by simp only [top]; omega)).trans ?_
            refine (hpres.mono (by simp only [top]; omega)).trans ?_
            exact Pres.of_only (Only.wrW (by lomega)) (by rw [hrsp']; lomega) (by simp only [top]; lomega)
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
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
