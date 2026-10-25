module

public import ConAgua.Compiler.RunEq

@[expose] public section

/-!
# Statements

`SimS p G sk run P s`: from any state related to `σ` (with the fuel counter satisfying `P`), the
code of `s` reaches the exit that `run s σ` names: the end of the code (normal), the `break`
target, the return label (with the results in the result registers), `ca_error` (an error other than running out
of fuel), or `ca_exhausted` (always allowed). The exits are continuations (`Conts`).
-/

namespace L.Compiler

open L

attribute [local simp] Reg64s.set64_rax Reg64s.set64_rcx Reg64s.set64_rdx Reg64s.set64_rsi
  Reg64s.set64_rsp Reg64s.set64_r14

/-- `d'` has every byte of `d`, and the same bytes outside the stack below `top`, outside the
arrays, the result area and the global variables. -/
structure Pres (G : Layout) (top : Nat) (d d' : DataMem) : Prop where
  grows : ∀ y, (d.get? y).isSome → (d'.get? y).isSome
  same : ∀ x < 2 ^ 64, ¬ (G.lo ≤ x ∧ x < top) → ¬ G.InArr x → ¬ G.InRes x → ¬ G.InGlob x →
    d'.get? (A x) = d.get? (A x)

namespace Pres
variable {G : Layout}

theorem refl (top : Nat) (d : DataMem) : Pres G top d d := ⟨fun _ h => h, fun _ _ _ _ _ _ => rfl⟩

theorem trans {top : Nat} {d d' d'' : DataMem} (h : Pres G top d d') (h' : Pres G top d' d'') :
    Pres G top d d'' :=
  ⟨fun y hy => h'.grows y (h.grows y hy), fun x hx h1 h2 h3 h4 => by
    rw [h'.same x hx h1 h2 h3 h4, h.same x hx h1 h2 h3 h4]⟩

theorem mono {top top' : Nat} {d d' : DataMem} (h : Pres G top d d') (ht : top ≤ top') :
    Pres G top' d d' :=
  ⟨h.grows, fun x hx h1 h2 h3 h4 => h.same x hx (fun ⟨a, b⟩ => h1 ⟨a, by omega⟩) h2 h3 h4⟩

theorem of_only {a b top : Nat} {d d' : DataMem} (h : Only a b d d') (ha : G.lo ≤ a) (hb : b ≤ top) :
    Pres G top d d' :=
  ⟨h.grows, fun x hx h1 _ _ _ => h.same x hx (by omega)⟩

/-- A change inside the result area. -/
theorem of_res {a b top : Nat} {d d' : DataMem} (h : Only a b d d') (hab : ∀ x, a ≤ x → x < b → G.InRes x) :
    Pres G top d d' :=
  ⟨h.grows, fun x hx _ _ h3 _ => h.same x hx (Classical.byContradiction fun hc => h3 (hab x (by omega) (by omega)))⟩

/-- A change inside the global variables. -/
theorem of_glob {a b top : Nat} {d d' : DataMem} (h : Only a b d d') (hab : ∀ x, a ≤ x → x < b → G.InGlob x) :
    Pres G top d d' :=
  ⟨h.grows, fun x hx _ _ _ h4 => h.same x hx (Classical.byContradiction fun hc => h4 (hab x (by omega) (by omega)))⟩

end Pres

theorem u64_sub_one_toNat {x : UInt64} (h : 0 < x.toNat) : (x - 1).toNat = x.toNat - 1 := by
  rw [UInt64.toNat_sub_of_le]
  · rfl
  · rw [UInt64.le_iff_toNat_le]; simp; omega

/-- The current function's frame ends here. -/
abbrev top (d : MachineData) (F : Nat) : Nat := d.regs.rsp.toNat + 8 * F

/-- What a statement keeps: the frame, `rbp`, `r15`; the fuel counter only goes down. -/
structure SPost (G : Layout) (F : Nat) (d d' : MachineData) : Prop where
  rsp : d'.regs.rsp = d.regs.rsp
  rbp : d'.regs.rbp = d.regs.rbp
  r15 : d'.regs.r15 = d.regs.r15
  r14 : d'.regs.r14.toNat ≤ d.regs.r14.toNat
  mem : Pres G (top d F) d.dmem d'.dmem

/-- What a statement keeps when it leaves through `ca_error` or `ca_exhausted`. -/
structure GPost (G : Layout) (top : Nat) (d d' : MachineData) : Prop where
  rbp : d'.regs.rbp = d.regs.rbp
  mem : Pres G top d.dmem d'.dmem

namespace SPost
variable {G : Layout} {F : Nat}

theorem refl (d : MachineData) : SPost G F d d := ⟨rfl, rfl, rfl, Nat.le_refl _, Pres.refl _ _⟩

theorem trans {d d' d'' : MachineData} (h : SPost G F d d') (h' : SPost G F d' d'') : SPost G F d d'' :=
  ⟨h'.rsp.trans h.rsp, h'.rbp.trans h.rbp, h'.r15.trans h.r15, Nat.le_trans h'.r14 h.r14,
    h.mem.trans (by have := h'.mem; simp only [top, h.rsp] at this; exact this)⟩

theorem gpost {d d' : MachineData} (h : SPost G F d d') : GPost G (top d F) d d' := ⟨h.rbp, h.mem⟩

theorem trans_g {d d' d'' : MachineData} (h : SPost G F d d') (h' : GPost G (top d' F) d' d'') :
    GPost G (top d F) d d'' :=
  ⟨h'.rbp.trans h.rbp, h.mem.trans (by have := h'.mem; simp only [top, h.rsp] at this; exact this)⟩

end SPost

theorem EPost.spost {G : Layout} {nl F t : Nat} {d d' : MachineData} (h : EPost nl F t d d')
    (hlo : G.lo ≤ d.regs.rsp.toNat) : SPost G F d d' :=
  ⟨h.rsp, h.rbp, h.r15, by rw [h.r14]; exact Nat.le_refl _, Pres.of_only h.mem (by omega) (Nat.le_refl _)⟩

/-- What a function's code keeps when it returns to its caller from a frame of `F` words at `rsp`
(a tail call: the frame popped, the return address above it taken). -/
structure TPost (G : Layout) (F : Nat) (d d' : MachineData) : Prop where
  rsp : d'.regs.rsp.toNat = top d F + 8
  rbp : d'.regs.rbp = d.regs.rbp
  r15 : d'.regs.r15 = d.regs.r15
  r14 : d'.regs.r14.toNat ≤ d.regs.r14.toNat
  mem : Pres G (top d F) d.dmem d'.dmem

theorem SPost.trans_t {G : Layout} {F : Nat} {d d' d'' : MachineData} (h : SPost G F d d')
    (h' : TPost G F d' d'') : TPost G F d d'' :=
  ⟨by rw [h'.rsp]; simp only [top, h.rsp], h'.rbp.trans h.rbp, h'.r15.trans h.r15,
    Nat.le_trans h'.r14 h.r14, h.mem.trans (by have := h'.mem; simp only [top, h.rsp] at this; exact this)⟩

/-- The exits of a statement whose run is `R`, for code that ends at `kend`. -/
structure Conts [Host] (G : Layout) (ctx : Ctx) (F : Nat) (d : MachineData) (R : Except Err (Sig × St))
    (kend : Nat) (Q : MachineState → Prop) : Prop where
  normal : ∀ σ' d', R = .ok (.normal, σ') → Inv G ctx F σ' d' → SPost G F d d' → Ev Q d' (at_ kend)
  brk : ∀ σ' d', R = .ok (.brk, σ') → Inv G ctx F σ' d' → SPost G F d d' → Ev Q d' (label ctx.brk)
  ret : ∀ vs σ' d', R = .ok (.ret vs, σ') → MemRel G σ'.mem d'.dmem → SPost G F d d' →
    ResOut G ctx.nr vs d' → Ev Q d' (label ctx.retL)
  err : ∀ d', (∃ e, R = .error e ∧ e ≠ .outOfFuel) → GPost G (top d F) d d' → Ev Q d' (label errorL)
  exh : ∀ d', GPost G (top d F) d d' → Ev Q d' (label exhaustedL)
  /-- A tail call returns to the caller of the current function, whose return address `ra` is
  the word above the frame. -/
  tail : ∀ Fw, ctx.tailF = some Fw → Fw = F ∧ ∀ vs σ' d' (ra : Word), R = .ok (.ret vs, σ') →
    MemRel G σ'.mem d'.dmem → TPost G F d d' → ResOut G ctx.nr vs d' →
    rdW d'.dmem (A (top d F)) = some ra → Ev Q d' (Int64.ofBitVec ra.toBitVec)

/-- The tail exit of a statement inside another (after `SPost`), from the outer one's. -/
theorem Conts.tail_fwd [Host] {G : Layout} {ctx ctx' : Ctx} {F : Nat} {d d1 : MachineData}
    {R R1 : Except Err (Sig × St)} {kend : Nat} {Q : MachineState → Prop} (hK : Conts G ctx F d R kend Q)
    (ht : ctx'.tailF = ctx.tailF) (hn : ctx'.nr = ctx.nr) (hS : SPost G F d d1)
    (hR : ∀ vs σ', R1 = .ok (.ret vs, σ') → R = .ok (.ret vs, σ')) :
    ∀ Fw, ctx'.tailF = some Fw → Fw = F ∧ ∀ vs σ' d' (ra : Word), R1 = .ok (.ret vs, σ') →
      MemRel G σ'.mem d'.dmem → TPost G F d1 d' → ResOut G ctx'.nr vs d' →
      rdW d'.dmem (A (top d1 F)) = some ra → Ev Q d' (Int64.ofBitVec ra.toBitVec) := by
  intro Fw hFw
  rw [ht] at hFw
  refine ⟨(hK.tail Fw hFw).1, fun vs σ' d' ra hr hm hT hO hra => ?_⟩
  rw [hn] at hO
  have htop : top d1 F = top d F := by simp only [top, hS.rsp]
  rw [htop] at hra
  exact (hK.tail Fw hFw).2 vs σ' d' ra (hR vs σ' hr) hm (hS.trans_t hT) hO hra

/-- The result counts of `ctx` fit statement `s`: every `return` of `s` sets at most `ctx.nr`
results, which fit the result registers and area, and `ctx.nrt` gives every callee's count; the
frames of the callees without a stack check (`skOf sk`) fit `ctx.need`. -/
structure NrOk (p : Prog) (G : Layout) (sk : NTree) (ctx : Ctx) (s : Stmt) : Prop where
  ret : Stmt.nret s ≤ ctx.nr
  le : ctx.nr ≤ G.tab.nres
  callee : ∀ g fd, p.lookup g = some fd → nrOf ctx.nrt G.tab g = Stmt.nret fd.body
  /-- A leaf calls nothing. -/
  leaf : ctx.leaf = true → Stmt.calls s = false
  need : Stmt.need sk s ≤ ctx.need

theorem NrOk.sub {p : Prog} {G : Layout} {sk : NTree} {ctx : Ctx} {s : Stmt} (h : NrOk p G sk ctx s) {t : Stmt}
    (ht : Stmt.nret t ≤ Stmt.nret s) (hc : Stmt.calls t = true → Stmt.calls s = true)
    (hn : Stmt.need sk t ≤ Stmt.need sk s) : NrOk p G sk ctx t :=
  ⟨Nat.le_trans ht h.ret, h.le, h.callee, (fun hl => by
    cases h' : Stmt.calls t
    · rfl
    · have := h.leaf hl; rw [hc h'] at this; cases this), Nat.le_trans hn h.need⟩

/-- The simulation of a statement `s`, for a run function `run` and a condition `P` on the fuel
counter. -/
def SimS [Host] (p : Prog) (G : Layout) (sk : NTree) (run : Stmt → St → Except Err (Sig × St)) (P : Nat → Prop)
    (s : Stmt) : Prop :=
  ∀ (ctx : Ctx) (F : Nat) (path : Path) (k : Nat), ctx.tab = G.tab → 8 * F + 8 < maxOff →
    Code (compileS ctx path s) k → Stmt.wf p ctx.nl G.tab s = true → NrOk p G sk ctx s →
    TmpFit ctx.nl F 0 (tempsS ctx.alloc ctx.nr s) →
    ∀ (σ : St) (d : MachineData) (Q : MachineState → Prop), Inv G ctx F σ d → P d.regs.r14.toNat →
    Conts G ctx F d (run s σ) (k + (compileS ctx path s).length) Q → Ev Q d (at_ k)

/-- The simulation of `s; t` where it is compiled as a tail call (`tailCode`). -/
def SimSTail [Host] (p : Prog) (G : Layout) (sk : NTree) (run : Stmt → St → Except Err (Sig × St)) (P : Nat → Prop)
    (s t : Stmt) : Prop :=
  ∀ (ctx : Ctx) (F : Nat) (k : Nat) (code : Program), ctx.tab = G.tab → 8 * F + 8 < maxOff →
    tailCode ctx s t = some code → Code code k → Stmt.wf p ctx.nl G.tab (.seq s t) = true →
    NrOk p G sk ctx (.seq s t) → TmpFit ctx.nl F 0 (tempsS ctx.alloc ctx.nr (.seq s t)) →
    ∀ (σ : St) (d : MachineData) (Q : MachineState → Prop), Inv G ctx F σ d → P d.regs.r14.toNat →
    Conts G ctx F d (run (.seq s t) σ) (k + code.length) Q → Ev Q d (at_ k)

/-- `exec p n` on statement `s` from state `σ`. -/
def execRun (p : Prog) (n : Nat) (s : Stmt) (σ : St) : Except Err (Sig × St) := (exec p n s).run σ

/-- Statements under `step p (exec p n)`, with at most `n` units of machine fuel. -/
abbrev StepSim [Host] (p : Prog) (G : Layout) (sk : NTree) (n : Nat) : Prop :=
  ∀ s, SimS p G sk (stepRun p (exec p n)) (· ≤ n) s

/-- Statements under `exec p n`, with fewer than `n` units of machine fuel. -/
abbrev ExecSim [Host] (p : Prog) (G : Layout) (sk : NTree) (n : Nat) : Prop :=
  ∀ s, SimS p G sk (execRun p n) (· < n) s

theorem execSim_zero [Host] (p : Prog) (G : Layout) (sk : NTree) : ExecSim p G sk 0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP _ => absurd hP (Nat.not_lt_zero _)

theorem execSim_succ [Host] {p : Prog} {G : Layout} {sk : NTree} {n : Nat} (h : StepSim p G sk n) : ExecSim p G sk (n + 1) :=
  fun s ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK =>
    h s ctx F path k hT hF hc hwf hN htmp σ d Q hI (Nat.lt_succ_iff.mp hP) hK


theorem SPost.store {G : Layout} {F : Nat} {d : MachineData} {a : Nat} {v : BitVec 64}
    (hlo : G.lo ≤ a) (ha : a + 8 ≤ top d F) (hov : top d F ≤ 2 ^ 64) :
    SPost G F d { d with dmem := wrW d.dmem (A a) v } :=
  ⟨rfl, rfl, rfl, Nat.le_refl _, Pres.of_only (Only.wrW (by omega)) hlo ha⟩

theorem SPost.regs {G : Layout} {F : Nat} {d : MachineData} {R : Reg64s} {st : StatusFlags}
    (h1 : R.rsp = d.regs.rsp) (h2 : R.rbp = d.regs.rbp) (h3 : R.r15 = d.regs.r15)
    (h4 : R.r14.toNat ≤ d.regs.r14.toNat) :
    SPost G F d { d with regs := R, status := st } := ⟨h1, h2, h3, h4, Pres.refl _ _⟩

section
variable {G : Layout} (hG : G.Ok)
include hG

theorem Inv.setLoc {ctx : Ctx} {F : Nat} {σ : St} {d : MachineData} (hI : Inv G ctx F σ d) {x : Nat}
    (hx : x < ctx.nl) (hn : ctx.alloc.lookup x = none) (v : Word) (ht : ctx.treg ≠ some x) :
    Inv G ctx F (σ.setLoc x v) { d with dmem := wrW d.dmem (A (d.regs.rsp.toNat + 8 * x)) v.toBitVec } where
  r15 := hI.r15
  lo := hI.lo
  lo8 := hI.lo8
  hi := hI.hi
  slot := hI.slot
  al := hI.al
  reg := fun y hy r hr => by
    have hxy : y ≠ x := fun h => by subst h; rw [hn] at hr; cases hr
    simp only [St.setLoc, hxy, ite_false]; exact hI.reg y hy r hr
  frame := fun y hy hyn => by
    have := hI.hi; have := hG.hi_le; have := hI.slot x hx hn; have := hI.slot y hy hyn
    by_cases hxy : y = x
    · subst hxy; simp [St.setLoc, rdW_wrW_same]
    · simp only [St.setLoc, hxy, ite_false]
      rw [rdW_wrW_A (by omega) (by omega) (by omega)]
      exact hI.frame y hy hyn
  mem := hI.mem.only hG (Only.wrW (by have := hI.hi; have := hG.hi_le; have := hI.slot x hx hn; omega))
    fun z h1 h2 => ⟨by have := hI.lo; omega, by have := hI.hi; have := hI.slot x hx hn; omega⟩
  tr := fun y hy => by
    have hyx : y ≠ x := fun h => ht (h ▸ hy)
    simp only [St.setLoc, hyx, ite_false]; exact hI.tr y hy

/-- A write of the tier local in its frame slot, with its tier set in `rsi` first (`tregSet`). -/
theorem Inv.setLocT {ctx : Ctx} {F : Nat} {σ : St} {d : MachineData} (hI : Inv G ctx F σ d) {x : Nat}
    (hx : x < ctx.nl) (hn : ctx.alloc.lookup x = none) (v : Word) (ht : ctx.treg = some x) (st : StatusFlags) :
    Inv G ctx F (σ.setLoc x v)
      { regs := d.regs.set64 .rsi (UInt64.toBitVec (v &&& 1)), zmms := d.zmms, status := st,
        dmem := wrW d.dmem (A (d.regs.rsp.toNat + 8 * x)) v.toBitVec } where
  r15 := hI.r15
  lo := hI.lo
  lo8 := hI.lo8
  hi := hI.hi
  slot := hI.slot
  al := hI.al
  reg := fun y hy r hr => by
    have hxy : y ≠ x := fun h => by subst h; rw [hn] at hr; cases hr
    have hrb : r ≠ .rsi := fun h => hI.al.trsi (by simp [ht]) y (h ▸ hr)
    simp only [rget_set, hrb, ite_false, St.setLoc, hxy]; exact hI.reg y hy r hr
  frame := fun y hy hyn => by
    have := hI.hi; have := hG.hi_le; have := hI.slot x hx hn; have := hI.slot y hy hyn
    show rdW (wrW d.dmem (A (d.regs.rsp.toNat + 8 * x)) v.toBitVec) (A (d.regs.rsp.toNat + 8 * y)) = _
    by_cases hxy : y = x
    · subst hxy; simp [St.setLoc, rdW_wrW_same]
    · simp only [St.setLoc, hxy, ite_false]
      rw [rdW_wrW_A (by omega) (by omega) (by omega)]
      exact hI.frame y hy hyn
  mem := hI.mem.only hG (Only.wrW (by have := hI.hi; have := hG.hi_le; have := hI.slot x hx hn; omega))
    fun z h1 h2 => ⟨by have := hI.lo; omega, by have := hI.hi; have := hI.slot x hx hn; omega⟩
  tr := fun y hy => by
    rw [ht] at hy; cases hy
    simp [St.setLoc, Reg64s.set64]

omit hG in
theorem set64_alloc_fields {R : Reg64s} {r : Reg64} (hr : r ∈ allocRegs) (v : BitVec 64) :
    (R.set64 r v).rsp = R.rsp ∧ (R.set64 r v).rbp = R.rbp ∧ (R.set64 r v).r14 = R.r14 ∧
    (R.set64 r v).r15 = R.r15 := by
  rw [mem_allocRegs] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩

omit hG in
/-- A write of a local kept in a register. -/
theorem Inv.setLocR {ctx : Ctx} {F : Nat} {σ : St} {d : MachineData} (hI : Inv G ctx F σ d) {x : Nat}
    (hx : x < ctx.nl) {r : Reg64} (hr : ctx.alloc.lookup x = some r) (v : Word) (st : StatusFlags)
    (ht : ctx.treg ≠ some x) :
    Inv G ctx F (σ.setLoc x v) { d with regs := d.regs.set64 r v.toBitVec, status := st } := by
  obtain ⟨h1, h2, h3, h4⟩ := set64_alloc_fields (R := d.regs) (hI.al.reg x r hr) v.toBitVec
  exact {
    r15 := by simp only [h4]; exact hI.r15
    lo := by simp only [h1]; exact hI.lo
    lo8 := by simp only [h1]; exact hI.lo8
    hi := by simp only [h1]; exact hI.hi
    slot := hI.slot
    al := hI.al
    reg := fun y hy r' hr' => by
      simp only [rget_set]
      by_cases hxy : y = x
      · subst hxy; rw [hr] at hr'; cases hr'; simp [St.setLoc]
      · have hne : r' ≠ r := fun h => hxy (hI.al.inj y x r (h ▸ hr') hr)
        simp only [hne, ite_false, St.setLoc, hxy]; exact hI.reg y hy r' hr'
    frame := fun y hy hyn => by
      have hxy : y ≠ x := fun h => by subst h; rw [hyn] at hr; cases hr
      simp only [h1, St.setLoc, hxy, ite_false]; exact hI.frame y hy hyn
    mem := hI.mem
    tr := fun y hy => by
      have hyx : y ≠ x := fun h => ht (h ▸ hy)
      have hrb : r ≠ .rsi := fun h => hI.al.trsi (by simp [hy]) x (h ▸ hr)
      rw [show (d.regs.set64 r v.toBitVec).rsi = d.regs.rsi from
        rsi_of_get64 (by rw [rget_set, if_neg (Ne.symm hrb)])]
      simp only [St.setLoc, hyx, ite_false]; exact hI.tr y hy }



end

section
variable [Host] {G : Layout} (hG : G.Ok) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
  (p : Prog) (K : Stmt → M Sig) (P : Nat → Prop) {sk : NTree}
include hG hTab

omit hG hTab in
theorem sim_skip : SimS p G sk (stepRun p K) P .skip := by
  intro ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK
  exact ev_congr (hK.normal σ d (step_skip_run p K σ) hI (SPost.refl d)) (by simp [compileS])

omit hG hTab in
theorem sim_brk : SimS p G sk (stepRun p K) P .brk := by
  intro ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK
  simp only [compileS] at hc
  exact ev_jmp hc.head (hK.brk σ d (step_brk_run p K σ) hI (SPost.refl d))

omit hG hTab in
theorem sim_abort : SimS p G sk (stepRun p K) P .abort := by
  intro ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK
  simp only [compileS] at hc
  exact ev_jmp hc.head (hK.err d ⟨.abort, step_abort_run p K σ, by simp⟩ (SPost.refl d).gpost)

/-- `x := e` into a frame slot, through `rax`. -/
theorem sim_set_mem (x : Var) (e : Expr) (ctx : Ctx) (F k : Nat) (hT : ctx.tab = G.tab)
    (hF : 8 * F + 8 < maxOff) (hc : Code (compileE ctx e 0 ++ [movMR (mb .rsp (8 * x)) .rax]) k)
    (hx : x < ctx.nl) (hwf : Expr.wf ctx.nl G.tab e = true) (hl : ctx.alloc.lookup x = none) (htmp : TmpFit ctx.nl F 0 (tempsE e))
    (ht : ctx.treg ≠ some x)
    (σ : St) (d : MachineData) (Q : MachineState → Prop) (hI : Inv G ctx F σ d)
    (hK : Conts G ctx F d (stepRun p K (.set x e) σ) (k + (compileE ctx e 0 ++ [movMR (mb .rsp (8 * x)) .rax]).length) Q)
    (hset : ∀ v, evalP σ e = .ok v → stepRun p K (.set x e) σ = .ok (.normal, σ.setLoc x v))
    (herrK : ∀ s1, (∃ x, evalP σ e = .error x) → EPost ctx.nl F 0 d s1 → Ev Q s1 (label errorL)) :
    Ev Q d (at_ k) := by
  have hF' := hF; simp only [maxOff] at hF'
  refine sim_expr hG ctx hT hTab F hF e 0 k hc.left hwf htmp σ d Q hI ?_ herrK
  intro v s1 hv hrax hE1
  have hI1 := hI.ofE hG hE1
  have := hI.slot x hx hl
  refine ev_movMR hc.right.head ⟨by lomega, by lomega⟩ ?_ ?_
  · rw [slot_addr _ x _ (by omega)]; exact hI1.mapped (by lomega)
  rw [slot_addr _ x _ (by omega)]
  have hv' : s1.regs.get64 .rax = v.toBitVec := by simp [hrax]
  rw [hv']
  refine ev_congr (hK.normal (σ.setLoc x v) _ (hset v hv) (hI1.setLoc hG hx hl v ht) ?_) ?_
  · refine (hE1.spost hI.lo).trans (SPost.store ?_ ?_ ?_)
    · have := hI1.lo; omega
    · have := hI.hi; simp only [top, hE1.rsp]; lomega
    · have := hI.hi; have := hG.hi_le; simp only [top, hE1.rsp]; omega
  · simp; omega

theorem sim_set (x : Var) (e : Expr) : SimS p G sk (stepRun p K) P (.set x e) := by
  intro ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
  simp only [compileS] at hc hK
  simp only [tempsS] at htmp
  have hF' := hF; simp only [maxOff] at hF'
  have hx := hwf.1
  -- the normal exit after `x := v`, with the code ending at `kend`
  have hset : ∀ v, evalP σ e = .ok v → stepRun p K (.set x e) σ = .ok (.normal, σ.setLoc x v) := by
    intro v hv; simp [step_set_run, hv]; rfl
  by_cases htx : ctx.treg = some x
  · -- the tier local: its tier into `rsi`, then the store
    have hb : (ctx.treg == some x) = true := by simp [htx]
    simp only [hb, ite_true, List.append_assoc] at hc hK
    have herrK : ∀ s1, (∃ x, evalP σ e = .error x) → EPost ctx.nl F 0 d s1 → Ev Q s1 (label errorL) :=
      fun s1 ⟨y, hy⟩ hE1 => hK.err s1 ⟨y, by simp [step_set_run, hy]; rfl, by rw [evalP_error hy]; simp⟩ (hE1.spost hI.lo).gpost
    refine sim_expr hG ctx hT hTab F hF e 0 k hc.left hwf.2 htmp σ d Q hI ?_ herrK
    intro v s1 hv hrax hE1
    have hI1 := hI.ofE hG hE1
    have hcR := hc.right
    simp only [tregSet, List.cons_append, List.nil_append] at hcR
    refine ev_movRR hcR.head ?_
    refine ev_aluRI (op := .and) (w := 1) rfl hcR.tail.head fun st => ?_
    have hv' : s1.regs.get64 .rax = v.toBitVec := by simp [hrax]
    simp only [rget_set, ↓reduceIte, set64_set64, hv', UInt64.ofBitVec_toBitVec, BinOp.eval]
    have hS : SPost G F d { s1 with regs := s1.regs.set64 .rsi (v &&& 1).toBitVec, status := st } :=
      (hE1.spost hI.lo).trans (SPost.regs rfl rfl rfl (Nat.le_refl _))
    cases hl : ctx.alloc.lookup x with
    | some r => exact absurd (hI.al.talloc x htx) (by simp [hl])
    | none =>
      simp only [storeRax, hl] at hcR hK
      have := hI.slot x hx hl
      have hE1' := hE1
      refine ev_movMR hcR.tail.tail.head ⟨by lomega, by lomega⟩ ?_ ?_
      · rw [slot_addr _ x _ (by omega)]; exact hI1.mapped (by lomega)
      rw [slot_addr _ x _ (by omega), show (s1.regs.set64 .rsi (v &&& 1).toBitVec).get64 .rax = v.toBitVec by
        rw [rget_set, if_neg (by decide)]; exact hv']
      refine ev_congr (hK.normal (σ.setLoc x v) _ (hset v hv) (hI1.setLocT hG hx hl v htx st) ?_) ?_
      · refine hS.trans (SPost.store ?_ ?_ ?_)
        · have := hI1.lo; simp only [Reg64s.set64]; omega
        · have := hI.hi; simp only [top, Reg64s.set64, hE1.rsp]; lomega
        · have := hI.hi; have := hG.hi_le; simp only [top, Reg64s.set64, hE1.rsp]; omega
      · simp [tregSet]; omega
  have hb : (ctx.treg == some x) = false := by simp [htx]
  simp only [hb, Bool.false_eq_true, ite_false] at hc hK
  cases hsp : setInPlace ctx x e
  case some dir =>
    simp only [hsp] at hc hK
    obtain ⟨op, w, rfl, hd⟩ : ∃ op w, e = .bin op (.var x) (.const w) ∧
        aluDirect op (match ctx.alloc.lookup x with
          | some r => .reg (rr r)
          | none => .mem (mb .rsp (8 * x))) (.imm (.int64 w.toInt64)) = some dir := by
      unfold setInPlace at hsp
      split at hsp
      · rename_i op y w
        split at hsp
        · rename_i hy
          simp only [Bool.and_eq_true, beq_iff_eq] at hy
          exact ⟨op, w, by rw [hy.1], hsp⟩
        · cases hsp
      · cases hsp
    have hev : evalP σ (.bin op (.var x) (.const w)) = .ok (op.eval (σ.loc x) w) := rfl
    cases hl : ctx.alloc.lookup x with
    | some r =>
      simp only [hl] at hd
      obtain ⟨h1, h2, h3, h4⟩ := set64_alloc_fields (R := d.regs) (hI.al.reg x r hl)
        (op.eval (σ.loc x) w).toBitVec
      refine ev_aluRI hd hc.head fun st => ?_
      rw [hI.reg x hx r hl, UInt64.ofBitVec_toBitVec]
      refine ev_congr (hK.normal (σ.setLoc x (op.eval (σ.loc x) w)) _ (hset _ hev)
        (hI.setLocR hx hl _ st htx) (SPost.regs h1 h2 h4 (by rw [h3]; exact Nat.le_refl _))) ?_
      simp
    | none =>
      simp only [hl] at hd
      have := hI.slot x hx hl
      refine ev_aluMI hd hc.head ⟨by lomega, by lomega⟩ (v := σ.loc x) ?_ fun st => ?_
      · rw [Reg64s.get64_rsp, UInt64.toNat_toBitVec, toNat_eight_mul]; exact hI.frame x hx hl
      rw [Reg64s.get64_rsp, UInt64.toNat_toBitVec, toNat_eight_mul]
      have hI0 : Inv G ctx F σ { d with status := st } := hI.of_regs rfl rfl rfl (fun _ _ => rfl) (fun _ => rfl)
      refine ev_congr (hK.normal (σ.setLoc x (op.eval (σ.loc x) w)) _ (hset _ hev) (hI0.setLoc hG hx hl _ htx) ?_) ?_
      · refine ⟨rfl, rfl, rfl, Nat.le_refl _, (SPost.store (d := d) ?_ ?_ ?_).mem⟩
        · have := hI.lo; omega
        · have := hI.hi; simp only [top]; lomega
        · have := hI.hi; have := hG.hi_le; simp only [top]; omega
      · simp
  simp only [hsp] at hc hK
  have herrK : ∀ s1, (∃ x, evalP σ e = .error x) → EPost ctx.nl F 0 d s1 → Ev Q s1 (label errorL) :=
    fun s1 ⟨y, hy⟩ hE1 => hK.err s1 ⟨y, by simp [step_set_run, hy]; rfl, by rw [evalP_error hy]; simp⟩ (hE1.spost hI.lo).gpost
  cases hl : ctx.alloc.lookup x with
  | some r =>
    simp only [hl] at hc hK
    have hra := (hI.al.ne hl)
    cases hld : loadInto ctx r e
    case some code =>
      simp only [hld] at hc hK
      obtain ⟨v, hv, hlen, hsim⟩ := sim_loadInto hT hTab hF hI hwf.2 hld hc
      refine hsim Q ?_
      obtain ⟨h1, h2, h3, h4⟩ := set64_alloc_fields (R := d.regs) (hI.al.reg x r hl) v.toBitVec
      refine ev_congr (hK.normal (σ.setLoc x v) _ (hset v hv) (hI.setLocR hx hl v d.status htx)
        (SPost.regs h1 h2 h4 (by rw [h3]; exact Nat.le_refl _))) ?_
      rw [hlen]
    case none =>
      simp only [hld] at hc hK
      refine sim_expr hG ctx hT hTab F hF e 0 k hc.left hwf.2 htmp σ d Q hI ?_ (herrK)
      intro v s1 hv hrax hE1
      have hI1 := hI.ofE hG hE1
      refine ev_movRR hc.right.head ?_
      have hv' : s1.regs.get64 .rax = v.toBitVec := by simp [hrax]
      rw [hv']
      obtain ⟨h1, h2, h3, h4⟩ := set64_alloc_fields (R := s1.regs) (hI.al.reg x r hl) v.toBitVec
      refine ev_congr (hK.normal (σ.setLoc x v) _ (hset v hv) (hI1.setLocR hx hl v s1.status htx)
        ((hE1.spost hI.lo).trans (SPost.regs h1 h2 h4 (by rw [h3]; exact Nat.le_refl _)))) ?_
      simp; omega
  | none =>
    simp only [hl] at hc hK
    have hsl := hI.slot x hx hl
    cases hso : simpleOp ctx e
    case some o =>
      cases o with
      | imm k' =>
        simp only [hso] at hc hK
        obtain ⟨w, rfl, hk⟩ : ∃ w, e = .const w ∧ k' = .int64 w.toInt64 := by
          cases e <;> simp only [simpleOp] at hso <;> (try split at hso) <;> simp_all
        subst hk
        refine ev_movMW hc.head ⟨by lomega, by lomega⟩ ?_ ?_
        · rw [slot_addr _ x _ (by omega)]; exact hI.mapped (by lomega)
        rw [slot_addr _ x _ (by omega)]
        refine ev_congr (hK.normal (σ.setLoc x w) _ (hset w rfl) (hI.setLoc hG hx hl w htx) ?_) ?_
        · refine SPost.store ?_ ?_ ?_
          · have := hI.lo; omega
          · have := hI.hi; simp only [top]; lomega
          · have := hI.hi; have := hG.hi_le; simp only [top]; omega
        · simp
      | regOrMem m =>
        simp only [hso] at hc hK
        exact sim_set_mem hG hTab p K x e ctx F k hT hF hc hx hwf.2 hl htmp htx σ d Q hI hK hset herrK
    case none =>
      simp only [hso] at hc hK
      exact sim_set_mem hG hTab p K x e ctx F k hT hF hc hx hwf.2 hl htmp htx σ d Q hI hK hset herrK

omit hG hTab in
theorem sim_seq (hPm : ∀ a b, a ≤ b → P b → P a) (s t : Stmt)
    (hs : SimS p G sk (stepRun p K) P s) (ht : SimS p G sk (stepRun p K) P t)
    (htail : SimSTail p G sk (stepRun p K) P s t) :
    SimS p G sk (stepRun p K) P (.seq s t) := by
  intro ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK
  simp only [compileS] at hc hK
  cases htc : tailCode ctx s t
  case some code =>
    simp only [htc] at hc hK
    exact htail ctx F k code hT hF htc hc hwf hN htmp σ d Q hI hP hK
  simp only [htc] at hc hK
  simp only [Stmt.wf, Bool.and_eq_true] at hwf
  simp only [tempsS] at htmp
  refine hs ctx F _ k hT hF hc.left hwf.1 (hN.sub (Nat.le_max_left _ _) (by intro h; simp_all [Stmt.calls]) (by simp only [Stmt.need]; omega)) (htmp.mono (by omega)) σ d Q hI hP ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ1 d1 hr1 hI1 hS1
    refine ht ctx F _ _ hT hF hc.right hwf.2 (hN.sub (Nat.le_max_right _ _) (by intro h; simp_all [Stmt.calls]) (by simp only [Stmt.need]; omega)) (htmp.mono (by omega)) σ1 d1 Q hI1 (hPm _ _ hS1.r14 hP) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro σ2 d2 hr2 hI2 hS2
      refine ev_congr (hK.normal σ2 d2 (by rw [step_seq_run, hr1]; exact hr2) hI2 (hS1.trans hS2)) ?_
      simp only [List.length_append]; omega
    · exact fun σ2 d2 hr2 hI2 hS2 => hK.brk σ2 d2 (by rw [step_seq_run, hr1]; exact hr2) hI2 (hS1.trans hS2)
    · intro v σ2 d2 hr2 hI2 hS2 hv
      exact hK.ret v σ2 d2 (by rw [step_seq_run, hr1]; exact hr2) hI2 (hS1.trans hS2) hv
    · intro d2 ⟨e, hr2, hne⟩ hG2
      exact hK.err d2 ⟨e, by rw [step_seq_run, hr1]; exact hr2, hne⟩ (hS1.trans_g hG2)
    · exact fun d2 hG2 => hK.exh d2 (hS1.trans_g hG2)
    · exact hK.tail_fwd rfl rfl hS1 fun vs σ' hr2 => by rw [step_seq_run, hr1]; exact hr2
  · exact fun σ1 d1 hr1 hI1 hS1 => hK.brk σ1 d1 (by rw [step_seq_run, hr1]) hI1 hS1
  · exact fun v σ1 d1 hr1 hI1 hS1 hv => hK.ret v σ1 d1 (by rw [step_seq_run, hr1]) hI1 hS1 hv
  · intro d1 ⟨e, hr1, hne⟩ hG1
    exact hK.err d1 ⟨e, by rw [step_seq_run, hr1], hne⟩ hG1
  · exact fun d1 hG1 => hK.exh d1 hG1
  · exact hK.tail_fwd rfl rfl (SPost.refl d) fun vs σ' hr1 => by rw [step_seq_run, hr1]

omit hG hTab in
/-- `compileS` of an `if` other than `if c abort`. -/
theorem compileS_ite {ctx : Ctx} {path : Path} {c : Cond} {s t : Stmt} (h : ¬ (s = .abort ∧ t = .skip)) :
    compileS ctx path (.ite c s t) =
      compileC ctx (path.ch 3) c false (ctx.lbl path "E") 0 ++ compileS ctx (path.ch 4) s ++
      [jmpL (ctx.lbl path "X"), .label (ctx.lbl path "E")] ++ compileS ctx (path.ch 5) t ++
      [.label (ctx.lbl path "X")] := by
  exact compileS.eq_7 ctx path c s t fun h1 h2 => h ⟨h1, h2⟩

/-- `if c abort`: one conditional jump to `ca_error`. -/
theorem sim_ifAbort (c : Cond) : SimS p G sk (stepRun p K) P (.ite c .abort .skip) := by
  intro ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true] at hwf
  simp only [compileS] at hc hK
  simp only [tempsS] at htmp
  refine sim_cond hG ctx hT hTab F hF c _ true _ 0 k hc hwf.1.1 (htmp.mono (by omega)) σ d Q hI ?_ ?_ ?_
  · intro d1 hcv hE1
    exact hK.err d1 ⟨.abort, by rw [step_ite_run, hcv]; rfl, by simp⟩ (hE1.spost (G := G) hI.lo).gpost
  · exact fun d1 hcv hE1 => hK.normal σ d1 (by rw [step_ite_run, hcv]; rfl) (hI.ofE hG hE1) (hE1.spost hI.lo)
  · intro d1 ⟨e, he⟩ hE1
    exact hK.err d1 ⟨e, by rw [step_ite_run, he], by rw [evalCP_error he]; simp⟩
      (hE1.spost (G := G) hI.lo).gpost

theorem sim_ite (c : Cond) (s t : Stmt)
    (hs : SimS p G sk (stepRun p K) P s) (ht : SimS p G sk (stepRun p K) P t) :
    SimS p G sk (stepRun p K) P (.ite c s t) := by
  by_cases hab : s = .abort ∧ t = .skip
  · obtain ⟨rfl, rfl⟩ := hab; exact sim_ifAbort hG hTab p K P c
  intro ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true] at hwf
  simp only [compileS_ite hab, List.append_assoc, List.cons_append, List.nil_append] at hc hK
  simp only [tempsS] at htmp
  have hc1 := hc.right
  have hc2 := hc1.right
  have hE := Code.label (i := 1) hc2 rfl
  have hc3 := hc2.tail.tail
  have hX := Code.label (i := 0) hc3.right rfl
  refine sim_cond hG ctx hT hTab F hF c _ false _ 0 k hc.left hwf.1.1 (htmp.mono (by omega)) σ d Q hI ?_ ?_ ?_
  · -- the condition is false: the else branch
    intro d1 hc1v hE1
    have hI1 := hI.ofE hG hE1
    have hS1 := hE1.spost (G := G) hI.lo
    rw [hE]
    refine ev_label hc2.tail.head ?_
    refine ht ctx F _ _ hT hF hc3.left hwf.2 (hN.sub (Nat.le_max_right _ _) (by intro h; simp_all [Stmt.calls]) (by simp only [Stmt.need]; omega)) (htmp.mono (by omega)) σ d1 Q hI1 (by rw [hE1.r14]; exact hP)
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro σ2 d2 hr2 hI2 hS2
      refine ev_label hc3.right.head ?_
      refine ev_congr (hK.normal σ2 d2 (by rw [step_ite_run, hc1v]; exact hr2) hI2 (hS1.trans hS2)) ?_
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · exact fun σ2 d2 hr2 hI2 hS2 => hK.brk σ2 d2 (by rw [step_ite_run, hc1v]; exact hr2) hI2 (hS1.trans hS2)
    · intro v σ2 d2 hr2 hI2 hS2 hv
      exact hK.ret v σ2 d2 (by rw [step_ite_run, hc1v]; exact hr2) hI2 (hS1.trans hS2) hv
    · intro d2 ⟨e, hr2, hne⟩ hG2
      exact hK.err d2 ⟨e, by rw [step_ite_run, hc1v]; exact hr2, hne⟩ (hS1.trans_g hG2)
    · exact fun d2 hG2 => hK.exh d2 (hS1.trans_g hG2)
    · exact hK.tail_fwd rfl rfl hS1 fun vs σ' hr2 => by rw [step_ite_run, hc1v]; exact hr2
  · -- the condition is true: the then branch
    intro d1 hc1v hE1
    have hI1 := hI.ofE hG hE1
    have hS1 := hE1.spost (G := G) hI.lo
    refine hs ctx F _ _ hT hF hc1.left hwf.1.2 (hN.sub (Nat.le_max_left _ _) (by intro h; simp_all [Stmt.calls]) (by simp only [Stmt.need]; omega)) (htmp.mono (by omega)) σ d1 Q hI1 (by rw [hE1.r14]; exact hP)
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro σ2 d2 hr2 hI2 hS2
      refine ev_jmp hc2.head ?_
      rw [hX]
      refine ev_label hc3.right.head ?_
      refine ev_congr (hK.normal σ2 d2 (by rw [step_ite_run, hc1v]; exact hr2) hI2 (hS1.trans hS2)) ?_
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · exact fun σ2 d2 hr2 hI2 hS2 => hK.brk σ2 d2 (by rw [step_ite_run, hc1v]; exact hr2) hI2 (hS1.trans hS2)
    · intro v σ2 d2 hr2 hI2 hS2 hv
      exact hK.ret v σ2 d2 (by rw [step_ite_run, hc1v]; exact hr2) hI2 (hS1.trans hS2) hv
    · intro d2 ⟨e, hr2, hne⟩ hG2
      exact hK.err d2 ⟨e, by rw [step_ite_run, hc1v]; exact hr2, hne⟩ (hS1.trans_g hG2)
    · exact fun d2 hG2 => hK.exh d2 (hS1.trans_g hG2)
    · exact hK.tail_fwd rfl rfl hS1 fun vs σ' hr2 => by rw [step_ite_run, hc1v]; exact hr2
  · intro d1 ⟨e, he⟩ hE1
    exact hK.err d1 ⟨e, by rw [step_ite_run, he], by rw [evalCP_error he]; simp⟩
      (hE1.spost (G := G) hI.lo).gpost

theorem sim_while (n : Nat) (hE : ExecSim p G sk n) (c : Cond) (s : Stmt)
    (hs : SimS p G sk (stepRun p (exec p n)) (· ≤ n) s) :
    SimS p G sk (stepRun p (exec p n)) (· ≤ n) (.while c s) := by
  intro ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK
  have hc0 := hc
  simp only [Stmt.wf, Bool.and_eq_true] at hwf
  simp only [compileS, burnFuel, List.append_assoc, List.cons_append, List.nil_append,
    List.singleton_append] at hc hK
  simp only [tempsS] at htmp
  have hH := Code.label (i := 0) hc rfl
  have hc1 := hc.tail
  have hc2 := hc1.right
  have hc3 := hc2.right
  have hX := Code.label (i := 3) hc3 rfl
  refine ev_label hc.head ?_
  refine sim_cond hG ctx hT hTab F hF c _ false _ 0 _ hc1.left hwf.1 (htmp.mono (by omega)) σ d Q hI ?_ ?_ ?_
  · -- the condition is false: leave the loop
    intro d1 hcv hE1
    have hI1 := hI.ofE hG hE1
    rw [hX]
    refine ev_label hc3.tail.tail.tail.head ?_
    refine ev_congr (hK.normal σ d1 (by rw [step_while_run, hcv]) hI1 (hE1.spost hI.lo)) ?_
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · -- the condition is true: the body
    intro d1 hcv hE1
    have hI1 := hI.ofE hG hE1
    have hS1 := hE1.spost (G := G) hI.lo
    refine hs { ctx with brk := ctx.lbl path "X" } F _ _ hT hF hc2.left hwf.2 ⟨hN.ret, hN.le, hN.callee, fun hl => by have := hN.leaf hl; simp_all [Stmt.calls], by have := hN.need; simpa [Stmt.need] using this⟩ (htmp.mono (Nat.le_max_right _ _)) σ d1 Q
      (hI1.ctx (ctx' := { ctx with brk := ctx.lbl path "X" }) rfl rfl rfl) (by rw [hE1.r14]; exact hP) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- the body ends normally: burn fuel and go round
      intro σ1 d2 hr1 hI2 hS2
      have hS12 := hS1.trans hS2
      refine ev_sub1 hc3.head fun st hst => ?_
      refine ev_jcc hc3.tail.head (fun hcc => ?_) (fun hcc => ?_)
      · exact hK.exh _ (hS12.trans_g ⟨by simp, Pres.refl _ _⟩)
      · simp only [CondCode.interp] at hcc
        rw [hst] at hcc
        have h0 : d2.regs.r14 ≠ 0 := by
          intro h; simp [h] at hcc
        have hpos : 0 < d2.regs.r14.toNat := by
          rcases Nat.eq_zero_or_pos d2.regs.r14.toNat with h | h
          · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) h0
          · exact h
        refine ev_jmp hc3.tail.tail.head ?_
        rw [hH]
        have hS3 : SPost G F d2 { d2 with regs := d2.regs.set64 .r14 (d2.regs.get64 .r14 - 1), status := st } :=
          SPost.regs (by simp) (by simp) (by simp) (by simp [Reg64s.set64_r14, u64_sub_one_toNat hpos])
        have hS13 := hS12.trans hS3
        refine hE (.while c s) ctx F path k hT hF hc0 (by simp [Stmt.wf, hwf.1, hwf.2]) hN (by simpa only [tempsS] using htmp) σ1 _ Q
          ((hI2.ctx (ctx' := ctx) rfl rfl rfl).of_regs rfl (by simp) (by simp) (fun r hr => by rw [rget_set, if_neg (allocRegs_ne hr).2.2.2.2.2.1]) (fun _ => rfl)) ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · show _ < n
          have := hS12.r14
          simp [Reg64s.set64_r14, u64_sub_one_toNat hpos]
          omega
        · intro σ2 d4 hr2 hI4 hS4
          refine ev_congr (hK.normal σ2 d4 (by rw [step_while_run, hcv]; simp only [Bool.not_false, hr1]; exact hr2)
            hI4 (hS13.trans hS4)) ?_
          simp [compileS, burnFuel]
        · intro σ2 d4 hr2 hI4 hS4
          exact hK.brk σ2 d4 (by rw [step_while_run, hcv]; simp only [Bool.not_false, hr1]; exact hr2) hI4 (hS13.trans hS4)
        · intro v σ2 d4 hr2 hI4 hS4 hv
          exact hK.ret v σ2 d4 (by rw [step_while_run, hcv]; simp only [Bool.not_false, hr1]; exact hr2) hI4 (hS13.trans hS4) hv
        · intro d4 ⟨e, hr2, hne⟩ hG4
          exact hK.err d4 ⟨e, by rw [step_while_run, hcv]; simp only [Bool.not_false, hr1]; exact hr2, hne⟩ (hS13.trans_g hG4)
        · exact fun d4 hG4 => hK.exh d4 (hS13.trans_g hG4)
        · exact hK.tail_fwd rfl rfl hS13 fun vs σ' hr2 => by
            rw [step_while_run, hcv]; simp only [Bool.not_false, hr1]; exact hr2
    · -- `break`: leave the loop
      intro σ1 d2 hr1 hI2 hS2
      show Ev Q d2 (label (ctx.lbl path "X"))
      rw [hX]
      refine ev_label hc3.tail.tail.tail.head ?_
      refine ev_congr (hK.normal σ1 d2 (by rw [step_while_run, hcv]; simp only [Bool.not_false, hr1]) (hI2.ctx (ctx' := ctx) rfl rfl rfl) (hS1.trans hS2)) ?_
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro v σ1 d2 hr1 hI2 hS2 hv
      exact hK.ret v σ1 d2 (by rw [step_while_run, hcv]; simp only [Bool.not_false, hr1]) hI2 (hS1.trans hS2) hv
    · intro d2 ⟨e, hr1, hne⟩ hG2
      exact hK.err d2 ⟨e, by rw [step_while_run, hcv]; simp only [Bool.not_false, hr1], hne⟩ (hS1.trans_g hG2)
    · exact fun d2 hG2 => hK.exh d2 (hS1.trans_g hG2)
    · exact hK.tail_fwd rfl rfl hS1 fun vs σ' hr1 => by rw [step_while_run, hcv]; simp only [Bool.not_false, hr1]
  · intro d1 ⟨e, he⟩ hE1
    exact hK.err d1 ⟨e, by rw [step_while_run, he], by rw [evalCP_error he]; simp⟩
      (hE1.spost (G := G) hI.lo).gpost

end

end L.Compiler
