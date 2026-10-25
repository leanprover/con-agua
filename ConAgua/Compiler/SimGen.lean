module

public import ConAgua.Compiler.SimExpr
public import ConAgua.Compiler.StepGen

@[expose] public section

/-!
# The register-stack code generator (lane leafgen, step G2)

`sim_gen`: the code `gen ctx e d fr` leaves `evalP σ e` in `d`, changes only `d`, the registers
`fr` and the flags (`XPost`), no memory; or reaches `ca_error` exactly when `evalP σ e` fails.
`d` and `fr` are distinct, none of `rsp`, `rbp`, `r14`, `r15` (nor `rsi` with a tier local), and
`e` reads none of them (`GOk`): so `d` may be the register of a local `e` does not read (the
target of `x := e`, a result register), and the invariant holds throughout for a ghost state
(`St.ghost`) that sets the locals in the written registers to their contents.
-/

namespace L.Compiler

open L

theorem reg64_beq_iff {a b : Reg64} : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

instance : LawfulBEq Reg64 where
  eq_of_beq h := reg64_beq_iff.mp h
  rfl {a} := reg64_beq_iff.mpr rfl

/-- What the register-stack code changes: the registers `W` and the flags; not memory. -/
structure XPost (W : List Reg64) (s s' : MachineData) : Prop where
  keep : ∀ r, r ∉ W → s'.regs.get64 r = s.regs.get64 r
  mem : s'.dmem = s.dmem

theorem XPost.refl (W : List Reg64) (s : MachineData) : XPost W s s := ⟨fun _ _ => rfl, rfl⟩

theorem XPost.trans {W W' : List Reg64} {s s' s'' : MachineData} (h : XPost W s s') (h' : XPost W' s' s'') :
    XPost (W ++ W') s s'' :=
  ⟨fun r hr => by
    simp only [List.mem_append, not_or] at hr
    rw [h'.keep r hr.2, h.keep r hr.1], h'.mem.trans h.mem⟩

theorem XPost.mono {W W' : List Reg64} {s s' : MachineData} (h : XPost W s s') (hW : ∀ r ∈ W, r ∈ W') :
    XPost W' s s' := ⟨fun r hr => h.keep r fun h' => hr (hW r h'), h.mem⟩

/-- A register the generated code may write. -/
structure DReg (ctx : Ctx) (r : Reg64) : Prop where
  rsp : r ≠ .rsp
  rbp : r ≠ .rbp
  r14 : r ≠ .r14
  r15 : r ≠ .r15
  rsi : ctx.treg ≠ none → r ≠ .rsi

/-- The registers `W` may be written by code for `e`: distinct, writable, not read by `e`. -/
structure ROk (ctx : Ctx) (e : Expr) (W : List Reg64) : Prop where
  nd : W.Nodup
  dr : ∀ r ∈ W, DReg ctx r
  rd : ∀ r ∈ W, Expr.readsReg ctx.alloc r e = false

/-- The target and scratch registers of `gen ctx e d fr` fit. -/
abbrev GOk (ctx : Ctx) (e : Expr) (d : Reg64) (fr : List Reg64) : Prop := ROk ctx e (d :: fr)

theorem ROk.sub {ctx : Ctx} {e : Expr} {W : List Reg64} (h : ROk ctx e W) {e' : Expr} {W' : List Reg64}
    (hnd : W'.Nodup) (hsub : ∀ r ∈ W', r ∈ W)
    (hrd : ∀ r, Expr.readsReg ctx.alloc r e = false → Expr.readsReg ctx.alloc r e' = false) :
    ROk ctx e' W' :=
  ⟨hnd, fun r hr => h.dr r (hsub r hr), fun r hr => hrd r (h.rd r (hsub r hr))⟩

/-- The L state with the locals kept in the registers `W` set to their contents in `R`: a ghost
state, for code that writes registers whose locals the expression does not read. -/
def _root_.L.St.ghost (al : List (Var × Reg64)) (W : List Reg64) (R : Reg64s) (σ : St) : St :=
  { σ with loc := fun y => match al.lookup y with
    | some r => if r ∈ W then UInt64.ofBitVec (R.get64 r) else σ.loc y
    | none => σ.loc y }

theorem evalP_ghost {al : List (Var × Reg64)} {W : List Reg64} {R : Reg64s} {σ : St} :
    ∀ e, (∀ r ∈ W, Expr.readsReg al r e = false) → evalP (σ.ghost al W R) e = evalP σ e := by
  intro e
  induction e with
  | var x =>
    intro h
    simp only [evalP, St.ghost]
    split
    · rename_i r hr
      have := h r
      simp only [Expr.readsReg, hr, BEq.rfl] at this
      split
      · rename_i hW; exact absurd (this hW) (by decide)
      · rfl
    · rfl
  | bin op a b iha ihb =>
    intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
    simp only [evalP, iha fun r hr => (h r hr).1, ihb fun r hr => (h r hr).2]
  | cmpw op a b iha ihb =>
    intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
    simp only [evalP, iha fun r hr => (h r hr).1, ihb fun r hr => (h r hr).2]
  | ld8 a i ih => intro h; simp only [Expr.readsReg] at h; simp only [evalP, ih h]; rfl
  | ld64 a i ih => intro h; simp only [Expr.readsReg] at h; simp only [evalP, ih h]; rfl
  | ldc d i ih => intro h; simp only [Expr.readsReg] at h; simp only [evalP, ih h]
  | ld64t a t i iht ihi =>
    intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
    simp only [evalP, iht fun r hr => (h r hr).1, ihi fun r hr => (h r hr).2]; rfl
  | len64t a t ih => intro h; simp only [Expr.readsReg] at h; simp only [evalP, ih h]; rfl
  | ld8x8 b i ih => intro h; simp only [Expr.readsReg] at h; simp only [evalP, ih h]; rfl
  | _ => intro _; rfl


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

/-- No local is kept in a register of the pool. -/
theorem pool_free {ctx : Ctx} (hal : AllocOk ctx) {r : Reg64} (h : r ∈ ctx.pool) :
    ∀ x, ctx.alloc.lookup x ≠ some r := by
  intro x hx
  have hm := lookup_mem hx
  have ha := allocRegs_ne (hal.reg x r hx)
  simp only [Ctx.pool, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_filter,
    Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at h
  rcases h with (rfl | rfl | rfl) | ⟨_, h1, _⟩
  · exact ha.1 rfl
  · exact ha.2.1 rfl
  · exact ha.2.2.1 rfl
  · exact absurd (h1 _ hm) (by simp)

theorem readsReg_free {al : List (Var × Reg64)} {r : Reg64} (h : ∀ x, al.lookup x ≠ some r) :
    ∀ e, Expr.readsReg al r e = false := by
  intro e
  induction e with
  | var x => simp only [Expr.readsReg, beq_eq_false_iff_ne, ne_eq]; exact h x
  | bin _ _ _ iha ihb | cmpw _ _ _ iha ihb | ld64t _ _ _ iha ihb => simp [Expr.readsReg, iha, ihb]
  | ld8 _ _ ih | ld64 _ _ ih | ldc _ _ ih | len64t _ _ ih | ld8x8 _ _ ih => simp [Expr.readsReg, ih]
  | _ => rfl

theorem pool_dreg {ctx : Ctx} {r : Reg64} (h : r ∈ ctx.pool) : DReg ctx r := by
  simp only [Ctx.pool, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_filter,
    Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    rcases h with (rfl | rfl | rfl) | ⟨(rfl | rfl | rfl | rfl | rfl | rfl), _, h2⟩ <;> simp_all

theorem pool_nodup (ctx : Ctx) : ctx.pool.Nodup := by
  unfold Ctx.pool
  refine List.nodup_append.mpr ⟨by decide, List.Nodup.sublist List.filter_sublist (by decide), ?_⟩
  intro a ha b hb hab
  subst hab
  simp only [List.mem_filter] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl <;> simp at hb

theorem Inv.ghost {G : Layout} {ctx : Ctx} {F : Nat} {σ : St} {s s' : MachineData} (hI : Inv G ctx F σ s)
    {W : List Reg64} (hX : XPost W s s') (hW : ∀ r ∈ W, DReg ctx r) :
    Inv G ctx F (σ.ghost ctx.alloc W s'.regs) s' := by
  have hk : ∀ r, r ∉ W → s'.regs.get64 r = s.regs.get64 r := hX.keep
  have hsp : s'.regs.rsp = s.regs.rsp :=
    UInt64.toBitVec_inj.mp (by simpa using hk .rsp fun h => (hW _ h).rsp rfl)
  have h15 : s'.regs.r15 = s.regs.r15 :=
    UInt64.toBitVec_inj.mp (by simpa using hk .r15 fun h => (hW _ h).r15 rfl)
  exact {
    r15 := h15 ▸ hI.r15
    lo := hsp ▸ hI.lo
    lo8 := hsp ▸ hI.lo8
    hi := hsp ▸ hI.hi
    slot := hI.slot
    al := hI.al
    reg := fun y hy r hr => by
      simp only [St.ghost, hr]
      split
      · simp
      · rename_i hrW; rw [hk r hrW]; exact hI.reg y hy r hr
    frame := fun y hy hyn => by
      simp only [St.ghost, hyn, hX.mem, hsp]; exact hI.frame y hy hyn
    mem := by rw [hX.mem]; exact hI.mem
    tr := fun y hy => by
      have hrsi : s'.regs.rsi = s.regs.rsi := rsi_of_get64 (hk .rsi fun h => (hW _ h).rsi (by simp [hy]) rfl)
      simp only [St.ghost, hI.al.talloc y hy, hrsi]; exact hI.tr y hy }

/-- The ghost state of registers no local is kept in is the state itself. -/
theorem St.ghost_free {al : List (Var × Reg64)} {W : List Reg64} (h : ∀ r ∈ W, ∀ x, al.lookup x ≠ some r)
    (R : Reg64s) (σ : St) : σ.ghost al W R = σ := by
  cases σ
  simp only [St.ghost, St.mk.injEq, true_and]
  funext y
  split
  · rename_i r hr; split
    · rename_i hW; exact absurd hr (h r hW y)
    · rfl
  · rfl

theorem XPost.upd {W : List Reg64} {s s1 : MachineData} (h : XPost W s s1) {R : Reg64s}
    (hR : ∀ r, r ∉ W → R.get64 r = s1.regs.get64 r) (st : StatusFlags) :
    XPost W s { s1 with regs := R, status := st } :=
  ⟨fun r hr => (hR r hr).trans (h.keep r hr), h.mem⟩

theorem XPost.set {W : List Reg64} {s s1 : MachineData} (h : XPost W s s1) {r : Reg64} (hr : r ∈ W)
    (v : BitVec 64) (st : StatusFlags) :
    XPost W s { s1 with regs := s1.regs.set64 r v, status := st } :=
  h.upd (fun r' hr' => by rw [rget_set, if_neg (by intro e; subst e; exact hr' hr)]) st

theorem XPost.flags {W : List Reg64} {s s1 : MachineData} (h : XPost W s s1) (st : StatusFlags) :
    XPost W s { s1 with status := st } := h.upd (fun _ _ => rfl) st

/-! ## The specification of a code generator for an expression -/

section
variable [Host] {G : Layout} (hG : G.Ok) {ctx : Ctx} (hT : ctx.tab = G.tab)
  (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
  {F : Nat} (hF : 8 * F + 8 < maxOff)

/-- `g` is a code generator for `e`: its code leaves `e`'s value in the target register and
changes only the target and scratch registers (and the flags), or reaches `ca_error` when `e`
fails. -/
def GenSpec (G : Layout) (ctx : Ctx) (F : Nat) (e : Expr) (g : GenF) : Prop :=
  ∀ (d : Reg64) (fr : List Reg64) (code : Program) (k : Nat), g d fr = some code → Code code k →
    GOk ctx e d fr → Expr.wf ctx.nl G.tab e = true →
    ∀ (σ : St) (s : MachineData) (Q : MachineState → Prop), Inv G ctx F σ s →
    (∀ v s', evalP σ e = .ok v → s'.regs.get64 d = v.toBitVec → XPost (d :: fr) s s' →
      Ev Q s' (at_ (k + code.length))) →
    (∀ s', (∃ x, evalP σ e = .error x) → XPost (d :: fr) s s' → Ev Q s' (label errorL)) →
    Ev Q s (at_ k)

end

theorem evalP_bin {σ : St} {op : BinOp} {a b : Expr} {va vb : Word} (ha : evalP σ a = .ok va)
    (hb : evalP σ b = .ok vb) : evalP σ (.bin op a b) = .ok (op.eval va vb) := by
  simp [evalP, ha, hb]; rfl

theorem evalP_bin_errA {σ : St} {op : BinOp} {a b : Expr} (h : ∃ x, evalP σ a = .error x) :
    ∃ x, evalP σ (.bin op a b) = .error x := by
  obtain ⟨x, hx⟩ := h; exact ⟨x, by simp [evalP, hx]; rfl⟩

theorem evalP_bin_errB {σ : St} {op : BinOp} {a b : Expr} {va : Word} (ha : evalP σ a = .ok va)
    (h : ∃ x, evalP σ b = .error x) : ∃ x, evalP σ (.bin op a b) = .error x := by
  obtain ⟨x, hx⟩ := h; exact ⟨x, by simp [evalP, ha, hx]; rfl⟩

theorem BinOp.eval_comm {op : BinOp} (h : op.comm = true) (a b : Word) : op.eval a b = op.eval b a := by
  cases op <;> simp only [BinOp.comm, reduceCtorEq] at h <;> simp only [BinOp.eval]
  · exact UInt64.add_comm a b
  · exact UInt64.mul_comm a b
  · exact UInt64.and_comm a b
  · exact UInt64.or_comm a b
  · exact UInt64.xor_comm a b

theorem readsReg_binL {al : List (Var × Reg64)} {op : BinOp} {a b : Expr} {r : Reg64}
    (h : Expr.readsReg al r (.bin op a b) = false) : Expr.readsReg al r a = false := by
  simp only [Expr.readsReg, Bool.or_eq_false_iff] at h; exact h.1

theorem readsReg_binR {al : List (Var × Reg64)} {op : BinOp} {a b : Expr} {r : Reg64}
    (h : Expr.readsReg al r (.bin op a b) = false) : Expr.readsReg al r b = false := by
  simp only [Expr.readsReg, Bool.or_eq_false_iff] at h; exact h.2

theorem ofInt_toInt64 (k : Word) : BitVec.ofInt 64 (Int64.ofInt k.toInt64.toInt).toInt = k.toBitVec := by
  rw [Int64.ofInt_toInt]
  show BitVec.ofInt 64 k.toInt64.toBitVec.toInt = _
  rw [BitVec.ofInt_toInt]; rfl

section
variable [Host] {G : Layout} {ctx : Ctx} {F : Nat}

/-- A leaf whose code is one move of its simple operand. -/
theorem gen_simple (hT : ctx.tab = G.tab)
    (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
    (hF : 8 * F + 8 < maxOff) {e : Expr} {g : GenF}
    (hs : ∀ d fr, g d fr = (simpleOp ctx e).map fun o => [i64 (.mov (.reg (rr d)) o)]) :
    GenSpec G ctx F e g := by
  intro d fr code k hg hc hok hwf σ s Q hI hv herr
  rw [hs] at hg
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hg
  obtain ⟨v, hv', hr⟩ := simpleOp_reads hT hTab hF hI hwf ho
  exact ev_movRO hc.head hr (hv v _ hv' (by simp [rget_set]) ((XPost.refl _ s).set List.mem_cons_self _ s.status))

theorem gen_const (w : Word) : GenSpec G ctx F (.const w) (gen ctx (.const w)) := by
  intro d fr code k hg hc hok hwf σ s Q hI hv herr
  simp only [gen, Option.some.injEq] at hg; subst hg
  exact ev_movRI hc.head (hv w _ rfl (by simp [rget_set]) ((XPost.refl _ s).set List.mem_cons_self _ s.status))

/-- `d := a op b` in one `lea` (`genLea`). -/
theorem genLea_spec {op : BinOp} {a b : Expr} {d : Reg64} {code : Program} (hg : genLea ctx op a b d = some code)
    {fr : List Reg64} {k : Nat} (hc : Code code k) (hwf : Expr.wf ctx.nl G.tab (.bin op a b) = true)
    {σ : St} {s : MachineData} {Q : MachineState → Prop} (hI : Inv G ctx F σ s) (hd : d ∈ d :: fr)
    (hv : ∀ v s', evalP σ (.bin op a b) = .ok v → s'.regs.get64 d = v.toBitVec → XPost (d :: fr) s s' →
      Ev Q s' (at_ (k + code.length))) : Ev Q s (at_ k) := by
  simp only [Expr.wf, Bool.and_eq_true] at hwf
  unfold genLea at hg
  split at hg
  · rename_i r kk hr
    split at hg
    · cases hg
      obtain ⟨x, rfl, hx⟩ : ∃ x, a = .var x ∧ ctx.alloc.lookup x = some r := by
        cases a <;> simp_all [regOf]
      have hxl : x < ctx.nl := by simpa [Expr.wf] using hwf.1
      refine ev_leaS hc.head (hv _ _ (evalP_bin rfl rfl) ?_ ((XPost.refl _ s).set hd _ s.status))
      simp only [rget_set, ite_true, hI.reg x hxl r hx, ofInt_toInt64, BinOp.eval, UInt64.toBitVec_add]
    · cases hg
  · rename_i r kk hr
    split at hg
    · cases hg
      obtain ⟨x, rfl, hx⟩ : ∃ x, a = .var x ∧ ctx.alloc.lookup x = some r := by
        cases a <;> simp_all [regOf]
      have hxl : x < ctx.nl := by simpa [Expr.wf] using hwf.1
      refine ev_leaS hc.head (hv _ _ (evalP_bin rfl rfl) ?_ ((XPost.refl _ s).set hd _ s.status))
      simp only [rget_set, ite_true, hI.reg x hxl r hx, ofInt_toInt64, BinOp.eval, UInt64.toBitVec_add,
        UInt64.toBitVec_sub]
      simp [BitVec.sub_eq_add_neg]
    · cases hg
  · rename_i r y hr
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hg
    obtain ⟨x, rfl, hx⟩ : ∃ x, a = .var x ∧ ctx.alloc.lookup x = some r := by
      cases a <;> simp_all [regOf]
    have hxl : x < ctx.nl := by simpa [Expr.wf] using hwf.1
    have hyl : y < ctx.nl := by simpa [Expr.wf] using hwf.2
    refine ev_leaRR hc.head (hv _ _ (evalP_bin rfl rfl) ?_ ((XPost.refl _ s).set hd _ s.status))
    simp only [rget_set, ite_true, hI.reg x hxl r hx, hI.reg y hyl t ht, BinOp.eval, UInt64.toBitVec_add]
  · cases hg

end

section
variable [Host] {G : Layout} {ctx : Ctx} {F : Nat}

theorem mem_app_cons {W W' : List Reg64} {d : Reg64} (h1 : ∀ r ∈ W, r ∈ d :: W') :
    ∀ r ∈ W ++ W', r ∈ d :: W' := fun r h =>
  (List.mem_append.mp h).elim (h1 r) (fun h => List.mem_cons_of_mem _ h)

/-- `d := a op b` (`genAlu`). -/
theorem genAlu_spec (hT : ctx.tab = G.tab)
    (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
    (hF : 8 * F + 8 < maxOff) {op : BinOp} {a b : Expr} {ga gb : GenF}
    (ha : GenSpec G ctx F a ga) (hb : GenSpec G ctx F b gb) :
    GenSpec G ctx F (.bin op a b) (genAlu ctx op a b ga gb) := by
  intro d fr code k hg hc hok hwf σ s Q hI hv herr
  have hwf' := hwf
  simp only [Expr.wf, Bool.and_eq_true] at hwf'
  have hda : GOk ctx a d fr := hok.sub hok.nd (fun r h => h) fun r h => readsReg_binL h
  have hdb : GOk ctx b d fr := hok.sub hok.nd (fun r h => h) fun r h => readsReg_binR h
  unfold genAlu at hg
  split at hg
  · rename_i c hl; cases hg
    exact genLea_spec hl hc hwf hI List.mem_cons_self hv
  split at hg
  · rename_i ob hob
    obtain ⟨ca, hca, hg⟩ := Option.bind_eq_some_iff.mp hg
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hg
    refine ha d fr ca k hca hc.left hda hwf'.1 σ s Q hI ?_ (fun s1 he hX => herr s1 (evalP_bin_errA he) hX)
    intro va s1 hva hd1 hX1
    have hI1 := hI.ghost hX1 hok.dr
    obtain ⟨vb, hvb, hrb⟩ := simpleOp_reads hT hTab hF hI1 hwf'.2 hob
    rw [evalP_ghost b fun r hr => hdb.rd r hr] at hvb
    refine ev_aluOp hi hc.right.head hrb fun st => ?_
    refine ev_congr (hv _ _ (evalP_bin hva hvb) ?_ (hX1.set List.mem_cons_self _ st))
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simp [rget_set, hd1]
  split at hg
  · rename_i oa hoa
    have hcm : op.comm = true := by cases h : op.comm <;> simp_all
    have hoa' : simpleOp ctx a = some oa := by simp_all
    obtain ⟨cb, hcb, hg⟩ := Option.bind_eq_some_iff.mp hg
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hg
    obtain ⟨va, hva, -⟩ := simpleOp_reads hT hTab hF hI hwf'.1 hoa'
    refine hb d fr cb k hcb hc.left hdb hwf'.2 σ s Q hI ?_ (fun s1 he hX => herr s1 (evalP_bin_errB hva he) hX)
    intro vb s1 hvb hd1 hX1
    have hI1 := hI.ghost hX1 hok.dr
    obtain ⟨va', hva', hra⟩ := simpleOp_reads hT hTab hF hI1 hwf'.1 hoa'
    rw [evalP_ghost a fun r hr => hda.rd r hr, hva] at hva'
    cases hva'
    refine ev_aluOp hi hc.right.head hra fun st => ?_
    refine ev_congr (hv _ _ (evalP_bin hva hvb) ?_ (hX1.set List.mem_cons_self _ st))
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simp [rget_set, hd1, BinOp.eval_comm hcm]
  split at hg
  · rename_i t fr'
    obtain ⟨ca, hca, hg⟩ := Option.bind_eq_some_iff.mp hg
    obtain ⟨cb, hcb, hg⟩ := Option.bind_eq_some_iff.mp hg
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hg
    have hnd := hok.nd
    have hdn : d ∉ t :: fr' := (List.nodup_cons.mp hnd).1
    have htb : GOk ctx b t fr' :=
      hok.sub (List.nodup_cons.mp hnd).2 (fun r h => List.mem_cons_of_mem _ h) fun r h => readsReg_binR h
    refine ha d (t :: fr') ca k hca hc.left.left hda hwf'.1 σ s Q hI ?_
      (fun s1 he hX => herr s1 (evalP_bin_errA he) hX)
    intro va s1 hva hd1 hX1
    have hI1 := hI.ghost hX1 hok.dr
    refine hb t fr' cb (k + ca.length) hcb hc.left.right htb hwf'.2 _ s1 Q hI1 ?_ ?_
    · intro vb s2 hvb hd2 hX2
      rw [evalP_ghost b fun r hr => hdb.rd r hr] at hvb
      have hdk : s2.regs.get64 d = va.toBitVec := by rw [hX2.keep d hdn]; exact hd1
      have hcR : Code [i] (k + ca.length + cb.length) := by
        have := hc.right; simpa only [List.length_append, Nat.add_assoc] using this
      refine ev_aluOp hi hcR.head (.inr (.inr ⟨t, rfl, hd2⟩)) fun st => ?_
      refine ev_congr (hv _ _ (evalP_bin hva hvb) ?_
        (((hX1.trans hX2).mono (mem_app_cons fun r h => h)).set List.mem_cons_self _ st)) (by simp; omega)
      simp [rget_set, hdk]
    · intro s2 he hX2
      rw [evalP_ghost b fun r hr => hdb.rd r hr] at he
      exact herr s2 (evalP_bin_errB hva he) ((hX1.trans hX2).mono (mem_app_cons fun r h => h))
  · cases hg

omit [Host] in
theorem mem_filter_sub {W : List Reg64} {p : Reg64 → Bool} : ∀ r ∈ W.filter p, r ∈ W :=
  fun _ h => (List.mem_filter.mp h).1

/-- `d := mulhi a b` (`genMulhi`). -/
theorem genMulhi_spec {a b : Expr} {ga gb : GenF}
    (ha : GenSpec G ctx F a ga) (hb : GenSpec G ctx F b gb) :
    GenSpec G ctx F (.bin .mulhi a b) (genMulhi ga gb) := by
  intro d fr code k hg hc hok hwf σ s Q hI hv herr
  have hwf' := hwf
  simp only [Expr.wf, Bool.and_eq_true] at hwf'
  unfold genMulhi at hg
  split at hg
  case isFalse => cases hg
  rename_i hcond
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hcond
  have hrax : Reg64.rax ∈ d :: fr := hcond.1.elim (fun h => h ▸ List.mem_cons_self) (fun h => List.mem_cons_of_mem _ h)
  have hrdx : Reg64.rdx ∈ d :: fr := List.mem_cons_of_mem _ hcond.2
  split at hg
  case h_2 => cases hg
  rename_i t rest ht
  have htm : t ∈ (d :: fr).filter (fun r => r != .rax && r != .rdx) := ht ▸ List.mem_cons_self
  simp only [List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq] at htm
  obtain ⟨htW, htr, htd⟩ := htm
  obtain ⟨ca, hca, hg⟩ := Option.bind_eq_some_iff.mp hg
  obtain ⟨cb, hcb, rfl⟩ := Option.map_eq_some_iff.mp hg
  have hnd := hok.nd
  -- `a` into `rax`
  have hFa : GOk ctx a .rax ((d :: fr).filter (· != .rax)) :=
    hok.sub (List.nodup_cons.mpr ⟨by simp, List.Nodup.sublist List.filter_sublist hnd⟩)
      (fun r h => by
        rcases List.mem_cons.mp h with rfl | h
        · exact hrax
        · exact mem_filter_sub r h) fun r h => readsReg_binL h
  refine ha .rax _ ca k hca hc.left.left hFa hwf'.1 σ s Q hI ?_ (fun s1 he hX => herr s1 (evalP_bin_errA he)
    (hX.mono fun r h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact hrax
      · exact mem_filter_sub r h))
  intro va s1 hva hr1 hX1
  have hI1 := hI.ghost hX1 hFa.dr
  have hFb : GOk ctx b t ((d :: fr).filter fun r => r != .rax && r != t) :=
    hok.sub (List.nodup_cons.mpr ⟨by simp, List.Nodup.sublist List.filter_sublist hnd⟩)
      (fun r h => by
        rcases List.mem_cons.mp h with rfl | h
        · exact htW
        · exact mem_filter_sub r h) fun r h => readsReg_binR h
  have hX1' : XPost (d :: fr) s s1 := hX1.mono fun r h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact hrax
    · exact mem_filter_sub r h
  refine hb t _ cb (k + ca.length) hcb hc.left.right hFb hwf'.2 _ s1 Q hI1 ?_ ?_
  · intro vb s2 hvb ht2 hX2
    rw [evalP_ghost b fun r hr => (hok.sub hFa.nd (fun r h => by
        rcases List.mem_cons.mp h with rfl | h
        · exact hrax
        · exact mem_filter_sub r h) fun r h => readsReg_binR h).rd r hr] at hvb
    have hX2' : XPost (d :: fr) s1 s2 := hX2.mono fun r h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact htW
      · exact mem_filter_sub r h
    have hra2 : s2.regs.rax = va := by
      have := hX2.keep .rax (by simp [Ne.symm htr])
      apply UInt64.toBitVec_inj.mp; simpa [hr1] using this
    have hc2 : Code [i64 (.mul (.reg (rr t))), movRR d .rdx] (k + ca.length + cb.length) := by
      have := hc.right; simpa only [List.length_append, Nat.add_assoc] using this
    refine ev_mulR hc2.head fun st => ?_
    refine ev_movRR hc2.tail.head ?_
    refine ev_congr (hv _ _ (evalP_bin hva hvb) ?_ ?_) (by simp; omega)
    · simp [rget_set, hra2, ht2, Reg64s.set64_rdx]
    · refine ((hX1'.trans hX2').mono fun r h => (List.mem_append.mp h).elim id id).upd ?_ st
      intro r hr
      have h1 : r ≠ d := fun e => hr (e ▸ List.mem_cons_self)
      have h2 : r ≠ .rdx := fun e => hr (e ▸ hrdx)
      have h3 : r ≠ .rax := fun e => hr (e ▸ hrax)
      simp [rget_set, h1, h2, h3]
  · intro s2 he hX2
    rw [evalP_ghost b fun r hr => (hok.sub hFa.nd (fun r h => by
        rcases List.mem_cons.mp h with rfl | h
        · exact hrax
        · exact mem_filter_sub r h) fun r h => readsReg_binR h).rd r hr] at he
    have hX2' : XPost (d :: fr) s1 s2 := hX2.mono fun r h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact htW
      · exact mem_filter_sub r h
    exact herr s2 (evalP_bin_errB hva he) ((hX1'.trans hX2').mono fun r h => (List.mem_append.mp h).elim id id)

end

section
variable [Host] {G : Layout} {ctx : Ctx} {F : Nat}

/-- `d := a op k` by `a` into `d`, then one instruction `i` on `d` (a shift by a constant). -/
theorem genPost_spec {op : BinOp} {a : Expr} {ga : GenF} {kk : Word} {d : Reg64} {i : Directive}
    (hstep : ∀ (s : MachineData) (Q : MachineState → Prop) (k : Nat), Host.prog[k]? = some i →
      (∀ st, Ev Q { s with regs := s.regs.set64 d (op.eval (UInt64.ofBitVec (s.regs.get64 d)) kk).toBitVec, status := st }
        (at_ (k + 1))) → Ev Q s (at_ k))
    (ha : GenSpec G ctx F a ga) {fr : List Reg64} {code : Program} {k : Nat}
    (hg : (ga d fr).map (· ++ [i]) = some code)
    (hc : Code code k) (hok : GOk ctx (.bin op a (.const kk)) d fr)
    (hwf : Expr.wf ctx.nl G.tab (.bin op a (.const kk)) = true)
    {σ : St} {s : MachineData} {Q : MachineState → Prop} (hI : Inv G ctx F σ s)
    (hv : ∀ v s', evalP σ (.bin op a (.const kk)) = .ok v → s'.regs.get64 d = v.toBitVec →
      XPost (d :: fr) s s' → Ev Q s' (at_ (k + code.length)))
    (herr : ∀ s', (∃ x, evalP σ (.bin op a (.const kk)) = .error x) → XPost (d :: fr) s s' →
      Ev Q s' (label errorL)) : Ev Q s (at_ k) := by
  simp only [Expr.wf, Bool.and_eq_true] at hwf
  obtain ⟨ca, hca, rfl⟩ := Option.map_eq_some_iff.mp hg
  refine ha d fr ca k hca hc.left (hok.sub hok.nd (fun r h => h) fun r h => readsReg_binL h) hwf.1 σ s Q hI
    ?_ (fun s1 he hX => herr s1 (evalP_bin_errA he) hX)
  intro va s1 hva hd1 hX1
  refine hstep s1 Q _ hc.right.head fun st => ?_
  refine ev_congr (hv _ _ (evalP_bin hva rfl) ?_ (hX1.set List.mem_cons_self _ st)) (by simp; omega)
  simp [rget_set, hd1]

/-- `d := a op b` (`genBin`). -/
theorem genBin_spec (hT : ctx.tab = G.tab)
    (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
    (hF : 8 * F + 8 < maxOff) (op : BinOp) {a b : Expr} {ga gb : GenF}
    (ha : GenSpec G ctx F a ga) (hb : GenSpec G ctx F b gb) :
    GenSpec G ctx F (.bin op a b) (genBin ctx op a b ga gb) := by
  intro d fr code k hg hc hok hwf σ s Q hI hv herr
  unfold genBin at hg
  split at hg
  · rename_i kk
    refine genPost_spec (op := .shl) (fun s Q k hk h => ev_shiftR (op := .shl) (Nat.mod_lt _ (by decide))
      (Or.inl rfl) hk fun st => ?_) ha hg hc hok hwf hI hv herr
    have := h st; simp only [BinOp.eval] at this ⊢; rwa [shl_mod64]
  · rename_i kk
    refine genPost_spec (op := .shr) (fun s Q k hk h => ev_shiftR (op := .shr) (Nat.mod_lt _ (by decide))
      (Or.inr rfl) hk fun st => ?_) ha hg hc hok hwf hI hv herr
    have := h st; simp only [BinOp.eval] at this ⊢; rwa [shr_mod64]
  · rename_i kk
    split at hg
    · rename_i hp
      have hp' : kk.toNat = 2 ^ Nat.log2 kk.toNat := by simpa using hp
      refine genPost_spec (op := .mul) (fun s Q k hk h => ev_shiftR (op := .shl) (log2_lt64 kk hp')
        (Or.inl rfl) hk fun st => ?_) ha hg hc hok hwf hI hv herr
      have := h st; simp only [BinOp.eval] at this ⊢; rwa [shl_log2 _ _ hp']
    · exact genAlu_spec hT hTab hF ha hb d fr code k hg hc hok hwf σ s Q hI hv herr
  · exact genMulhi_spec ha hb d fr code k hg hc hok hwf σ s Q hI hv herr
  · cases hg
  · cases hg
  · exact genAlu_spec hT hTab hF ha hb d fr code k hg hc hok hwf σ s Q hI hv herr

end

/-! ## Array loads -/

/-- `[ln]` holds the length of the word array `arr`, `[bs]` its base `B`, from which it lies in
memory. -/
structure ArrW (s : MachineData) (ln bs : AddrExpr) (arr : Array Word) : Prop where
  len : MemW s ln (UInt64.ofNat arr.size)
  base : ∃ B : Nat, MemW s bs (UInt64.ofNat B) ∧ B + 8 * arr.size < 2 ^ 64 ∧
    ∀ j (h : j < arr.size), rdW s.dmem (A (B + 8 * j)) = some arr[j]

/-- The same for a byte array. -/
structure ArrB (s : MachineData) (ln bs : AddrExpr) (arr : Array UInt8) : Prop where
  len : MemW s ln (UInt64.ofNat arr.size)
  base : ∃ B : Nat, MemW s bs (UInt64.ofNat B) ∧ B + arr.size < 2 ^ 64 ∧
    ∀ j (h : j < arr.size), s.dmem.get? (A (B + j)) = some arr[j]

theorem interp_be (a b : UInt64) : CondCode.be.interp (cmpFlags a.toBitVec b.toBitVec) = decide (a ≤ b) := by
  have := cmpCC_interp .ule a b; simpa [cmpCC, Cmp.eval] using this

theorem ofInt_small {k : Word} (hk : k.toNat < 2 ^ 28) : (Int64.ofInt (k.toNat : Int)).toBitVec = k.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  simp only [Int64.toBitVec_ofInt, BitVec.toNat_ofInt, UInt64.toNat_toBitVec]
  have : ((k.toNat : Int) % (2 ^ 64 : Nat) : Int) = k.toNat := Int.emod_eq_of_lt (by omega) (by omega)
  omega

theorem lookup_ne_of_readsReg {al : List (Var × Reg64)} {x : Var} {r d : Reg64} (hx : al.lookup x = some r)
    (h : Expr.readsReg al d (.var x) = false) : r ≠ d := by
  intro e; subst e; simp [Expr.readsReg, hx] at h

section
variable [Host] {G : Layout} {ctx : Ctx} {F : Nat}

/-- `d := A[i]` for a word array (`genLd`). -/
theorem genLdW_spec (hF : 8 * F + 8 < maxOff) {ln bs : AddrExpr} {i : Expr} {gi : GenF}
    (hi : GenSpec G ctx F i gi) {d : Reg64} {fr : List Reg64} {code : Program} {k : Nat}
    (hg : genLd ctx ln bs false i gi d fr = some code) (hc : Code code k) (hok : GOk ctx i d fr)
    (hwf : Expr.wf ctx.nl G.tab i = true) {arr : Array Word}
    {σ : St} {s : MachineData} {Q : MachineState → Prop} (hI : Inv G ctx F σ s)
    (hA : ∀ s', XPost (d :: fr) s s' → ArrW s' ln bs arr)
    (hv : ∀ j (h : j.toNat < arr.size) s', evalP σ i = .ok j → s'.regs.get64 d = arr[j.toNat].toBitVec →
      XPost (d :: fr) s s' → Ev Q s' (at_ (k + code.length)))
    (herr : ∀ s', ((∃ x, evalP σ i = .error x) ∨ ∃ j, evalP σ i = .ok j ∧ ¬ j.toNat < arr.size) →
      XPost (d :: fr) s s' → Ev Q s' (label errorL)) : Ev Q s (at_ k) := by
  have hd : d ∈ d :: fr := List.mem_cons_self
  unfold genLd at hg
  split at hg
  · -- a constant index, folded into the displacement
    rename_i kk
    split at hg
    case isFalse => cases hg
    rename_i hk
    cases hg
    simp only [ldA, Bool.false_eq_true, ite_false] at hc hv
    obtain ⟨hlen, B, hB, hBs, hget⟩ := hA s (XPost.refl _ s)
    refine ev_cmpAI hc.head hlen ?_
    rw [ofInt_small hk]
    have hsz : arr.size < 2 ^ 64 := by omega
    refine ev_jcc hc.tail.head (fun hcc => ?_) (fun hcc => ?_)
    · refine herr _ (.inr ⟨kk, rfl, ?_⟩) ((XPost.refl _ s).flags _)
      rw [interp_be] at hcc
      simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz] at hcc
      omega
    · rw [interp_be] at hcc
      simp only [decide_eq_false_iff_not, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz] at hcc
      have hj : kk.toNat < arr.size := by omega
      obtain ⟨_, B', hB', -, -⟩ := hA _ ((XPost.refl _ s).flags (cmpFlags (UInt64.ofNat arr.size).toBitVec kk.toBitVec))
      refine ev_movRA hc.tail.tail.head hB ?_
      refine ev_movRM hc.tail.tail.tail.head ⟨by omega, by omega⟩ (v := arr[kk.toNat]) ?_ ?_
      · simp only [rget_set, ite_true, UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' (show B < 2 ^ 64 by omega)]
        rw [show (8 * (kk.toNat : Int)).toNat = 8 * kk.toNat by omega]
        exact hget _ hj
      · refine ev_congr (hv kk hj _ rfl (by simp [rget_set]) ?_) (by simp)
        exact (((XPost.refl _ s).flags _).set hd _ _).set hd _ _
  · split at hg
    · -- the index in a local's register
      rename_i r hr
      cases hg
      simp only [ldA, Bool.false_eq_true, ite_false] at hc hv
      obtain ⟨x, rfl, hx⟩ : ∃ x, i = .var x ∧ ctx.alloc.lookup x = some r := by
        cases i <;> simp_all [regOf]
      have hxl : x < ctx.nl := by simpa [Expr.wf] using hwf
      have hrd : r ≠ d := lookup_ne_of_readsReg hx (hok.rd d hd)
      obtain ⟨hlen, B, hB, hBs, hget⟩ := hA s (XPost.refl _ s)
      have hsz : arr.size < 2 ^ 64 := by omega
      refine ev_cmpRA hc.head hlen ?_
      rw [hI.reg x hxl r hx]
      refine ev_jcc hc.tail.head (fun hcc => ?_) (fun hcc => ?_)
      · refine herr _ (.inr ⟨σ.loc x, rfl, ?_⟩) ((XPost.refl _ s).flags _)
        rw [interp_nc] at hcc
        simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz] at hcc
        omega
      · rw [interp_nc] at hcc
        simp only [decide_eq_false_iff_not, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz] at hcc
        have hj : (σ.loc x).toNat < arr.size := by omega
        refine ev_movRA hc.tail.tail.head hB ?_
        refine ev_ldX hc.tail.tail.tail.head (v := arr[(σ.loc x).toNat]) ?_ ?_
        · simp only [rget_set, ite_true, if_neg hrd, hI.reg x hxl r hx]
          rw [← hget _ hj]; congr 1
          apply BitVec.eq_of_toNat_eq
          simp [A, UInt64.toNat_ofNat_of_lt' (show B < 2 ^ 64 by omega)]
          omega
        · refine ev_congr (hv _ hj _ rfl (by simp [rget_set]) ?_) (by simp)
          exact (((XPost.refl _ s).flags _).set hd _ _).set hd _ _
    · -- the index into `d`, the base into a scratch register
      split at hg
      case h_2 => cases hg
      rename_i t rest
      obtain ⟨ci, hci, rfl⟩ := Option.map_eq_some_iff.mp hg
      simp only [ldA, Bool.false_eq_true, ite_false] at hc hv
      have htd : t ≠ d := fun e => (List.nodup_cons.mp hok.nd).1 (e ▸ List.mem_cons_self)
      have ht : t ∈ d :: t :: rest := List.mem_cons_of_mem _ List.mem_cons_self
      refine hi d (t :: rest) ci k hci hc.left hok hwf σ s Q hI ?_ (fun s1 he hX => herr s1 (.inl he) hX)
      intro j s1 hj hd1 hX1
      obtain ⟨hlen, B, hB, hBs, hget⟩ := hA s1 hX1
      have hsz : arr.size < 2 ^ 64 := by omega
      have hcR := hc.right
      refine ev_cmpRA hcR.head hlen ?_
      rw [hd1]
      refine ev_jcc hcR.tail.head (fun hcc => ?_) (fun hcc => ?_)
      · refine herr _ (.inr ⟨j, hj, ?_⟩) (hX1.flags _)
        rw [interp_nc] at hcc
        simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz] at hcc
        omega
      · rw [interp_nc] at hcc
        simp only [decide_eq_false_iff_not, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz] at hcc
        have hjs : j.toNat < arr.size := by omega
        obtain ⟨_, B', hB', -, -⟩ := hA _ (hX1.flags (cmpFlags j.toBitVec (UInt64.ofNat arr.size).toBitVec))
        refine ev_movRA hcR.tail.tail.head hB ?_
        refine ev_ldX hcR.tail.tail.tail.head (v := arr[j.toNat]) ?_ ?_
        · simp only [rget_set, ite_true, if_neg (Ne.symm htd), hd1]
          rw [← hget _ hjs]; congr 1
          apply BitVec.eq_of_toNat_eq
          simp [A, UInt64.toNat_ofNat_of_lt' (show B < 2 ^ 64 by omega)]
          omega
        · refine ev_congr (hv _ hjs _ hj (by simp [rget_set]) ?_) (by simp; omega)
          exact ((hX1.flags _).set ht _ _).set hd _ _

/-- `d := A[i]` for a byte array (`genLd`). -/
theorem genLdB_spec (hF : 8 * F + 8 < maxOff) {ln bs : AddrExpr} {i : Expr} {gi : GenF}
    (hi : GenSpec G ctx F i gi) {d : Reg64} {fr : List Reg64} {code : Program} {k : Nat}
    (hg : genLd ctx ln bs true i gi d fr = some code) (hc : Code code k) (hok : GOk ctx i d fr)
    (hwf : Expr.wf ctx.nl G.tab i = true) {arr : Array UInt8}
    {σ : St} {s : MachineData} {Q : MachineState → Prop} (hI : Inv G ctx F σ s)
    (hA : ∀ s', XPost (d :: fr) s s' → ArrB s' ln bs arr)
    (hv : ∀ j (h : j.toNat < arr.size) s', evalP σ i = .ok j → s'.regs.get64 d = arr[j.toNat].toUInt64.toBitVec →
      XPost (d :: fr) s s' → Ev Q s' (at_ (k + code.length)))
    (herr : ∀ s', ((∃ x, evalP σ i = .error x) ∨ ∃ j, evalP σ i = .ok j ∧ ¬ j.toNat < arr.size) →
      XPost (d :: fr) s s' → Ev Q s' (label errorL)) : Ev Q s (at_ k) := by
  have hd : d ∈ d :: fr := List.mem_cons_self
  unfold genLd at hg
  split at hg
  · -- a constant index, folded into the displacement
    rename_i kk
    split at hg
    case isFalse => cases hg
    rename_i hk
    cases hg
    simp only [ldA, ite_true] at hc hv
    obtain ⟨hlen, B, hB, hBs, hget⟩ := hA s (XPost.refl _ s)
    refine ev_cmpAI hc.head hlen ?_
    rw [ofInt_small hk]
    have hsz : arr.size < 2 ^ 64 := by omega
    refine ev_jcc hc.tail.head (fun hcc => ?_) (fun hcc => ?_)
    · refine herr _ (.inr ⟨kk, rfl, ?_⟩) ((XPost.refl _ s).flags _)
      rw [interp_be] at hcc
      simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz] at hcc
      omega
    · rw [interp_be] at hcc
      simp only [decide_eq_false_iff_not, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz] at hcc
      have hj : kk.toNat < arr.size := by omega
      obtain ⟨_, B', hB', -, -⟩ := hA _ ((XPost.refl _ s).flags (cmpFlags (UInt64.ofNat arr.size).toBitVec kk.toBitVec))
      refine ev_movRA hc.tail.tail.head hB ?_
      refine ev_movzxM hc.tail.tail.tail.head ⟨by omega, by omega⟩ (v := arr[kk.toNat]) ?_ ?_
      · simp only [rget_set, ite_true, UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' (show B < 2 ^ 64 by omega)]
        rw [show ((kk.toNat : Int)).toNat = kk.toNat by omega]
        exact hget _ hj
      · refine ev_congr (hv kk hj _ rfl (by simp [rget_set]) ?_) (by simp)
        exact (((XPost.refl _ s).flags _).set hd _ _).set hd _ _
  · split at hg
    · -- the index in a local's register
      rename_i r hr
      cases hg
      simp only [ldA, ite_true] at hc hv
      obtain ⟨x, rfl, hx⟩ : ∃ x, i = .var x ∧ ctx.alloc.lookup x = some r := by
        cases i <;> simp_all [regOf]
      have hxl : x < ctx.nl := by simpa [Expr.wf] using hwf
      have hrd : r ≠ d := lookup_ne_of_readsReg hx (hok.rd d hd)
      obtain ⟨hlen, B, hB, hBs, hget⟩ := hA s (XPost.refl _ s)
      have hsz : arr.size < 2 ^ 64 := by omega
      refine ev_cmpRA hc.head hlen ?_
      rw [hI.reg x hxl r hx]
      refine ev_jcc hc.tail.head (fun hcc => ?_) (fun hcc => ?_)
      · refine herr _ (.inr ⟨σ.loc x, rfl, ?_⟩) ((XPost.refl _ s).flags _)
        rw [interp_nc] at hcc
        simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz] at hcc
        omega
      · rw [interp_nc] at hcc
        simp only [decide_eq_false_iff_not, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz] at hcc
        have hj : (σ.loc x).toNat < arr.size := by omega
        refine ev_movRA hc.tail.tail.head hB ?_
        refine ev_movzxX hc.tail.tail.tail.head (v := arr[(σ.loc x).toNat]) ?_ ?_
        · simp only [rget_set, ite_true, if_neg hrd, hI.reg x hxl r hx]
          rw [← hget _ hj]; congr 1
          apply BitVec.eq_of_toNat_eq
          simp [A, UInt64.toNat_ofNat_of_lt' (show B < 2 ^ 64 by omega)]
        · refine ev_congr (hv _ hj _ rfl (by simp [rget_set]) ?_) (by simp)
          exact (((XPost.refl _ s).flags _).set hd _ _).set hd _ _
    · -- the index into `d`, the base into a scratch register
      split at hg
      case h_2 => cases hg
      rename_i t rest
      obtain ⟨ci, hci, rfl⟩ := Option.map_eq_some_iff.mp hg
      simp only [ldA, ite_true] at hc hv
      have htd : t ≠ d := fun e => (List.nodup_cons.mp hok.nd).1 (e ▸ List.mem_cons_self)
      have ht : t ∈ d :: t :: rest := List.mem_cons_of_mem _ List.mem_cons_self
      refine hi d (t :: rest) ci k hci hc.left hok hwf σ s Q hI ?_ (fun s1 he hX => herr s1 (.inl he) hX)
      intro j s1 hj hd1 hX1
      obtain ⟨hlen, B, hB, hBs, hget⟩ := hA s1 hX1
      have hsz : arr.size < 2 ^ 64 := by omega
      have hcR := hc.right
      refine ev_cmpRA hcR.head hlen ?_
      rw [hd1]
      refine ev_jcc hcR.tail.head (fun hcc => ?_) (fun hcc => ?_)
      · refine herr _ (.inr ⟨j, hj, ?_⟩) (hX1.flags _)
        rw [interp_nc] at hcc
        simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz] at hcc
        omega
      · rw [interp_nc] at hcc
        simp only [decide_eq_false_iff_not, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz] at hcc
        have hjs : j.toNat < arr.size := by omega
        obtain ⟨_, B', hB', -, -⟩ := hA _ (hX1.flags (cmpFlags j.toBitVec (UInt64.ofNat arr.size).toBitVec))
        refine ev_movRA hcR.tail.tail.head hB ?_
        refine ev_movzxX hcR.tail.tail.tail.head (v := arr[j.toNat]) ?_ ?_
        · simp only [rget_set, ite_true, if_neg (Ne.symm htd), hd1]
          rw [← hget _ hjs]; congr 1
          apply BitVec.eq_of_toNat_eq
          simp [A, UInt64.toNat_ofNat_of_lt' (show B < 2 ^ 64 by omega)]
        · refine ev_congr (hv _ hjs _ hj (by simp [rget_set]) ?_) (by simp; omega)
          exact ((hX1.flags _).set ht _ _).set hd _ _

end

section
variable [Host] {G : Layout} (hG : G.Ok) {ctx : Ctx} {F : Nat} (hT : ctx.tab = G.tab)
  (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
include hG hT hTab

/-- A word array's descriptor in the table. -/
theorem arrW_plain {a : ArrId} (ha : a < G.tab.nw) {σ : St} {s : MachineData} (hI : Inv G ctx F σ s) :
    ArrW s (mb .r15 (ctx.tab.len64 a)) (mb .r15 (ctx.tab.base64 a)) (σ.mem.arr64 a) := by
  simp only [maxOff] at hTab
  have hw64 := G.tab.wpos_lt ha
  have hsz := hI.mem.size64 a ha
  have hend := hG.end64 a ha
  refine ⟨.inl ⟨_, _, rfl, ⟨by simp [Tab.len64]; lomega, by simp [hT, Tab.len64]; lomega⟩, ?_⟩,
    G.b64 a, .inl ⟨_, _, rfl, ⟨by simp [Tab.base64]; lomega, by simp [hT, Tab.base64]; lomega⟩, ?_⟩,
    by rw [hsz]; exact hend, fun j hj => hI.mem.get64 a ha j hj⟩
  · rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT, hsz]; exact hI.mem.len64 a ha
  · rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT]; exact hI.mem.base64 a ha

/-- A byte array's descriptor in the table. -/
theorem arrB_plain {a : ArrId} (ha : a < G.tab.nb) {σ : St} {s : MachineData} (hI : Inv G ctx F σ s) :
    ArrB s (mb .r15 (ctx.tab.len8 a)) (mb .r15 (ctx.tab.base8 a)) (σ.mem.arr8 a) := by
  simp only [maxOff] at hTab
  have hsz := hI.mem.size8 a ha
  have hend := hG.end8 a ha
  refine ⟨.inl ⟨_, _, rfl, ⟨by simp [Tab.len8]; lomega, by simp [hT, Tab.len8]; lomega⟩, ?_⟩,
    G.b8 a, .inl ⟨_, _, rfl, ⟨by simp [Tab.base8]; lomega, by simp [hT, Tab.base8]; lomega⟩, ?_⟩,
    by rw [hsz]; exact hend, fun j hj => hI.mem.get8 a ha j hj⟩
  · rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT, hsz]; exact hI.mem.len8 a ha
  · rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT]; exact hI.mem.base8 a ha

/-- A tiered word array's descriptor, the tier `u & 1` in register `R`. -/
theorem arrW_tier {a : ArrId} (ha : a < G.tab.wK) {σ : St} {s : MachineData} (hI : Inv G ctx F σ s)
    {R : Reg64} {u : Word} (hR : s.regs.get64 R = (u &&& 1).toBitVec) :
    ArrW s (tdesc R (ctx.tab.len64 a)) (tdesc R (ctx.tab.base64 a)) (σ.mem.arr64 (tierA a u)) := by
  simp only [maxOff] at hTab
  have ha' := (G.tab.wK_spec ha).2
  have hta : tierA a u < G.tab.nw := Nat.lt_of_le_of_lt (tierA_le a u) ha'
  have hw := G.tab.wpos_lt (Nat.lt_of_le_of_lt (Nat.le_add_right a tierOff) ha')
  have hb := tier_bit u
  have hoff := tier_off G.tab ha u
  have hD : ∀ d : Int, s.regs.r15.toNat + 8 * (s.regs.get64 R).toNat + d.toNat =
      G.T + 8 * (u &&& 1).toNat + d.toNat := by
    intro d; rw [hR, UInt64.toNat_toBitVec, hI.r15]
  have hsz := hI.mem.size64 _ hta
  have hend := hG.end64 _ hta
  refine ⟨.inr ⟨_, _, rfl, ⟨by simp [Tab.len64]; lomega, by simp [hT, Tab.len64]; lomega⟩, ?_⟩,
    G.b64 (tierA a u), .inr ⟨_, _, rfl, ⟨by simp [Tab.base64]; lomega, by simp [hT, Tab.base64]; lomega⟩, ?_⟩,
    by rw [hsz]; exact hend, fun j hj => hI.mem.get64 _ hta j hj⟩
  · rw [hD, show G.T + 8 * (u &&& 1).toNat + (ctx.tab.len64 a).toNat =
      G.T + (G.tab.len64 (tierA a u)).toNat by rw [hT]; omega, hsz]
    exact hI.mem.len64 _ hta
  · rw [hD, show G.T + 8 * (u &&& 1).toNat + (ctx.tab.base64 a).toNat =
      G.T + (G.tab.base64 (tierA a u)).toNat by rw [hT]; omega]
    exact hI.mem.base64 _ hta

end

end L.Compiler
