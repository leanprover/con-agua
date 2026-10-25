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

end L.Compiler
