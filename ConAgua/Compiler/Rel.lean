module

public import ConAgua.Compiler.Step
public import ConAgua.Compiler.WF

@[expose] public section

/-!
# The simulation relation

`Layout` fixes where everything lives (ghost data: the proof quantifies over it, the code reads
it from the table). `MemRel G m d` relates L's memory `m` to the machine's data memory `d`:
the arrays hold `m`'s contents, the table holds the layout, and the stack region is mapped.
`Inv` adds the current frame.
-/

namespace L.Compiler

/-- Where the table, the arrays and the L stack are. -/
structure Layout where
  tab : Tab
  /-- The table address (`r15`). -/
  T : Nat
  b8 : Nat → Nat
  s8 : Nat → Nat
  b64 : Nat → Nat
  s64 : Nat → Nat
  /-- The L stack is `[lo, hi)`. -/
  lo : Nat
  hi : Nat
  /-- The number of entry arguments (stored at the end of the table). -/
  nargs : Nat

namespace Layout

variable (G : Layout)

/-- The bytes of the table that the code reads or writes: the descriptors, the constant data, the
result area, the global variables and the entry arguments. -/
def tabEnd : Nat := G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres +
  8 * G.tab.ng + 8 * G.nargs

/-- Where the global variables start. -/
def globStart : Nat := G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres

/-- Where global `g` is. -/
def globAddr (g : GVar) : Nat := G.globStart + 8 * g.id

/-- Where result `i ≥ maxRes` goes. -/
def resAddr (i : Nat) : Nat := G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * (i - maxRes)

def InTab (x : Nat) : Prop := G.T ≤ x ∧ x < G.tabEnd
/-- The descriptors and the constant data (the part of the table that `MemRel` describes). -/
def InDesc (x : Nat) : Prop := G.T ≤ x ∧ x < G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords
/-- The result area (inside the table). -/
def InRes (x : Nat) : Prop :=
  G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords ≤ x ∧
    x < G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres
/-- The global variables (inside the table). -/
def InGlob (x : Nat) : Prop := G.globStart ≤ x ∧ x < G.globStart + 8 * G.tab.ng
def InStack (x : Nat) : Prop := G.lo ≤ x ∧ x < G.hi
def In8 (a x : Nat) : Prop := G.b8 a ≤ x ∧ x < G.b8 a + G.s8 a
def In64 (a x : Nat) : Prop := G.b64 a ≤ x ∧ x < G.b64 a + 8 * G.s64 a
def InArr (x : Nat) : Prop := (∃ a < G.tab.nb, G.In8 a x) ∨ (∃ a < G.tab.nw, G.In64 a x)

/-- The regions are inside the address space and pairwise disjoint. -/
structure Ok : Prop where
  tab_end : G.tabEnd < 2 ^ 64
  hi_le : G.hi < 2 ^ 64
  lo_le : G.lo ≤ G.hi
  end8 : ∀ a < G.tab.nb, G.b8 a + G.s8 a < 2 ^ 64
  end64 : ∀ a < G.tab.nw, G.b64 a + 8 * G.s64 a < 2 ^ 64
  tab_stack : ∀ x, G.InTab x → ¬ G.InStack x
  tab_arr : ∀ x, G.InTab x → ¬ G.InArr x
  stack_arr : ∀ x, G.InStack x → ¬ G.InArr x
  arr8_disj : ∀ a < G.tab.nb, ∀ b < G.tab.nb, a ≠ b → ∀ x, G.In8 a x → ¬ G.In8 b x
  arr64_disj : ∀ a < G.tab.nw, ∀ b < G.tab.nw, a ≠ b → ∀ x, G.In64 a x → ¬ G.In64 b x
  arr8_64 : ∀ a < G.tab.nb, ∀ b < G.tab.nw, ∀ x, G.In8 a x → ¬ G.In64 b x

theorem InRes.tab {G : Layout} {x : Nat} (h : G.InRes x) : G.InTab x :=
  ⟨by have := h.1; omega, by have := h.2; simp only [Layout.tabEnd]; omega⟩

theorem InGlob.tab {G : Layout} {x : Nat} (h : G.InGlob x) : G.InTab x :=
  ⟨by have := h.1; simp only [Layout.globStart] at this; omega,
   by have := h.2; simp only [Layout.globStart] at this; simp only [Layout.tabEnd]; omega⟩

theorem InGlob.not_res {G : Layout} {x : Nat} (h : G.InGlob x) : ¬ G.InRes x := fun h' => by
  have := h.1; have := h'.2; simp only [Layout.globStart] at *; omega

theorem globAddr_toNat (G : Layout) (g : GVar) : G.T + (G.tab.globOff g).toNat = G.globAddr g := by
  simp only [Tab.globOff, Tab.globBase, Layout.globAddr, Layout.globStart]; omega

theorem inGlob_cell {G : Layout} {g : GVar} (hg : g.id < G.tab.ng) :
    ∀ k < 8, G.InGlob (G.globAddr g + k) := fun k hk => by
  simp only [Layout.InGlob, Layout.globAddr]; omega

theorem inRes_of {G : Layout} {x : Nat} (h1 : G.resAddr maxRes ≤ x) (h2 : x < G.resAddr G.tab.nres) :
    G.InRes x := by
  simp only [Layout.resAddr, Layout.InRes, Tab.nxres] at *; omega

end Layout

/-- L's memory `m` in the machine's data memory `d`. -/
structure MemRel (G : Layout) (m : Mem) (d : DataMem) : Prop where
  nb : m.bytes.size = G.tab.nb
  nw : m.words.size = G.tab.nw
  size8 : ∀ a < G.tab.nb, (m.arr8 a).size = G.s8 a
  size64 : ∀ a < G.tab.nw, (m.arr64 a).size = G.s64 a
  get8 : ∀ a < G.tab.nb, ∀ (i : Nat) (h : i < (m.arr8 a).size), d.get? (A (G.b8 a + i)) = some (m.arr8 a)[i]
  get64 : ∀ a < G.tab.nw, ∀ (i : Nat) (h : i < (m.arr64 a).size),
    rdW d (A (G.b64 a + 8 * i)) = some (m.arr64 a)[i]
  limit : rdW d (A (G.T + 8)) = some (UInt64.ofNat G.lo)
  base8 : ∀ a < G.tab.nb, rdW d (A (G.T + (G.tab.base8 a).toNat)) = some (UInt64.ofNat (G.b8 a))
  len8 : ∀ a < G.tab.nb, rdW d (A (G.T + (G.tab.len8 a).toNat)) = some (UInt64.ofNat (G.s8 a))
  base64 : ∀ a < G.tab.nw, rdW d (A (G.T + (G.tab.base64 a).toNat)) = some (UInt64.ofNat (G.b64 a))
  len64 : ∀ a < G.tab.nw, rdW d (A (G.T + (G.tab.len64 a).toNat)) = some (UInt64.ofNat (G.s64 a))
  rom : ∀ (i : Nat) (h : i < G.tab.rom.length),
    d.get? (A (G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + i)) = some G.tab.rom[i]
  stack : ∀ x, G.InStack x → (d.get? (A x)).isSome
  res : ∀ x, G.InRes x → (d.get? (A x)).isSome
  /-- The global variables. -/
  glob : ∀ g : GVar, g.id < G.tab.ng → rdW d (A (G.globAddr g)) = some (m.glob g)

theorem mem_allocRegs {r : Reg64} : r ∈ allocRegs ↔
    r = .rdi ∨ r = .r8 ∨ r = .r9 ∨ r = .r10 ∨ r = .r11 ∨ r = .rsi ∨ r = .rbx ∨ r = .r12 ∨ r = .r13 := by
  simp [allocRegs, argRegs]

theorem argRegs_sub {r : Reg64} (h : r ∈ argRegs) : r ∈ allocRegs := by
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [allocRegs]

/-- The registers of `allocRegs` are none of `rax`, `rcx`, `rdx` (scratch), `rsp`, `rbp`, `r14`,
`r15`. -/
theorem allocRegs_ne {r : Reg64} (h : r ∈ allocRegs) :
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsp ∧ r ≠ .rbp ∧ r ≠ .r14 ∧ r ≠ .r15 := by
  rw [mem_allocRegs] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The allocation of `ctx` is one the proof can use (`allocOk`, checked by `compileFn`). -/
structure AllocOk (ctx : Ctx) : Prop where
  reg : ∀ x r, ctx.alloc.lookup x = some r → r ∈ allocRegs
  inj : ∀ x y r, ctx.alloc.lookup x = some r → ctx.alloc.lookup y = some r → x = y
  leaf : ctx.leaf = false → ctx.alloc = []
  /-- Only a leaf has a tier local (lane tiercost). -/
  tleaf : ctx.leaf = false → ctx.treg = none
  /-- The tier local stays in its frame slot. -/
  talloc : ∀ x, ctx.treg = some x → ctx.alloc.lookup x = none
  /-- No local is in `rsi`, which holds the tier. -/
  trsi : ctx.treg ≠ none → ∀ y, ctx.alloc.lookup y ≠ some .rsi

theorem AllocOk.ne {ctx : Ctx} (h : AllocOk ctx) {x : Var} {r : Reg64} (hx : ctx.alloc.lookup x = some r) :
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsp ∧ r ≠ .rbp ∧ r ≠ .r14 ∧ r ≠ .r15 :=
  allocRegs_ne (h.reg x r hx)

/-- The machine runs a body of a function with context `ctx` (its locals: `ctx.nl`, those in
registers: `ctx.alloc`) and an `F`-word frame, in L state `σ`. A local in a register is there;
the others are in their frame slots. -/
structure Inv (G : Layout) (ctx : Ctx) (F : Nat) (σ : St) (s : MachineData) : Prop where
  r15 : s.regs.r15.toNat = G.T
  lo : G.lo ≤ s.regs.rsp.toNat
  /-- The next call's return address fits below the frame, and so does the frame of a callee
  without a stack check (`Ctx.need`; a leaf has no calls, and maybe no frame). -/
  lo8 : ctx.leaf = false → G.lo + 8 + 8 * ctx.need ≤ s.regs.rsp.toNat
  hi : s.regs.rsp.toNat + 8 * F + 8 ≤ G.hi
  slot : ∀ x < ctx.nl, ctx.alloc.lookup x = none → x < F
  al : AllocOk ctx
  reg : ∀ x < ctx.nl, ∀ r, ctx.alloc.lookup x = some r → s.regs.get64 r = (σ.loc x).toBitVec
  frame : ∀ x < ctx.nl, ctx.alloc.lookup x = none → rdW s.dmem (A (s.regs.rsp.toNat + 8 * x)) = some (σ.loc x)
  mem : MemRel G σ.mem s.dmem
  /-- The tier local's tier is in `rsi` (lane tiercost). -/
  tr : ∀ x, ctx.treg = some x → s.regs.rsi = σ.loc x &&& 1

/-- Result register `i`. -/
def rres (R : Reg64s) : Nat → Word
  | 0 => R.rax | 1 => R.rdi | 2 => R.r8 | 3 => R.r9 | 4 => R.r10 | _ => R.r11

/-- Of the first `n` results, those in registers hold the values `vs` (`0` past the end of `vs`). -/
def ResRel (n : Nat) (vs : List Word) (R : Reg64s) : Prop := ∀ i < n, i < maxRes → rres R i = vs.getD i 0

/-- Of the first `n` results, those past the registers are in the result area. -/
def ResMem (G : Layout) (n : Nat) (vs : List Word) (d : DataMem) : Prop :=
  ∀ i, maxRes ≤ i → i < n → rdW d (A (G.resAddr i)) = some (vs.getD i 0)

/-- The results `vs` of a call, at most `n` of them, in the registers and the result area. -/
def ResOut (G : Layout) (n : Nat) (vs : List Word) (s : MachineData) : Prop :=
  ResRel n vs s.regs ∧ ResMem G n vs s.dmem ∧ vs.length ≤ n

theorem rres_set64_resReg (R : Reg64s) {i j : Nat} (hi : i < maxRes) (hj : j < maxRes)
    (v : BitVec 64) : rres (R.set64 (resReg i) v) j = if j = i then UInt64.ofBitVec v else rres R j := by
  simp only [maxRes] at hi hj
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The registers that are not result registers. -/
theorem rres_set64 (R : Reg64s) {r : Reg64}
    (hr : r = .rcx ∨ r = .rdx ∨ r = .rsi ∨ r = .rsp ∨ r = .rbp ∨ r = .r14 ∨ r = .r15)
    (v : BitVec 64) (j : Nat) : rres (R.set64 r v) j = rres R j := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (match j with
     | 0 | 1 | 2 | 3 | 4 | _ + 5 => rfl)

theorem ResRel.set64 {n : Nat} {vs : List Word} {R : Reg64s} (h : ResRel n vs R) {r : Reg64}
    (hr : r = .rcx ∨ r = .rdx ∨ r = .rsi ∨ r = .rsp ∨ r = .rbp ∨ r = .r14 ∨ r = .r15)
    (v : BitVec 64) : ResRel n vs (R.set64 r v) :=
  fun i hi hm => by rw [rres_set64 R hr]; exact h i hi hm

theorem ResRel.congr {n : Nat} {vs : List Word} {R R' : Reg64s} (h : ResRel n vs R)
    (h0 : R'.rax = R.rax) (h1 : R'.rdi = R.rdi) (h2 : R'.r8 = R.r8) (h3 : R'.r9 = R.r9)
    (h4 : R'.r10 = R.r10) (h5 : R'.r11 = R.r11) : ResRel n vs R' := fun i hi hm => by
  rw [← h i hi hm]
  match i with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | 4 => exact h4
  | _ + 5 => exact h5

/-- `rsi` is unchanged (states built by writes of other registers, the flags or memory). -/
macro "bx_keep" : tactic => `(tactic| (intro _; first | rfl | (simp [Reg64s.set64]; done) | simp_all [Reg64s.set64]))

/-- `rsi` from its 64-bit view. -/
theorem rsi_of_get64 {R R' : Reg64s} (h : R'.get64 .rsi = R.get64 .rsi) : R'.rsi = R.rsi :=
  UInt64.toBitVec_inj.mp h

/-- `Inv` only reads the locals, the allocation, the leaf flag, the tier local and the need of the
context. -/
theorem Inv.ctx {G : Layout} {ctx ctx' : Ctx} {F : Nat} {σ : St} {s : MachineData} (hI : Inv G ctx F σ s)
    (hn : ctx'.nl = ctx.nl) (ha : ctx'.alloc = ctx.alloc) (hl : ctx'.leaf = ctx.leaf)
    (ht : ctx'.treg = ctx.treg := by rfl) (hd : ctx'.need = ctx.need := by rfl) : Inv G ctx' F σ s where
  r15 := hI.r15
  lo := hI.lo
  lo8 := hl ▸ hd ▸ hI.lo8
  hi := hI.hi
  slot := hn ▸ ha ▸ hI.slot
  al := ⟨ha ▸ hI.al.reg, ha ▸ hI.al.inj, fun h => ha ▸ hI.al.leaf (hl ▸ h), fun h => ht ▸ hI.al.tleaf (hl ▸ h), fun x hx => ha ▸ hI.al.talloc x (ht ▸ hx), fun h => ha ▸ hI.al.trsi (ht ▸ h)⟩
  reg := hn ▸ ha ▸ hI.reg
  frame := hn ▸ ha ▸ hI.frame
  mem := hI.mem
  tr := ht ▸ hI.tr

/-- `Inv` for a new L state with the same locals, from the same registers and frame slots. -/
theorem Inv.congr' {G : Layout} {ctx : Ctx} {F : Nat} {σ σ' : St} {s s' : MachineData} (hI : Inv G ctx F σ s)
    (hloc : σ'.loc = σ.loc) (hsp : s'.regs.rsp = s.regs.rsp) (h15 : s'.regs.r15 = s.regs.r15)
    (hR : ∀ x r, ctx.alloc.lookup x = some r → s'.regs.get64 r = s.regs.get64 r)
    (hfr : ∀ x < ctx.nl, ctx.alloc.lookup x = none →
      rdW s'.dmem (A (s.regs.rsp.toNat + 8 * x)) = rdW s.dmem (A (s.regs.rsp.toNat + 8 * x)))
    (hm : MemRel G σ'.mem s'.dmem) (hbx : ctx.treg ≠ none → s'.regs.rsi = s.regs.rsi := by bx_keep) : Inv G ctx F σ' s' where
  r15 := h15 ▸ hI.r15
  lo := hsp ▸ hI.lo
  lo8 := hsp ▸ hI.lo8
  hi := hsp ▸ hI.hi
  slot := hI.slot
  al := hI.al
  reg := fun x hx r hr => by rw [hR x r hr, hloc]; exact hI.reg x hx r hr
  frame := fun x hx hn => by rw [hsp, hfr x hx hn, hloc]; exact hI.frame x hx hn
  mem := hm
  tr := fun x hx => by rw [hbx (by simp [hx]), hloc]; exact hI.tr x hx

theorem Inv.congr {G : Layout} {ctx : Ctx} {F : Nat} {σ σ' : St} {s s' : MachineData} (hI : Inv G ctx F σ s)
    (hloc : σ'.loc = σ.loc) (hsp : s'.regs.rsp = s.regs.rsp) (h15 : s'.regs.r15 = s.regs.r15)
    (hR : ∀ r ∈ allocRegs, s'.regs.get64 r = s.regs.get64 r)
    (hfr : ∀ x < ctx.nl, ctx.alloc.lookup x = none →
      rdW s'.dmem (A (s.regs.rsp.toNat + 8 * x)) = rdW s.dmem (A (s.regs.rsp.toNat + 8 * x)))
    (hm : MemRel G σ'.mem s'.dmem) (hbx : ctx.treg ≠ none → s'.regs.rsi = s.regs.rsi := by bx_keep) : Inv G ctx F σ' s' :=
  hI.congr' hloc hsp h15 (fun x r h => hR r (hI.al.reg x r h)) hfr hm hbx

/-- `Inv` after a change of the scratch registers and the flags. -/
theorem Inv.of_regs {G : Layout} {ctx : Ctx} {F : Nat} {σ : St} {s s' : MachineData} (hI : Inv G ctx F σ s)
    (hd : s'.dmem = s.dmem) (hsp : s'.regs.rsp = s.regs.rsp) (h15 : s'.regs.r15 = s.regs.r15)
    (hR : ∀ r ∈ allocRegs, s'.regs.get64 r = s.regs.get64 r)
    (hbx : ctx.treg ≠ none → s'.regs.rsi = s.regs.rsi := by bx_keep) : Inv G ctx F σ s' :=
  hI.congr rfl hsp h15 hR (fun x _ _ => by rw [hd]) (hd ▸ hI.mem) hbx

/-- The registers of `allocRegs` agree, for states built by writes of other registers. -/
macro "alloc_keep" : tactic => `(tactic| (intro r hr; have hne := allocRegs_ne hr; first | (simp only [rget_set, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2.1, hne.2.2.2.2.2.2, ite_false, if_false]; done) | (cases r <;> first | exact absurd rfl hne.1 | exact absurd rfl hne.2.1 | exact absurd rfl hne.2.2.1 | rfl)))

/-- Reading a register after a write. -/
theorem rget_set (R : Reg64s) (r r' : Reg64) (v : BitVec 64) :
    (R.set64 r v).get64 r' = if r' = r then v else R.get64 r' := by
  cases r <;> cases r' <;> simp [Reg64s.set64, Reg64s.get64]

/-- `Inv` of a function that keeps no locals in registers, after a change of registers. -/
theorem Inv.of_regs0 {G : Layout} {ctx : Ctx} {F : Nat} {σ : St} {s s' : MachineData} (hI : Inv G ctx F σ s)
    (hal : ctx.alloc = []) (hd : s'.dmem = s.dmem) (hsp : s'.regs.rsp = s.regs.rsp)
    (h15 : s'.regs.r15 = s.regs.r15) (hbx : ctx.treg ≠ none → s'.regs.rsi = s.regs.rsi := by bx_keep) : Inv G ctx F σ s' :=
  hI.congr' rfl hsp h15 (fun x r h => by simp [hal] at h) (fun x _ _ => by rw [hd]) (hd ▸ hI.mem) hbx

/-- The registers but `rax`, `rcx`, `rdx` after a write of one of them. -/
theorem get64_set64_scratch {R : Reg64s} {r : Reg64} (hr : r = .rax ∨ r = .rcx ∨ r = .rdx) (v : BitVec 64)
    (r' : Reg64) (h1 : r' ≠ .rax) (h2 : r' ≠ .rcx) (h3 : r' ≠ .rdx) : (R.set64 r v).get64 r' = R.get64 r' := by
  rcases hr with rfl | rfl | rfl <;> cases r' <;> simp_all [Reg64s.set64, Reg64s.get64]

/-- `d'` differs from `d` at most in the bytes `[a, b)`, and has every byte `d` has. -/
structure Only (a b : Nat) (d d' : DataMem) : Prop where
  grows : ∀ y, (d.get? y).isSome → (d'.get? y).isSome
  same : ∀ x < 2 ^ 64, (x < a ∨ b ≤ x) → d'.get? (A x) = d.get? (A x)

theorem Only.refl (a b : Nat) (d : DataMem) : Only a b d d := ⟨fun _ h => h, fun _ _ _ => rfl⟩

theorem Only.trans {a b a' b' : Nat} {d d' d'' : DataMem} (h : Only a b d d') (h' : Only a' b' d' d'')
    (ha : a ≤ a') (hb : b' ≤ b) : Only a b d d'' :=
  ⟨fun y hy => h'.grows y (h.grows y hy), fun x hx hab => by
    rw [h'.same x hx (by omega), h.same x hx hab]⟩

/-- Two changes, inside `[a, b)` together. -/
theorem Only.union {a b a₁ b₁ a₂ b₂ : Nat} {d d' d'' : DataMem} (h : Only a₁ b₁ d d') (h' : Only a₂ b₂ d' d'')
    (h1 : a ≤ a₁) (h2 : a ≤ a₂) (h3 : b₁ ≤ b) (h4 : b₂ ≤ b) : Only a b d d'' :=
  ⟨fun y hy => h'.grows y (h.grows y hy), fun x hx hab => by
    rw [h'.same x hx (by omega), h.same x hx (by omega)]⟩

theorem Only.mono {a b a' b' : Nat} {d d' : DataMem} (h : Only a b d d') (ha : a' ≤ a) (hb : b ≤ b') :
    Only a' b' d d' :=
  ⟨h.grows, fun x hx hab => h.same x hx (by omega)⟩

theorem Only.wrW {x : Nat} {d : DataMem} {v : BitVec 64} (hx : x + 8 ≤ 2 ^ 64) :
    Only x (x + 8) d (wrW d (A x) v) :=
  ⟨fun _ h => isSome_get?_storeInt h, fun _ hy h => get?_wrW_A hx hy (by omega)⟩

/-- A word inside `[a, b)` survives a change outside it. -/
theorem Only.rdW_eq {a b x : Nat} {d d' : DataMem} (h : Only a b d d') (hx : x + 8 ≤ 2 ^ 64)
    (hout : x + 8 ≤ a ∨ b ≤ x) : rdW d' (A x) = rdW d (A x) :=
  rdW_congr fun j hj => by
    rw [A_add]; exact h.same _ (by omega) (by omega)


/-- Two 8-byte cells in disjoint sets of bytes do not overlap. -/
theorem cell_disj {x y : Nat} {P Q : Nat → Prop} (hP : ∀ k < 8, P (x + k)) (hQ : ∀ k < 8, Q (y + k))
    (h : ∀ t, P t → ¬ Q t) : y + 8 ≤ x ∨ x + 8 ≤ y := by
  refine Classical.byContradiction fun hc => ?_
  simp only [not_or, Nat.not_le] at hc
  by_cases hxy : x ≤ y
  · exact h y (by have := hP (y - x) (by omega); rwa [show x + (y - x) = y by omega] at this)
      (by have := hQ 0 (by omega); simpa using this)
  · exact h x (by have := hP 0 (by omega); simpa using this)
      (by have := hQ (x - y) (by omega); rwa [show y + (x - y) = x by omega] at this)

/-- A byte outside a set of bytes is not in an 8-byte cell inside it. -/
theorem byte_cell_disj {x y : Nat} {P Q : Nat → Prop} (hP : ∀ k < 8, P (x + k)) (hQ : Q y)
    (h : ∀ t, P t → ¬ Q t) : y < x ∨ x + 8 ≤ y := by
  refine Classical.byContradiction fun hc => ?_
  simp only [not_or, Nat.not_lt] at hc
  exact h y (by have := hP (y - x) (by omega); rwa [show x + (y - x) = y by omega] at this) hQ

/-! ## Changes inside the stack leave the memory relation alone -/

section
variable {G : Layout} (hG : G.Ok)
include hG

theorem Layout.Ok.notStack_of_arr {x : Nat} (h : G.InArr x) : ¬ G.InStack x :=
  fun hs => hG.stack_arr x hs h

theorem Layout.Ok.notStack_of_arr' {x : Nat} (h : G.InStack x) : ¬ G.InArr x :=
  fun ha => hG.stack_arr x h ha

theorem Layout.Ok.notStack_of_tab {x : Nat} (h : G.InTab x) : ¬ G.InStack x :=
  hG.tab_stack x h

/-- A table word at offset `off` (within the table) survives a change in the stack. -/
theorem Only.rdW_tab {a b : Nat} {d d' : DataMem} (h : Only a b d d')
    (hab : ∀ x, a ≤ x → x < b → ¬ G.InDesc x ∧ ¬ G.InArr x)
    {off : Nat} (hoff : 8 ≤ off + 8) (hend : G.T + off + 8 ≤ G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords) :
    rdW d' (A (G.T + off)) = rdW d (A (G.T + off)) :=
  rdW_congr fun j hj => by
    rw [A_add]
    refine h.same _ (by have := hG.tab_end; simp only [Layout.tabEnd] at this; omega) ?_
    refine Classical.byContradiction fun hc => ?_
    simp only [not_or, Nat.not_lt] at hc
    exact (hab (G.T + off + j) (by omega) (by omega)).1 ⟨by omega, by omega⟩

/-- A change outside the descriptors, the constant data and the arrays, to a memory with the same
arrays, keeps the memory relation if the global variables hold the new memory's. -/
theorem MemRel.onlyG {m m' : Mem} {d d' : DataMem} (hm : MemRel G m d) (hb : m'.bytes = m.bytes)
    (hw : m'.words = m.words) {a b : Nat} (h : Only a b d d')
    (hab : ∀ x, a ≤ x → x < b → ¬ G.InDesc x ∧ ¬ G.InArr x)
    (hglob : ∀ g : GVar, g.id < G.tab.ng → rdW d' (A (G.globAddr g)) = some (m'.glob g)) :
    MemRel G m' d' := by
  obtain ⟨b₁, w₁, g₁⟩ := m
  obtain ⟨b₂, w₂, g₂⟩ := m'
  cases hb; cases hw
  exact {
    nb := hm.nb
    nw := hm.nw
    size8 := hm.size8
    size64 := hm.size64
    get8 := fun c hc i hi => by
      replace hi : i < (Mem.arr8 ⟨b₁, w₁, g₁⟩ c).size := hi
      show _ = some ((Mem.arr8 ⟨b₁, w₁, g₁⟩ c)[i]'hi)
      have hs := hm.size8 c hc
      have he := hG.end8 c hc
      rw [h.same _ (by omega) ?_, hm.get8 c hc i hi]
      refine Classical.byContradiction fun hx => ?_
      simp only [not_or, Nat.not_lt] at hx
      exact (hab (G.b8 c + i) (by omega) (by omega)).2 (Or.inl ⟨c, hc, by omega, by omega⟩)
    get64 := fun c hc i hi => by
      replace hi : i < (Mem.arr64 ⟨b₁, w₁, g₁⟩ c).size := hi
      show _ = some ((Mem.arr64 ⟨b₁, w₁, g₁⟩ c)[i]'hi)
      have hs := hm.size64 c hc
      have he := hG.end64 c hc
      rw [← hm.get64 c hc i hi]
      refine rdW_congr fun j hj => ?_
      rw [A_add]
      refine h.same _ (by omega) ?_
      refine Classical.byContradiction fun hx => ?_
      simp only [not_or, Nat.not_lt] at hx
      exact (hab (G.b64 c + 8 * i + j) (by omega) (by omega)).2 (Or.inr ⟨c, hc, by omega, by omega⟩)
    limit := by
      rw [h.rdW_tab hG hab (by omega) (by omega)]; exact hm.limit
    base8 := fun c hc => by
      rw [h.rdW_tab hG hab (by omega) (by simp only [Tab.base8]; omega)]; exact hm.base8 c hc
    len8 := fun c hc => by
      rw [h.rdW_tab hG hab (by omega) (by simp only [Tab.len8]; omega)]; exact hm.len8 c hc
    base64 := fun c hc => by
      have := G.tab.wpos_lt hc
      rw [h.rdW_tab hG hab (by omega) (by simp only [Tab.base64]; omega)]; exact hm.base64 c hc
    len64 := fun c hc => by
      have := G.tab.wpos_lt hc
      rw [h.rdW_tab hG hab (by omega) (by simp only [Tab.len64]; omega)]; exact hm.len64 c hc
    rom := fun i hi => by
      have hw : G.tab.rom.length ≤ 8 * G.tab.romWords := G.tab.rom_length_le
      have := hG.tab_end
      simp only [Layout.tabEnd] at this
      rw [h.same _ (by omega) ?_, hm.rom i hi]
      refine Classical.byContradiction fun hc => ?_
      simp only [not_or, Nat.not_lt] at hc
      exact (hab (G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + i) (by omega) (by omega)).1
        ⟨by omega, by omega⟩
    stack := fun x hx => h.grows _ (hm.stack x hx)
    res := fun x hx => h.grows _ (hm.res x hx)
    glob := hglob }

/-- A change outside the descriptors, the constant data, the arrays and the global variables
keeps the memory relation. -/
theorem MemRel.onlyD {m : Mem} {d d' : DataMem} (hm : MemRel G m d) {a b : Nat} (h : Only a b d d')
    (hab : ∀ x, a ≤ x → x < b → ¬ G.InDesc x ∧ ¬ G.InArr x)
    (hglob : ∀ x, a ≤ x → x < b → ¬ G.InGlob x) : MemRel G m d' :=
  hm.onlyG hG rfl rfl h hab fun g hg => by
    have := hG.tab_end
    have hc := Layout.inGlob_cell (G := G) hg
    have hT : G.globAddr g + 8 ≤ G.tabEnd := by
      simp only [Layout.tabEnd, Layout.globAddr, Layout.globStart]; omega
    rw [← hm.glob g hg]
    refine rdW_congr fun j hj => ?_
    rw [A_add]
    refine h.same _ (by omega) ?_
    refine Classical.byContradiction fun hx => ?_
    simp only [not_or, Nat.not_lt] at hx
    exact hglob _ (by omega) (by omega) (hc j hj)

/-- The memory relation after a write of a global variable. -/
theorem MemRel.storeG {m : Mem} {d : DataMem} (hm : MemRel G m d) {g : GVar} (hg : g.id < G.tab.ng)
    (v : Word) : MemRel G (m.setG g v) (wrW d (A (G.globAddr g)) v.toBitVec) := by
  have := hG.tab_end
  have hc := Layout.inGlob_cell (G := G) hg
  have hT : G.globAddr g + 8 ≤ G.tabEnd := by
    simp only [Layout.tabEnd, Layout.globAddr, Layout.globStart]; omega
  refine hm.onlyG hG rfl rfl (Only.wrW (by omega)) (fun x h1 h2 => ⟨fun hd => ?_, fun ha => ?_⟩)
    fun g' hg' => ?_
  · have := hd.2; simp only [Layout.globAddr, Layout.globStart] at h1; omega
  · have hx := hc (x - G.globAddr g) (by omega)
    rw [show G.globAddr g + (x - G.globAddr g) = x by omega] at hx
    exact hG.tab_arr x hx.tab ha
  · by_cases e : g' = g
    · subst e; rw [rdW_wrW_same]; simp [Mem.setG]
    · have hne : g'.id ≠ g.id := fun h' => e (by cases g; cases g'; simp_all)
      have hT' : G.globAddr g' + 8 ≤ G.tabEnd := by
        simp only [Layout.tabEnd, Layout.globAddr, Layout.globStart]; omega
      rw [rdW_wrW_A (by omega) (by omega) (by simp only [Layout.globAddr]; omega), hm.glob g' hg']
      simp [Mem.setG, e]

/-- A change outside the table and the arrays keeps the memory relation. -/
theorem MemRel.only' {m : Mem} {d d' : DataMem} (hm : MemRel G m d) {a b : Nat} (h : Only a b d d')
    (hab : ∀ x, a ≤ x → x < b → ¬ G.InTab x ∧ ¬ G.InArr x) : MemRel G m d' :=
  hm.onlyD hG h (fun x h1 h2 => ⟨fun ⟨u, v⟩ => (hab x h1 h2).1 ⟨u, by simp only [Layout.tabEnd]; omega⟩,
    (hab x h1 h2).2⟩) fun x h1 h2 hg => (hab x h1 h2).1 hg.tab

theorem Layout.Ok.notStack_of_res {x : Nat} (h : G.InRes x) : ¬ G.InStack x := hG.tab_stack x h.tab
theorem Layout.Ok.notArr_of_res {x : Nat} (h : G.InRes x) : ¬ G.InArr x := hG.tab_arr x h.tab

/-- A result cell and a stack cell do not overlap. -/
theorem Layout.Ok.res_stack_disj {x y : Nat} (hx : ∀ t < 8, G.InRes (x + t)) (hy : ∀ t < 8, G.InStack (y + t)) :
    y + 8 ≤ x ∨ x + 8 ≤ y :=
  cell_disj hx hy fun t h1 h2 => hG.notStack_of_res h1 h2

/-- A change inside the result area keeps the memory relation. -/
theorem MemRel.only_res {m : Mem} {d d' : DataMem} (hm : MemRel G m d) {a b : Nat} (h : Only a b d d')
    (hab : ∀ x, a ≤ x → x < b → G.InRes x) : MemRel G m d' :=
  hm.onlyD hG h (fun x h1 h2 => ⟨fun ⟨_, v⟩ => by have := (hab x h1 h2).1; omega,
    hG.notArr_of_res (hab x h1 h2)⟩) fun x h1 h2 hg => hg.not_res (hab x h1 h2)

/-- A change inside the stack keeps the memory relation. -/
theorem MemRel.only {m : Mem} {d d' : DataMem} (hm : MemRel G m d) {a b : Nat} (h : Only a b d d')
    (hab : ∀ x, a ≤ x → x < b → G.InStack x) : MemRel G m d' :=
  hm.only' hG h fun x h1 h2 => ⟨fun ht => hG.notStack_of_tab ht (hab x h1 h2),
    fun ha => hG.notStack_of_arr ha (hab x h1 h2)⟩

/-- A change among the temporaries keeps `Inv`. -/
theorem Inv.only {ctx : Ctx} {F : Nat} {σ : St} {s s' : MachineData} (hI : Inv G ctx F σ s)
    (h : Only (s.regs.rsp.toNat + 8 * ctx.nl) (s.regs.rsp.toNat + 8 * F) s.dmem s'.dmem)
    (hsp : s'.regs.rsp = s.regs.rsp) (h15 : s'.regs.r15 = s.regs.r15)
    (hR : ∀ r ∈ allocRegs, s'.regs.get64 r = s.regs.get64 r)
    (hbx : ctx.treg ≠ none → s'.regs.rsi = s.regs.rsi := by bx_keep) : Inv G ctx F σ s' :=
  hI.congr rfl hsp h15 hR (fun x hx hn => by
      have := hI.hi; have := hG.hi_le; have := hI.slot x hx hn
      exact h.rdW_eq (by omega) (by omega))
    (hI.mem.only hG h fun x h1 h2 => ⟨by have := hI.lo; omega, by have := hI.hi; omega⟩) hbx

/-- A change inside the result area keeps `Inv`. -/
theorem Inv.only_res {ctx : Ctx} {F : Nat} {σ : St} {s s' : MachineData} (hI : Inv G ctx F σ s) {a b : Nat}
    (h : Only a b s.dmem s'.dmem) (hab : ∀ x, a ≤ x → x < b → G.InRes x)
    (hsp : s'.regs.rsp = s.regs.rsp) (h15 : s'.regs.r15 = s.regs.r15)
    (hR : ∀ r ∈ allocRegs, s'.regs.get64 r = s.regs.get64 r)
    (hbx : ctx.treg ≠ none → s'.regs.rsi = s.regs.rsi := by bx_keep) : Inv G ctx F σ s' :=
  hI.congr rfl hsp h15 hR (fun x hx hn => by
      have := hI.hi; have := hG.hi_le; have := hI.slot x hx hn; have := hI.lo
      refine rdW_congr fun j hj => ?_
      rw [A_add]
      refine h.same _ (by omega) (Classical.byContradiction fun hc => ?_)
      simp only [not_or, Nat.not_lt, Nat.not_le] at hc
      exact hG.notStack_of_res (hab _ hc.1 hc.2) ⟨by omega, by omega⟩)
    (hI.mem.only_res hG h hab) hbx

end
end L.Compiler
