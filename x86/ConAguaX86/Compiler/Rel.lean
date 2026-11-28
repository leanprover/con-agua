module

public import ConAguaX86.Compiler.Step
public import ConAgua.Compiler.WF
import Kraken.X64.Registers

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
  /-- The base address of the array at descriptor position `p`. -/
  b : Nat → Nat
  /-- Its length: bytes at a byte position, words at a word position (`Tab.wd`). -/
  s : Nat → Nat
  /-- The L stack is `[lo, hi)`. -/
  lo : Nat
  hi : Nat
  /-- The number of entry arguments (stored at the end of the table). -/
  nargs : Nat

namespace Layout

variable (G : Layout)

/-- The bytes of the table that the code reads or writes: the descriptors, the constant data, the
result area, the global variables and the entry arguments. -/
def tabEnd : Nat := G.T + 16 + 24 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres +
  8 * G.tab.ng + 8 * G.nargs

/-- Where the global variables start. -/
def globStart : Nat := G.T + 16 + 24 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres

/-- Where global `g` is. -/
def globAddr (g : GVar) : Nat := G.globStart + 8 * g.id

/-- Where result `i ≥ maxRes` goes. -/
def resAddr (i : Nat) : Nat := G.T + 16 + 24 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * (i - maxRes)

def InTab (x : Nat) : Prop := G.T ≤ x ∧ x < G.tabEnd
/-- The descriptors and the constant data (the part of the table that `MemRel` describes). -/
def InDesc (x : Nat) : Prop := G.T ≤ x ∧ x < G.T + 16 + 24 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords
/-- The result area (inside the table). -/
def InRes (x : Nat) : Prop :=
  G.T + 16 + 24 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords ≤ x ∧
    x < G.T + 16 + 24 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres
/-- The global variables (inside the table). -/
def InGlob (x : Nat) : Prop := G.globStart ≤ x ∧ x < G.globStart + 8 * G.tab.ng
def InStack (x : Nat) : Prop := G.lo ≤ x ∧ x < G.hi
/-- Byte `x` is in the region of position `p`: `s p` elements of the position's width. -/
def In (p x : Nat) : Prop := G.b p ≤ x ∧ x < G.b p + G.tab.wd p * G.s p
/-- The region of position `p`, read as bytes (`In` at a byte position). -/
def In8 (p x : Nat) : Prop := G.b p ≤ x ∧ x < G.b p + G.s p
/-- The region of position `p`, read as words (`In` at a word position). -/
def In64 (p x : Nat) : Prop := G.b p ≤ x ∧ x < G.b p + 8 * G.s p
def InArr (x : Nat) : Prop := ∃ p < G.tab.nb + G.tab.nw, G.In p x

/-- The regions are inside the address space and pairwise disjoint, every word array the program
may name has at least its minimum length (`Tab.min64`, the hint the code generator drops
constant-index bounds checks by), and the table-relative array (`Tab.tbl64`) starts where the
code addresses it, at `T + c`. -/
structure Ok : Prop where
  tab_end : G.tabEnd < 2 ^ 64
  hi_le : G.hi < 2 ^ 64
  lo_le : G.lo ≤ G.hi
  end_ : ∀ p < G.tab.nb + G.tab.nw, G.b p + G.tab.wd p * G.s p < 2 ^ 64
  tab_stack : ∀ x, G.InTab x → ¬ G.InStack x
  tab_arr : ∀ x, G.InTab x → ¬ G.InArr x
  stack_arr : ∀ x, G.InStack x → ¬ G.InArr x
  disj : ∀ p < G.tab.nb + G.tab.nw, ∀ q < G.tab.nb + G.tab.nw, p ≠ q → ∀ x, G.In p x → ¬ G.In q x
  min64 : ∀ s, G.tab.dom64 s = true → G.tab.min64 s ≤ G.s (G.tab.pos64 s)
  tbl64 : ∀ s c, G.tab.dom64 s = true → G.tab.tbl64 s = some c → G.b (G.tab.pos64 s) = G.T + c

section
variable {G : Layout} {p x : Nat}

theorem wd_byte (hp : p < G.tab.nb) : G.tab.wd p = 1 := by simp [Tab.wd, hp]
theorem wd_word (hp : G.tab.nb ≤ p) : G.tab.wd p = 8 := by simp [Tab.wd, show ¬ p < G.tab.nb by omega]
theorem In.of8 (hp : p < G.tab.nb) (h : G.In8 p x) : G.In p x := by
  unfold In; unfold In8 at h; rw [wd_byte hp]; omega
theorem In.of64 (hp : G.tab.nb ≤ p) (h : G.In64 p x) : G.In p x := by
  unfold In; unfold In64 at h; rw [wd_word hp]; omega
theorem In.to8 (hp : p < G.tab.nb) (h : G.In p x) : G.In8 p x := by
  unfold In at h; unfold In8; rw [wd_byte hp] at h; omega
theorem In.to64 (hp : G.tab.nb ≤ p) (h : G.In p x) : G.In64 p x := by
  unfold In at h; unfold In64; rw [wd_word hp] at h; omega
theorem InArr.of8 (hp : p < G.tab.nb) (h : G.In8 p x) : G.InArr x := ⟨p, by omega, In.of8 hp h⟩
theorem InArr.of64 (hp : G.tab.nb ≤ p ∧ p < G.tab.nb + G.tab.nw) (h : G.In64 p x) : G.InArr x :=
  ⟨p, hp.2, In.of64 hp.1 h⟩

/-- A byte region ends in the address space. -/
theorem Ok.end8 (hG : G.Ok) : ∀ p < G.tab.nb, G.b p + G.s p < 2 ^ 64 := fun p hp => by
  have := hG.end_ p (by omega); rw [wd_byte hp] at this; omega
/-- A word region ends in the address space. -/
theorem Ok.end64 (hG : G.Ok) : ∀ p, G.tab.nb ≤ p ∧ p < G.tab.nb + G.tab.nw → G.b p + 8 * G.s p < 2 ^ 64 :=
  fun p hp => by have := hG.end_ p hp.2; rw [wd_word hp.1] at this; omega
theorem Ok.arr8_disj (hG : G.Ok) : ∀ a < G.tab.nb, ∀ b < G.tab.nb, a ≠ b → ∀ x, G.In8 a x → ¬ G.In8 b x :=
  fun a ha b hb e x h h' => hG.disj a (by omega) b (by omega) e x (In.of8 ha h) (In.of8 hb h')
theorem Ok.arr64_disj (hG : G.Ok) : ∀ a, G.tab.nb ≤ a ∧ a < G.tab.nb + G.tab.nw →
    ∀ b, G.tab.nb ≤ b ∧ b < G.tab.nb + G.tab.nw → a ≠ b → ∀ x, G.In64 a x → ¬ G.In64 b x :=
  fun a ha b hb e x h h' => hG.disj a ha.2 b hb.2 e x (In.of64 ha.1 h) (In.of64 hb.1 h')
theorem Ok.arr8_64 (hG : G.Ok) : ∀ a < G.tab.nb, ∀ b, G.tab.nb ≤ b ∧ b < G.tab.nb + G.tab.nw →
    ∀ x, G.In8 a x → ¬ G.In64 b x :=
  fun a ha b hb x h h' => hG.disj a (by omega) b hb.2 (by omega) x (In.of8 ha h) (In.of64 hb.1 h')

end

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

/-- L's memory `m` in the machine's data memory `d`. The machine side (`Layout`, the table) is
positional; L's arrays are names, related to their regions through the compiler's layout map
(`Tab.pos8`, `Tab.pos64`): the array a program may name (`dom8`, `dom64`) has the region of its
position. -/
structure MemRel (G : Layout) (m : Mem) (d : DataMem) : Prop where
  size8 : ∀ a, G.tab.dom8 a → (m.arr8 a).size = G.s (G.tab.pos8 a)
  size64 : ∀ s, G.tab.dom64 s → (m.arr64 s).size = G.s (G.tab.pos64 s)
  get8 : ∀ a, G.tab.dom8 a → ∀ (i : Nat) (h : i < (m.arr8 a).size),
    d.get? (A (G.b (G.tab.pos8 a) + i)) = some (m.arr8 a)[i]
  get64 : ∀ s, G.tab.dom64 s → ∀ (i : Nat) (h : i < (m.arr64 s).size),
    rdW d (A (G.b (G.tab.pos64 s) + 8 * i)) = some (m.arr64 s)[i]
  limit : rdW d (A (G.T + 8)) = some (UInt64.ofNat G.lo)
  /-- The descriptors, by position: no L array in them. -/
  base : ∀ p < G.tab.nb + G.tab.nw, rdW d (A (G.T + (G.tab.dbase p).toNat)) = some (UInt64.ofNat (G.b p))
  len : ∀ p < G.tab.nb + G.tab.nw, rdW d (A (G.T + (G.tab.dlen p).toNat)) = some (UInt64.ofNat (G.s p))
  /-- A word position's length in 32-bit elements. -/
  len32 : ∀ p, G.tab.nb ≤ p → p < G.tab.nb + G.tab.nw →
    rdW d (A (G.T + (G.tab.dlen32 p).toNat)) = some (UInt64.ofNat (2 * G.s p))
  rom : ∀ (i : Nat) (h : i < G.tab.rom.length),
    d.get? (A (G.T + 16 + 24 * (G.tab.nb + G.tab.nw) + i)) = some G.tab.rom[i]
  stack : ∀ x, G.InStack x → (d.get? (A x)).isSome
  res : ∀ x, G.InRes x → (d.get? (A x)).isSome
  /-- The global variables. -/
  glob : ∀ g : GVar, g.id < G.tab.ng → rdW d (A (G.globAddr g)) = some (m.glob g)

/-! ### The relation per array, through the layout map

The descriptor words of an array the program may name, read at the address the code computes
(`Tab.base8 a`, …: the position the layout map gives). The simulation proofs use these, never
positions directly. -/

namespace MemRel
variable {G : Layout} {m : Mem} {d : DataMem}

theorem base8A (hm : MemRel G m d) {a : ArrId} (h : G.tab.dom8 a = true) :
    rdW d (A (G.T + (G.tab.base8 a).toNat)) = some (UInt64.ofNat (G.b (G.tab.pos8 a))) :=
  hm.base _ (by have := G.tab.pos8_lt h; omega)
theorem len8A (hm : MemRel G m d) {a : ArrId} (h : G.tab.dom8 a = true) :
    rdW d (A (G.T + (G.tab.len8 a).toNat)) = some (UInt64.ofNat (G.s (G.tab.pos8 a))) :=
  hm.len _ (by have := G.tab.pos8_lt h; omega)
theorem base64A (hm : MemRel G m d) {s : TieredArray} (h : G.tab.dom64 s = true) :
    rdW d (A (G.T + (G.tab.base64 s).toNat)) = some (UInt64.ofNat (G.b (G.tab.pos64 s))) :=
  hm.base _ (G.tab.pos64_lt h).2
theorem len64A (hm : MemRel G m d) {s : TieredArray} (h : G.tab.dom64 s = true) :
    rdW d (A (G.T + (G.tab.len64 s).toNat)) = some (UInt64.ofNat (G.s (G.tab.pos64 s))) :=
  hm.len _ (G.tab.pos64_lt h).2

theorem len32A (hm : MemRel G m d) {s : TieredArray} (h : G.tab.dom64 s = true) :
    rdW d (A (G.T + (G.tab.len32 s).toNat)) = some (UInt64.ofNat (2 * G.s (G.tab.pos64 s))) :=
  hm.len32 _ (G.tab.pos64_lt h).1 (G.tab.pos64_lt h).2

/-- Below the minimum length, an index is in bounds (`Layout.Ok.min64`). -/
theorem lt_of_min (hm : MemRel G m d) (hG : G.Ok) {s : TieredArray} (h : G.tab.dom64 s = true) {k : Nat}
    (hk : k < G.tab.min64 s) : k < (m.arr64 s).size := by
  rw [hm.size64 s h]; exact Nat.lt_of_lt_of_le hk (hG.min64 s h)

end MemRel

theorem mem_allocRegs {r : Reg64} : r ∈ allocRegs ↔
    r = .rdi ∨ r = .r8 ∨ r = .r9 ∨ r = .r10 ∨ r = .r11 ∨ r = .rsi ∨ r = .rbx ∨ r = .r12 ∨ r = .r13 := by
  simp [allocRegs]

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

/-- A table word at offset `off` (within the table) survives a change in the stack. -/
theorem Only.rdW_tab {a b : Nat} {d d' : DataMem} (h : Only a b d d')
    (hab : ∀ x, a ≤ x → x < b → ¬ G.InDesc x ∧ ¬ G.InArr x)
    {off : Nat} (hoff : 8 ≤ off + 8) (hend : G.T + off + 8 ≤ G.T + 16 + 24 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords) :
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
    size8 := hm.size8
    size64 := hm.size64
    get8 := fun c hc i hi => by
      replace hi : i < (Mem.arr8 ⟨b₁, w₁, g₁⟩ c).size := hi
      show _ = some ((Mem.arr8 ⟨b₁, w₁, g₁⟩ c)[i]'hi)
      have hs := hm.size8 c hc
      have hp := G.tab.pos8_lt hc
      have he := hG.end8 _ hp
      rw [h.same _ (by omega) ?_, hm.get8 c hc i hi]
      refine Classical.byContradiction fun hx => ?_
      simp only [not_or, Nat.not_lt] at hx
      exact (hab (G.b (G.tab.pos8 c) + i) (by omega) (by omega)).2 (Layout.InArr.of8 hp ⟨by omega, by omega⟩)
    get64 := fun c hc i hi => by
      replace hi : i < (Mem.arr64 ⟨b₁, w₁, g₁⟩ c).size := hi
      show _ = some ((Mem.arr64 ⟨b₁, w₁, g₁⟩ c)[i]'hi)
      have hs := hm.size64 c hc
      have hp := G.tab.pos64_lt hc
      have he := hG.end64 _ hp
      rw [← hm.get64 c hc i hi]
      refine rdW_congr fun j hj => ?_
      rw [A_add]
      refine h.same _ (by omega) ?_
      refine Classical.byContradiction fun hx => ?_
      simp only [not_or, Nat.not_lt] at hx
      exact (hab (G.b (G.tab.pos64 c) + 8 * i + j) (by omega) (by omega)).2 (Layout.InArr.of64 hp ⟨by omega, by omega⟩)
    limit := by
      rw [h.rdW_tab hG hab (by omega) (by omega)]; exact hm.limit
    base := fun c hc => by
      rw [h.rdW_tab hG hab (by omega) (by simp only [Tab.dbase]; omega)]; exact hm.base c hc
    len := fun c hc => by
      rw [h.rdW_tab hG hab (by omega) (by simp only [Tab.dlen]; omega)]; exact hm.len c hc
    len32 := fun c h1 h2 => by
      rw [h.rdW_tab hG hab (by omega) (by simp only [Tab.dlen32]; omega)]; exact hm.len32 c h1 h2
    rom := fun i hi => by
      have hw : G.tab.rom.length ≤ 8 * G.tab.romWords := G.tab.rom_length_le
      have := hG.tab_end
      simp only [Layout.tabEnd] at this
      rw [h.same _ (by omega) ?_, hm.rom i hi]
      refine Classical.byContradiction fun hc => ?_
      simp only [not_or, Nat.not_lt] at hc
      exact (hab (G.T + 16 + 24 * (G.tab.nb + G.tab.nw) + i) (by omega) (by omega)).1
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
  cell_disj hx hy fun _t h1 h2 => hG.notStack_of_res h1 h2

/-- A change inside the result area keeps the memory relation. -/
theorem MemRel.only_res {m : Mem} {d d' : DataMem} (hm : MemRel G m d) {a b : Nat} (h : Only a b d d')
    (hab : ∀ x, a ≤ x → x < b → G.InRes x) : MemRel G m d' :=
  hm.onlyD hG h (fun x h1 h2 => ⟨fun ⟨_, v⟩ => by have := (hab x h1 h2).1; omega,
    hG.notArr_of_res (hab x h1 h2)⟩) fun x h1 h2 hg => hg.not_res (hab x h1 h2)

/-- A change inside the stack keeps the memory relation. -/
theorem MemRel.only {m : Mem} {d d' : DataMem} (hm : MemRel G m d) {a b : Nat} (h : Only a b d d')
    (hab : ∀ x, a ≤ x → x < b → G.InStack x) : MemRel G m d' :=
  hm.only' hG h fun x h1 h2 => ⟨fun ht => hG.tab_stack _ ht (hab x h1 h2),
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
