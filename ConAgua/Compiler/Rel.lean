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

namespace Layout

variable (G : Layout)

/-- The bytes of the table that the code reads. -/
def tabEnd : Nat := G.T + 16 + 16 * (G.tab.nb + G.tab.nw)

def InTab (x : Nat) : Prop := G.T ≤ x ∧ x < G.tabEnd
def InStack (x : Nat) : Prop := G.lo ≤ x ∧ x < G.hi
def In8 (a x : Nat) : Prop := G.b8 a ≤ x ∧ x < G.b8 a + G.s8 a
def In64 (a x : Nat) : Prop := G.b64 a ≤ x ∧ x < G.b64 a + 8 * G.s64 a
def InArr (x : Nat) : Prop := (∃ a < G.tab.nb, G.In8 a x) ∨ (∃ a < G.tab.nw, G.In64 a x)

/-- The regions are inside the address space and pairwise disjoint. -/
structure Ok : Prop where
  tab_end : G.tabEnd ≤ 2 ^ 64
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
  stack : ∀ x, G.InStack x → (d.get? (A x)).isSome

/-- The machine runs a body of a function with `nl` locals and an `F`-word frame, in L state `σ`. -/
structure Inv (G : Layout) (nl F : Nat) (σ : St) (s : MachineData) : Prop where
  r15 : s.regs.r15.toNat = G.T
  /-- The next call's return address fits below the frame. -/
  lo8 : G.lo + 8 ≤ s.regs.rsp.toNat
  hi : s.regs.rsp.toNat + 8 * F + 8 ≤ G.hi
  nlF : nl ≤ F
  frame : ∀ x < nl, rdW s.dmem (A (s.regs.rsp.toNat + 8 * x)) = some (σ.loc x)
  mem : MemRel G σ.mem s.dmem

theorem Inv.lo {G : Layout} {nl F : Nat} {σ : St} {s : MachineData} (hI : Inv G nl F σ s) :
    G.lo ≤ s.regs.rsp.toNat := by have := hI.lo8; omega

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
theorem Only.rdW_tab {a b : Nat} {d d' : DataMem} (h : Only a b d d') (hab : ∀ x, a ≤ x → x < b → G.InStack x)
    {off : Nat} (hoff : 8 ≤ off + 8) (hend : G.T + off + 8 ≤ G.tabEnd) :
    rdW d' (A (G.T + off)) = rdW d (A (G.T + off)) :=
  rdW_congr fun j hj => by
    rw [A_add]
    refine h.same _ (by have := hG.tab_end; omega) ?_
    refine Classical.byContradiction fun hc => ?_
    simp only [not_or, Nat.not_lt] at hc
    exact hG.notStack_of_tab ⟨by omega, by omega⟩ (hab (G.T + off + j) (by omega) (by omega))

theorem MemRel.only {m : Mem} {d d' : DataMem} (hm : MemRel G m d) {a b : Nat} (h : Only a b d d')
    (hab : ∀ x, a ≤ x → x < b → G.InStack x) : MemRel G m d' where
  nb := hm.nb
  nw := hm.nw
  size8 := hm.size8
  size64 := hm.size64
  get8 := fun c hc i hi => by
    have hs := hm.size8 c hc
    have he := hG.end8 c hc
    rw [h.same _ (by omega) ?_, hm.get8 c hc i hi]
    refine Classical.byContradiction fun hx => ?_
    simp only [not_or, Nat.not_lt] at hx
    exact hG.notStack_of_arr (Or.inl ⟨c, hc, by omega, by omega⟩) (hab (G.b8 c + i) (by omega) (by omega))
  get64 := fun c hc i hi => by
    have hs := hm.size64 c hc
    have he := hG.end64 c hc
    rw [← hm.get64 c hc i hi]
    refine rdW_congr fun j hj => ?_
    rw [A_add]
    refine h.same _ (by omega) ?_
    refine Classical.byContradiction fun hx => ?_
    simp only [not_or, Nat.not_lt] at hx
    exact hG.notStack_of_arr (Or.inr ⟨c, hc, by omega, by omega⟩) (hab (G.b64 c + 8 * i + j) (by omega) (by omega))
  limit := by
    rw [h.rdW_tab hG hab (by omega) (by simp [Layout.tabEnd])]; exact hm.limit
  base8 := fun c hc => by
    rw [h.rdW_tab hG hab (by omega) (by simp [Layout.tabEnd, Tab.base8] <;> omega)]; exact hm.base8 c hc
  len8 := fun c hc => by
    rw [h.rdW_tab hG hab (by omega) (by simp [Layout.tabEnd, Tab.len8] <;> omega)]; exact hm.len8 c hc
  base64 := fun c hc => by
    rw [h.rdW_tab hG hab (by omega) (by simp [Layout.tabEnd, Tab.base64] <;> omega)]; exact hm.base64 c hc
  len64 := fun c hc => by
    rw [h.rdW_tab hG hab (by omega) (by simp [Layout.tabEnd, Tab.len64] <;> omega)]; exact hm.len64 c hc
  stack := fun x hx => h.grows _ (hm.stack x hx)

/-- A change among the temporaries keeps `Inv`. -/
theorem Inv.only {nl F : Nat} {σ : St} {s s' : MachineData} (hI : Inv G nl F σ s)
    (h : Only (s.regs.rsp.toNat + 8 * nl) (s.regs.rsp.toNat + 8 * F) s.dmem s'.dmem)
    (hsp : s'.regs.rsp = s.regs.rsp) (h15 : s'.regs.r15 = s.regs.r15) : Inv G nl F σ s' where
  r15 := h15 ▸ hI.r15
  lo8 := hsp ▸ hI.lo8
  hi := hsp ▸ hI.hi
  nlF := hI.nlF
  frame := fun x hx => by
    have := hI.hi; have := hG.hi_le; have := hI.nlF
    rw [hsp, h.rdW_eq (by omega) (by omega)]; exact hI.frame x hx
  mem := hI.mem.only hG h fun x h1 h2 => ⟨by have := hI.lo; omega, by have := hI.hi; omega⟩

end
end L.Compiler
