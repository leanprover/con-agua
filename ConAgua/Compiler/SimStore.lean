module

public import ConAgua.Compiler.SimStmt
import Kraken.X64.Registers

@[expose] public section

/-!
# Array stores

The memory relation after a store into an array, and the simulation of `A.u8[i] := e` and
`A.u64[i] := e`.
-/

namespace L.Compiler

open L

attribute [local simp] Reg64s.set64_rax Reg64s.set64_rcx Reg64s.set64_rdx Reg64s.set64_rsi
  Reg64s.set64_rsp Reg64s.set64_r14

theorem Mem.arr64_set64 (m : Mem) (a a' : ArrId) (i v : Word) :
    (m.set64 a i v).arr64 a' = if a = a' then (m.arr64 a).set! i.toNat v else m.arr64 a' := by
  simp only [Mem.set64, Mem.arr64]
  by_cases h : a = a'
  · subst h; simp [Array.getD]
    intro h1 h2; omega
  · simp [h, Array.getD]
    split
    · rw [Array.getElem_setIfInBounds_ne]; omega
    · rfl

theorem Mem.arr8_set8 (m : Mem) (a a' : ArrId) (i v : Word) :
    (m.set8 a i v).arr8 a' = if a = a' then (m.arr8 a).set! i.toNat v.toUInt8 else m.arr8 a' := by
  simp only [Mem.set8, Mem.arr8]
  by_cases h : a = a'
  · subst h; simp [Array.getD]
    intro h1 h2; omega
  · simp [h, Array.getD]
    split
    · rw [Array.getElem_setIfInBounds_ne]; omega
    · rfl

theorem Mem.arr8_set64 (m : Mem) (a : ArrId) (i v : Word) : (m.set64 a i v).arr8 = m.arr8 := rfl
theorem Mem.arr64_set8 (m : Mem) (a : ArrId) (i v : Word) : (m.set8 a i v).arr64 = m.arr64 := rfl

section
variable {G : Layout} (hG : G.Ok)
include hG

theorem MemRel.store64 {m : Mem} {d : DataMem} (hm : MemRel G m d) {a : ArrId} (ha : a < G.tab.nw)
    {i : Word} (hi : i.toNat < (m.arr64 a).size) (v : Word) :
    MemRel G (m.set64 a i v) (wrW d (A (G.b64 a + 8 * i.toNat)) v.toBitVec) := by
  have hsz := hm.size64 a ha
  have hend := hG.end64 a ha
  have hcell : ∀ k < 8, G.In64 a (G.b64 a + 8 * i.toNat + k) := fun k hk => ⟨by omega, by omega⟩
  have hov : G.b64 a + 8 * i.toNat + 8 ≤ 2 ^ 64 := by omega
  have htab : ∀ off, 8 ≤ off + 8 → G.T + off + 8 ≤ G.tabEnd →
      rdW (wrW d (A (G.b64 a + 8 * i.toNat)) v.toBitVec) (A (G.T + off)) = rdW d (A (G.T + off)) := by
    intro off _ hoff
    have := hG.tab_end
    refine rdW_wrW_A hov (by omega) ?_
    exact cell_disj (P := G.In64 a) (Q := G.InTab) hcell (fun k hk => ⟨by omega, by omega⟩)
      fun t h1 h2 => hG.tab_arr t h2 (Or.inr ⟨a, ha, h1⟩)
  refine ⟨by simpa [Mem.set64] using hm.nb, by simpa [Mem.set64] using hm.nw,
    fun c hc => by rw [Mem.arr8_set64]; exact hm.size8 c hc,
    fun c hc => by rw [Mem.arr64_set64]; split <;> simp_all [hm.size64 c hc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc k hk
    have hk2 : k < (m.arr8 c).size := hk
    have h8 := hm.size8 c hc
    have he8 := hG.end8 c hc
    rw [get?_wrW_A hov (by omega) ?_]
    · exact hm.get8 c hc k hk2
    exact byte_cell_disj (P := G.In64 a) (Q := G.In8 c) hcell ⟨by omega, by omega⟩
      fun t h1 h2 => hG.arr8_64 c hc a ha t h2 h1
  · intro c hc k hk
    have hk' := hk
    simp only [Mem.arr64_set64] at hk'
    have hsc := hm.size64 c hc
    have hec := hG.end64 c hc
    by_cases hca : a = c
    · subst hca
      by_cases hki : k = i.toNat
      · subst hki
        simp only [Mem.arr64_set64, ite_true, rdW_wrW_same, UInt64.ofBitVec_toBitVec]
        simp
      · simp only [ite_true, Array.size_set!] at hk'
        simp only [Mem.arr64_set64, ite_true]
        rw [rdW_wrW_A hov (by omega) (by omega)]
        simp only [Array.set!]
        rw [Array.getElem_setIfInBounds_ne]
        · exact hm.get64 a ha k hk'
        · omega
    · simp only [Mem.arr64_set64, hca, ite_false]
      simp only [hca, ite_false] at hk'
      rw [rdW_wrW_A hov (by omega) ?_]
      · exact hm.get64 c hc k hk'
      exact cell_disj (P := G.In64 a) (Q := G.In64 c) hcell (fun j hj => ⟨by omega, by omega⟩)
        fun t h1 h2 => hG.arr64_disj a ha c hc hca t h1 h2
  · rw [show G.T + 8 = G.T + 8 from rfl, htab 8 (by omega) (by simp [Layout.tabEnd]; omega)]; exact hm.limit
  · intro c hc; rw [htab _ (by omega) (by simp [Layout.tabEnd, Tab.base8] <;> omega)]; exact hm.base8 c hc
  · intro c hc; rw [htab _ (by omega) (by simp [Layout.tabEnd, Tab.len8] <;> omega)]; exact hm.len8 c hc
  · intro c hc; have := G.tab.wpos_lt hc; rw [htab _ (by omega) (by simp [Layout.tabEnd, Tab.base64] <;> omega)]; exact hm.base64 c hc
  · intro c hc; have := G.tab.wpos_lt hc; rw [htab _ (by omega) (by simp [Layout.tabEnd, Tab.len64] <;> omega)]; exact hm.len64 c hc
  · intro k hk
    have hw : G.tab.rom.length ≤ 8 * G.tab.romWords := G.tab.rom_length_le
    have := hG.tab_end
    simp only [Layout.tabEnd] at this
    rw [get?_wrW_A hov (by omega) ?_]
    · exact hm.rom k hk
    exact byte_cell_disj (P := G.In64 a) (Q := G.InTab) hcell ⟨by omega, by simp only [Layout.tabEnd]; omega⟩
      fun t h1 h2 => hG.tab_arr t h2 (Or.inr ⟨a, ha, h1⟩)
  · intro x hx; exact isSome_get?_storeInt (hm.stack x hx)
  · intro x hx; exact isSome_get?_storeInt (hm.res x hx)
  · intro g hg
    have hT : G.globAddr g + 8 ≤ G.tabEnd := by
      simp only [Layout.tabEnd, Layout.globAddr, Layout.globStart]; omega
    have := htab (G.globAddr g - G.T) (by omega) (by simp only [Layout.globAddr, Layout.globStart] at hT ⊢; omega)
    rw [show G.T + (G.globAddr g - G.T) = G.globAddr g by simp only [Layout.globAddr, Layout.globStart]; omega] at this
    rw [this]; exact hm.glob g hg

theorem MemRel.store8 {m : Mem} {d : DataMem} (hm : MemRel G m d) {a : ArrId} (ha : a < G.tab.nb)
    {i : Word} (hi : i.toNat < (m.arr8 a).size) (v : Word) (V : Int) (hV : (V.take 8).toNat.toUInt8 = v.toUInt8) :
    MemRel G (m.set8 a i v) (Mem.storeInt d (A (G.b8 a + i.toNat)) 1 V) := by
  have hsz := hm.size8 a ha
  have hend := hG.end8 a ha
  have hx : G.b8 a + i.toNat < 2 ^ 64 := by omega
  have hin : G.In8 a (G.b8 a + i.toNat) := ⟨by omega, by omega⟩
  have hcellw : ∀ y, (∀ k < 8, ¬ G.In8 a (y + k)) → y + 8 ≤ 2 ^ 64 →
      rdW (Mem.storeInt d (A (G.b8 a + i.toNat)) 1 V) (A y) = rdW d (A y) := by
    intro y hy hy2
    refine rdW_congr fun j hj => ?_
    rw [A_add]
    exact get?_store1_A hx (by omega) fun he => hy j hj (he ▸ hin)
  have htab : ∀ off, 8 ≤ off + 8 → G.T + off + 8 ≤ G.tabEnd →
      rdW (Mem.storeInt d (A (G.b8 a + i.toNat)) 1 V) (A (G.T + off)) = rdW d (A (G.T + off)) := by
    intro off _ hoff
    have := hG.tab_end
    exact hcellw _ (fun k hk h8 => hG.tab_arr _ ⟨by omega, by omega⟩ (Or.inl ⟨a, ha, h8⟩)) (by omega)
  refine ⟨by simpa [Mem.set8] using hm.nb, by simpa [Mem.set8] using hm.nw,
    fun c hc => by rw [Mem.arr8_set8]; split <;> simp_all [hm.size8 c hc],
    fun c hc => by rw [Mem.arr64_set8]; exact hm.size64 c hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc k hk
    have hk' := hk
    simp only [Mem.arr8_set8] at hk'
    have hsc := hm.size8 c hc
    have hec := hG.end8 c hc
    by_cases hca : a = c
    · subst hca
      by_cases hki : k = i.toNat
      · subst hki
        simp only [Mem.arr8_set8, ite_true]
        rw [Mem.get?_storeInt_one, ite_eq_left_iff.mpr (fun h => absurd rfl h), hV]
        simp
      · simp only [ite_true, Array.size_set!] at hk'
        simp only [Mem.arr8_set8, ite_true]
        rw [get?_store1_A hx (by omega) (by omega)]
        simp only [Array.set!]
        rw [Array.getElem_setIfInBounds_ne]
        · exact hm.get8 a ha k hk'
        · omega
    · simp only [Mem.arr8_set8, hca, ite_false]
      simp only [hca, ite_false] at hk'
      rw [get?_store1_A hx (by omega) ?_]
      · exact hm.get8 c hc k hk'
      intro he
      exact hG.arr8_disj a ha c hc hca _ hin (he ▸ ⟨by omega, by omega⟩)
  · intro c hc k hk
    have hk2 : k < (m.arr64 c).size := hk
    have hsc := hm.size64 c hc
    have hec := hG.end64 c hc
    rw [hcellw _ (fun j hj h8 => hG.arr8_64 a ha c hc _ h8 ⟨by omega, by omega⟩) (by omega)]
    exact hm.get64 c hc k hk2
  · rw [htab 8 (by omega) (by simp [Layout.tabEnd]; omega)]; exact hm.limit
  · intro c hc; rw [htab _ (by omega) (by simp [Layout.tabEnd, Tab.base8] <;> omega)]; exact hm.base8 c hc
  · intro c hc; rw [htab _ (by omega) (by simp [Layout.tabEnd, Tab.len8] <;> omega)]; exact hm.len8 c hc
  · intro c hc; have := G.tab.wpos_lt hc; rw [htab _ (by omega) (by simp [Layout.tabEnd, Tab.base64] <;> omega)]; exact hm.base64 c hc
  · intro c hc; have := G.tab.wpos_lt hc; rw [htab _ (by omega) (by simp [Layout.tabEnd, Tab.len64] <;> omega)]; exact hm.len64 c hc
  · intro k hk
    have hw : G.tab.rom.length ≤ 8 * G.tab.romWords := G.tab.rom_length_le
    have := hG.tab_end
    simp only [Layout.tabEnd] at this
    rw [get?_store1_A hx (by omega) ?_]
    · exact hm.rom k hk
    intro he
    exact hG.tab_arr _ ⟨by omega, by simp only [Layout.tabEnd]; omega⟩ (Or.inl ⟨a, ha, he ▸ hin⟩)
  · intro x hx; exact isSome_get?_storeInt (hm.stack x hx)
  · intro x hx; exact isSome_get?_storeInt (hm.res x hx)
  · intro g hg
    have hT : G.globAddr g + 8 ≤ G.tabEnd := by
      simp only [Layout.tabEnd, Layout.globAddr, Layout.globStart]; omega
    have := htab (G.globAddr g - G.T) (by omega) (by simp only [Layout.globAddr, Layout.globStart] at hT ⊢; omega)
    rw [show G.T + (G.globAddr g - G.T) = G.globAddr g by simp only [Layout.globAddr, Layout.globStart]; omega] at this
    rw [this]; exact hm.glob g hg

theorem Inv.store64 {ctx : Ctx} {F : Nat} {σ : St} {s : MachineData} (hI : Inv G ctx F σ s) {a : ArrId}
    (ha : a < G.tab.nw) {i : Word} (hi : i.toNat < (σ.mem.arr64 a).size) (v : Word) :
    Inv G ctx F { σ with mem := σ.mem.set64 a i v }
      { s with dmem := wrW s.dmem (A (G.b64 a + 8 * i.toNat)) v.toBitVec } := by
  have hsz := hI.mem.size64 a ha
  have hend := hG.end64 a ha
  refine hI.congr rfl rfl rfl (fun _ _ => rfl) (fun x hx hn => ?_) (hI.mem.store64 hG ha hi v)
  have := hI.hi; have := hG.hi_le; have := hI.slot x hx hn; have := hI.lo
  show rdW (wrW s.dmem _ _) (A (s.regs.rsp.toNat + 8 * x)) = _
  rw [rdW_wrW_A (by omega) (by omega) ?_]
  exact cell_disj (P := G.In64 a) (Q := G.InStack) (fun k hk => ⟨by omega, by omega⟩)
    (fun k hk => ⟨by omega, by omega⟩) fun t h1 h2 => hG.stack_arr t h2 (Or.inr ⟨a, ha, h1⟩)

theorem Inv.store8 {ctx : Ctx} {F : Nat} {σ : St} {s : MachineData} (hI : Inv G ctx F σ s) {a : ArrId}
    (ha : a < G.tab.nb) {i : Word} (hi : i.toNat < (σ.mem.arr8 a).size) (v : Word) (V : Int)
    (hV : (V.take 8).toNat.toUInt8 = v.toUInt8) :
    Inv G ctx F { σ with mem := σ.mem.set8 a i v }
      { s with dmem := Mem.storeInt s.dmem (A (G.b8 a + i.toNat)) 1 V } := by
  have hsz := hI.mem.size8 a ha
  have hend := hG.end8 a ha
  refine hI.congr rfl rfl rfl (fun _ _ => rfl) (fun x hx hn => ?_) (hI.mem.store8 hG ha hi v V hV)
  have := hI.hi; have := hG.hi_le; have := hI.slot x hx hn; have := hI.lo
  show rdW (Mem.storeInt s.dmem _ 1 V) (A (s.regs.rsp.toNat + 8 * x)) = _
  refine rdW_congr fun j hj => ?_
  rw [A_add]
  refine get?_store1_A (by omega) (by omega) fun he => ?_
  exact hG.stack_arr (s.regs.rsp.toNat + 8 * x + j) ⟨by omega, by omega⟩
    (Or.inl ⟨a, ha, show G.In8 a _ from ⟨by omega, by omega⟩⟩)

/-- A store into an array keeps every byte outside the arrays. -/
theorem Pres.store64 {top : Nat} {d : DataMem} {a : ArrId} (ha : a < G.tab.nw) {j : Nat} (hj : j < G.s64 a)
    (v : BitVec 64) : Pres G top d (wrW d (A (G.b64 a + 8 * j)) v) := by
  have hend := hG.end64 a ha
  refine ⟨fun _ h => isSome_get?_storeInt h, fun x hx _ hna _ _ => ?_⟩
  refine get?_wrW_A (by omega) hx ?_
  exact byte_cell_disj (P := G.In64 a) (Q := fun t => ¬ G.InArr t) (fun k hk => ⟨by omega, by omega⟩) hna
    fun t h1 h2 => h2 (Or.inr ⟨a, ha, h1⟩)

theorem Pres.store8 {top : Nat} {d : DataMem} {a : ArrId} (ha : a < G.tab.nb) {j : Nat} (hj : j < G.s8 a)
    (V : Int) : Pres G top d (Mem.storeInt d (A (G.b8 a + j)) 1 V) := by
  have hend := hG.end8 a ha
  refine ⟨fun _ h => isSome_get?_storeInt h, fun x hx _ hna _ _ => ?_⟩
  refine get?_store1_A (by omega) hx fun he => hna (Or.inl ⟨a, ha, he ▸ ⟨by omega, by omega⟩⟩)

/-- The memory relation after a write of a global variable, with the frame. -/
theorem Inv.storeG {ctx : Ctx} {F : Nat} {σ : St} {s : MachineData} (hI : Inv G ctx F σ s) {g : GVar}
    (hg : g.id < G.tab.ng) (v : Word) :
    Inv G ctx F (σ.setG g v) { s with dmem := wrW s.dmem (A (G.globAddr g)) v.toBitVec } := by
  have hc := Layout.inGlob_cell (G := G) hg
  have := hG.tab_end
  have hT : G.globAddr g + 8 ≤ G.tabEnd := by
    simp only [Layout.tabEnd, Layout.globAddr, Layout.globStart]; omega
  refine hI.congr rfl rfl rfl (fun _ _ => rfl) (fun x hx hn => ?_) (hI.mem.storeG hG hg v)
  have := hI.hi; have := hG.hi_le; have := hI.slot x hx hn; have := hI.lo
  show rdW (wrW s.dmem _ _) (A (s.regs.rsp.toNat + 8 * x)) = _
  rw [rdW_wrW_A (by omega) (by omega) ?_]
  exact cell_disj (P := G.InGlob) (Q := G.InStack) hc
    (fun k hk => ⟨by omega, by omega⟩) fun t h1 h2 => hG.tab_stack t h1.tab h2

/-- A write of a global variable keeps every byte outside the global variables. -/
theorem Pres.storeG {top : Nat} {d : DataMem} {g : GVar} (hg : g.id < G.tab.ng) (v : BitVec 64) :
    Pres G top d (wrW d (A (G.globAddr g)) v) := by
  have := hG.tab_end
  have hT : G.globAddr g + 8 ≤ G.tabEnd := by
    simp only [Layout.tabEnd, Layout.globAddr, Layout.globStart]; omega
  exact Pres.of_glob (Only.wrW (by omega)) fun x h1 h2 => by
    have hx := Layout.inGlob_cell (G := G) hg (x - G.globAddr g) (by omega)
    rwa [show G.globAddr g + (x - G.globAddr g) = x by omega] at hx

end

theorem byte_val (r : Reg64s) :
    ((r.get (Reg.low .rdx .W8)).toInt.take 8).toNat.toUInt8 = r.rdx.toUInt8 := by
  simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop, Int.take]
  have h : ((r.rdx.toNat : Int).bmod 256 % 256) = (r.rdx.toNat % 256 : Nat) := by
    rw [show (256 : Int) = ((256 : Nat) : Int) by rfl, Int.bmod_emod]; omega
  rw [h]
  apply UInt8.toNat_inj.mp
  simp [UInt64.toNat_toUInt8]
  omega

section
variable [Host] {G : Layout} (hG : G.Ok) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
  (p : Prog) (K : Stmt → M Sig) (P : Nat → Prop) {sk : NTree}
include hG hTab

/-! ## Stores through the register stack (lane leafgen, step G2) -/

omit [Host] in
omit hG hTab in
/-- A write of a pool register (the base register of a store) keeps the invariant and the post. -/
theorem CPost.setPool {ctx : Ctx} {F : Nat} {σ : St} {s : MachineData} (hI : Inv G ctx F σ s) {t : Reg64}
    (ht : t ∈ ctx.pool) (v : BitVec 64) (st : StatusFlags) :
    CPost G ctx F σ s { s with regs := s.regs.set64 t v, status := st } :=
  CPost.ofX hI ((XPost.refl [t] s).set (List.mem_singleton_self t) v st) (by simpa using ht)

omit hTab in
/-- The bounds check, the base and the store of a word (`genSt`), the index `j` in register `X`. -/
theorem genSt_tailWX {ctx : Ctx} {F : Nat} {a' : ArrId} (ha : a' < G.tab.nw)
    {ln bs : AddrExpr} {σ : St} {d s2 : MachineData} {X t : Reg64} {src : Operand .W64} {j vb : Word}
    {kT : Nat} {Q : MachineState → Prop}
    (hcR : Code [i64 (.cmp (.reg (rr X)) (oM ln)), jccL .nc errorL, movRM t bs,
      i64 (.mov (.mem (mbi t X .W64)) src)] kT)
    (hI2 : Inv G ctx F σ s2) (hS2 : SPost G F d s2) (htP : t ∈ ctx.pool) (htX : t ≠ X)
    (hX : s2.regs.get64 X = j.toBitVec)
    (hsrc : src = .imm (.int64 vb.toInt64) ∨ ∃ r, src = oR r ∧ r ≠ t ∧ s2.regs.get64 r = vb.toBitVec)
    (hln : MemW s2 ln (UInt64.ofNat (σ.mem.arr64 a').size))
    (hbs : ∀ st, MemW { s2 with status := st } bs (UInt64.ofNat (G.b64 a')))
    (hok : ∀ s', j.toNat < (σ.mem.arr64 a').size → Inv G ctx F { σ with mem := σ.mem.set64 a' j vb } s' →
      SPost G F d s' → Ev Q s' (at_ (kT + 4)))
    (hoob : ∀ s', ¬ j.toNat < (σ.mem.arr64 a').size → GPost G (top d F) d s' → Ev Q s' (label errorL)) :
    Ev Q s2 (at_ kT) := by
  have hsz := hI2.mem.size64 a' ha
  have hend := hG.end64 a' ha
  have hlt : (σ.mem.arr64 a').size < 2 ^ 64 := by omega
  refine ev_cmpRA hcR.head hln ?_
  rw [hX]
  refine ev_jcc hcR.tail.head (fun hcc => ?_) (fun hcc => ?_)
  · rw [interp_nc] at hcc
    simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hlt] at hcc
    exact hoob _ (by omega) (hS2.trans (SPost.regs rfl rfl rfl (Nat.le_refl _))).gpost
  · rw [interp_nc] at hcc
    simp only [decide_eq_false_iff_not, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hlt] at hcc
    have hj : j.toNat < (σ.mem.arr64 a').size := by omega
    have hI2' : Inv G ctx F σ { s2 with status := cmpFlags j.toBitVec (UInt64.ofNat (σ.mem.arr64 a').size).toBitVec } :=
      hI2.of_regs rfl rfl rfl (fun _ _ => rfl) (fun _ => rfl)
    refine ev_movRA hcR.tail.tail.head (hbs _) ?_
    have hC := CPost.setPool hI2' htP (UInt64.ofNat (G.b64 a')).toBitVec
      (cmpFlags j.toBitVec (UInt64.ofNat (σ.mem.arr64 a').size).toBitVec)
    have haddr : (s2.regs.set64 t (UInt64.ofNat (G.b64 a')).toBitVec).get64 t +
        (s2.regs.set64 t (UInt64.ofNat (G.b64 a')).toBitVec).get64 X * 8 = A (G.b64 a' + 8 * j.toNat) := by
      rw [rget_set, rget_set, ite_eq_left rfl, ite_eq_right (Ne.symm htX), hX]
      apply BitVec.eq_of_toNat_eq
      simp [A, BitVec.toNat_add, BitVec.toNat_mul, UInt64.toNat_ofNat_of_lt' (show G.b64 a' < 2 ^ 64 by omega)]
      omega
    have hmap : (rdW s2.dmem (A (G.b64 a' + 8 * j.toNat))).isSome := by
      rw [hI2.mem.get64 a' ha j.toNat hj]; rfl
    have hfin : ∀ (s3 : MachineData), Inv G ctx F σ s3 → SPost G F d s3 →
        Ev Q { s3 with dmem := wrW s3.dmem (A (G.b64 a' + 8 * j.toNat)) vb.toBitVec } (at_ (kT + 3 + 1)) := by
      intro s3 hI3 hS3
      refine hok _ hj (hI3.store64 hG ha hj vb) ?_
      exact hS3.trans ⟨rfl, rfl, rfl, Nat.le_refl _, Pres.store64 hG ha (by omega) _⟩
    rcases hsrc with rfl | ⟨r, rfl, hrt, hr⟩
    · refine ev_stXI hcR.tail.tail.tail.head ?_ ?_
      · simp only; rw [haddr]; exact hmap
      · simp only; rw [haddr]
        exact hfin _ hC.1 ((hS2.trans (SPost.regs rfl rfl rfl (Nat.le_refl _))).trans hC.2.1)
    · refine ev_stX hcR.tail.tail.tail.head ?_ ?_
      · simp only; rw [haddr]; exact hmap
      · simp only; rw [haddr, rget_set, ite_eq_right hrt, hr]
        exact hfin _ hC.1 ((hS2.trans (SPost.regs rfl rfl rfl (Nat.le_refl _))).trans hC.2.1)


omit hTab in
/-- The bounds check, the base and the store of a word (`genSt`), a constant index `k`. -/
theorem genSt_tailWK {ctx : Ctx} {F : Nat} {a' : ArrId} (ha : a' < G.tab.nw)
    {ln bs : AddrExpr} {σ : St} {d s2 : MachineData} {t : Reg64} {src : Operand .W64} {kk vb : Word}
    {kT : Nat} {Q : MachineState → Prop} (hk : kk.toNat < 2 ^ 28)
    (hcR : Code [i64 (.cmp (.mem ln) (oI kk.toNat)), jccL .be errorL, movRM t bs,
      i64 (.mov (.mem (mb t (8 * kk.toNat))) src)] kT)
    (hI2 : Inv G ctx F σ s2) (hS2 : SPost G F d s2) (htP : t ∈ ctx.pool)
    (hsrc : src = .imm (.int64 vb.toInt64) ∨ ∃ r, src = oR r ∧ r ≠ t ∧ s2.regs.get64 r = vb.toBitVec)
    (hln : MemW s2 ln (UInt64.ofNat (σ.mem.arr64 a').size))
    (hbs : ∀ st, MemW { s2 with status := st } bs (UInt64.ofNat (G.b64 a')))
    (hok : ∀ s', kk.toNat < (σ.mem.arr64 a').size → Inv G ctx F { σ with mem := σ.mem.set64 a' kk vb } s' →
      SPost G F d s' → Ev Q s' (at_ (kT + 4)))
    (hoob : ∀ s', ¬ kk.toNat < (σ.mem.arr64 a').size → GPost G (top d F) d s' → Ev Q s' (label errorL)) :
    Ev Q s2 (at_ kT) := by
  have hsz := hI2.mem.size64 a' ha
  have hend := hG.end64 a' ha
  have hlt : (σ.mem.arr64 a').size < 2 ^ 64 := by omega
  refine ev_cmpAI hcR.head hln ?_
  rw [ofInt_small hk]
  refine ev_jcc hcR.tail.head (fun hcc => ?_) (fun hcc => ?_)
  · rw [interp_be] at hcc
    simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hlt] at hcc
    exact hoob _ (by omega) (hS2.trans (SPost.regs rfl rfl rfl (Nat.le_refl _))).gpost
  · rw [interp_be] at hcc
    simp only [decide_eq_false_iff_not, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hlt] at hcc
    have hj : kk.toNat < (σ.mem.arr64 a').size := by omega
    have hI2' : Inv G ctx F σ { s2 with status := cmpFlags (UInt64.ofNat (σ.mem.arr64 a').size).toBitVec kk.toBitVec } :=
      hI2.of_regs rfl rfl rfl (fun _ _ => rfl) (fun _ => rfl)
    refine ev_movRA hcR.tail.tail.head (hbs _) ?_
    have hC := CPost.setPool hI2' htP (UInt64.ofNat (G.b64 a')).toBitVec
      (cmpFlags (UInt64.ofNat (σ.mem.arr64 a').size).toBitVec kk.toBitVec)
    have hoff : SmallOff (8 * (kk.toNat : Int)) := ⟨by omega, by omega⟩
    have haddr : A (((s2.regs.set64 t (UInt64.ofNat (G.b64 a')).toBitVec).get64 t).toNat + (8 * (kk.toNat : Int)).toNat) =
        A (G.b64 a' + 8 * kk.toNat) := by
      rw [rget_set, ite_eq_left rfl, UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' (show G.b64 a' < 2 ^ 64 by omega)]
      congr 1 <;> omega
    have hmap : (rdW s2.dmem (A (G.b64 a' + 8 * kk.toNat))).isSome := by
      rw [hI2.mem.get64 a' ha kk.toNat hj]; rfl
    have hfin : ∀ (s3 : MachineData), Inv G ctx F σ s3 → SPost G F d s3 →
        Ev Q { s3 with dmem := wrW s3.dmem (A (G.b64 a' + 8 * kk.toNat)) vb.toBitVec } (at_ (kT + 3 + 1)) := by
      intro s3 hI3 hS3
      refine hok _ hj (hI3.store64 hG ha hj vb) ?_
      exact hS3.trans ⟨rfl, rfl, rfl, Nat.le_refl _, Pres.store64 hG ha (by omega) _⟩
    rcases hsrc with rfl | ⟨r, rfl, hrt, hr⟩
    · refine ev_movMW hcR.tail.tail.tail.head hoff ?_ ?_
      · simp only; rw [haddr]; exact hmap
      · simp only; rw [haddr]
        exact hfin _ hC.1 ((hS2.trans (SPost.regs rfl rfl rfl (Nat.le_refl _))).trans hC.2.1)
    · refine ev_movMR hcR.tail.tail.tail.head hoff ?_ ?_
      · simp only; rw [haddr]; exact hmap
      · simp only; rw [haddr, rget_set, ite_eq_right hrt, hr]
        exact hfin _ hC.1 ((hS2.trans (SPost.regs rfl rfl rfl (Nat.le_refl _))).trans hC.2.1)

omit [Host] hG in
/-- A plain word array's descriptor words. -/
theorem descW_plain {ctx : Ctx} {F : Nat} (hT : ctx.tab = G.tab)
    {a : ArrId} (ha : a < G.tab.nw) {σ : St} {s : MachineData} (hI : Inv G ctx F σ s) :
    MemW s (mb .r15 (ctx.tab.len64 a)) (UInt64.ofNat (σ.mem.arr64 a).size) ∧
    MemW s (mb .r15 (ctx.tab.base64 a)) (UInt64.ofNat (G.b64 a)) := by
  have hTab' := hTab
  simp only [maxOff] at hTab'
  have hw64 := G.tab.wpos_lt ha
  have hsz := hI.mem.size64 a ha
  refine ⟨.inl ⟨_, _, rfl, ⟨by simp [Tab.len64]; lomega, by simp [hT, Tab.len64]; lomega⟩, ?_⟩,
    .inl ⟨_, _, rfl, ⟨by simp [Tab.base64]; lomega, by simp [hT, Tab.base64]; lomega⟩, ?_⟩⟩
  · rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT, hsz]; exact hI.mem.len64 a ha
  · rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT]; exact hI.mem.base64 a ha

omit [Host] hG in
/-- A tiered word array's descriptor words, the tier `u & 1` in register `R`. -/
theorem descW_tier {ctx : Ctx} {F : Nat} (hT : ctx.tab = G.tab)
    {a : ArrId} (ha : a < G.tab.wK) {σ : St} {s : MachineData} (hI : Inv G ctx F σ s)
    {R : Reg64} {u : Word} (hR : s.regs.get64 R = (u &&& 1).toBitVec) :
    MemW s (tdesc R (ctx.tab.len64 a)) (UInt64.ofNat (σ.mem.arr64 (tierA a u)).size) ∧
    MemW s (tdesc R (ctx.tab.base64 a)) (UInt64.ofNat (G.b64 (tierA a u))) := by
  have hTab' := hTab
  simp only [maxOff] at hTab'
  have ha' := (G.tab.wK_spec ha).2
  have hta : tierA a u < G.tab.nw := Nat.lt_of_le_of_lt (tierA_le a u) ha'
  have hw := G.tab.wpos_lt (Nat.lt_of_le_of_lt (Nat.le_add_right a tierOff) ha')
  have hb := tier_bit u
  have hoff := tier_off G.tab ha u
  have hD : ∀ d : Int, s.regs.r15.toNat + 8 * (s.regs.get64 R).toNat + d.toNat =
      G.T + 8 * (u &&& 1).toNat + d.toNat := by
    intro d; rw [hR, UInt64.toNat_toBitVec, hI.r15]
  have hsz := hI.mem.size64 _ hta
  refine ⟨.inr ⟨_, _, rfl, ⟨by simp [Tab.len64]; lomega, by simp [hT, Tab.len64]; lomega⟩, ?_⟩,
    .inr ⟨_, _, rfl, ⟨by simp [Tab.base64]; lomega, by simp [hT, Tab.base64]; lomega⟩, ?_⟩⟩
  · rw [hD, show G.T + 8 * (u &&& 1).toNat + (ctx.tab.len64 a).toNat =
      G.T + (G.tab.len64 (tierA a u)).toNat by rw [hT]; omega, hsz]
    exact hI.mem.len64 _ hta
  · rw [hD, show G.T + 8 * (u &&& 1).toNat + (ctx.tab.base64 a).toNat =
      G.T + (G.tab.base64 (tierA a u)).toNat by rw [hT]; omega]
    exact hI.mem.base64 _ hta

omit [Host] in
omit hG hTab in
theorem simpleOp_reg {ctx : Ctx} {e : Expr} {r : Reg .W64} (h : simpleOp ctx e = some (.regOrMem (.reg r))) :
    ∃ x r', ctx.alloc.lookup x = some r' ∧ r = rr r' := by
  cases e <;> simp only [simpleOp] at h
  case var x =>
    cases hl : ctx.alloc.lookup x with
    | some r' => simp only [hl, Option.some.injEq] at h; cases h; exact ⟨x, r', hl, rfl⟩
    | none => simp [hl] at h
  case const w => split at h <;> simp at h
  all_goals simp at h

/-- A store's value (`genStV`): in place, or evaluated into a scratch register. -/
theorem sim_genStV {ctx : Ctx} {F : Nat} (hT : ctx.tab = G.tab) (hF : 8 * F + 8 < maxOff)
    {e : Expr} {fr : List Reg64} {cv : Program} {src : Operand .W64} {fr1 : List Reg64}
    (h : genStV ctx e fr = some (cv, src, fr1)) {k : Nat} (hc : Code cv k)
    (hfr : ∀ r ∈ fr, r ∈ ctx.pool) (hfn : fr.Nodup) (hwf : Expr.wf ctx.nl G.tab e = true)
    {σ : St} {s : MachineData} {Q : MachineState → Prop} (hI : Inv G ctx F σ s)
    (hok : ∀ vb s1, evalP σ e = .ok vb → XPost fr s s1 → (∀ r ∈ fr1, r ∈ fr) → fr1.Nodup →
      (src = .imm (.int64 vb.toInt64) ∨
        ∃ r, src = oR r ∧ r ∉ fr1 ∧ s1.regs.get64 r = vb.toBitVec) →
      Ev Q s1 (at_ (k + cv.length)))
    (herr : ∀ s1, (∃ x, evalP σ e = .error x) → XPost fr s s1 → Ev Q s1 (label errorL)) :
    Ev Q s (at_ k) := by
  unfold genStV at h
  split at h
  · rename_i o ho
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hcv, hsrc, hfr1⟩ := h
    subst hcv hfr1 hsrc
    have hs : ∃ o', simpleOp ctx e = some o' ∧ o = o' ∧
        ((∃ w, o' = .imm w) ∨ ∃ r, o' = .regOrMem (.reg r)) := by
      split at ho
      · rename_i w hw; cases ho; exact ⟨_, hw, rfl, .inl ⟨w, rfl⟩⟩
      · rename_i r hr; cases ho; exact ⟨_, hr, rfl, .inr ⟨r, rfl⟩⟩
      · cases ho
    obtain ⟨o', ho', rfl, hform⟩ := hs
    obtain ⟨vb, hvb, hrd⟩ := simpleOp_reads hT hTab hF hI hwf ho'
    refine ev_congr (hok vb s hvb (XPost.refl _ s) (fun r h => h) hfn ?_) (by simp)
    rcases hform with ⟨w, rfl⟩ | ⟨r0, rfl⟩
    · rcases hrd with h1 | ⟨_, _, h1, _⟩ | ⟨_, h1, _⟩
      · exact .inl h1
      · cases h1
      · cases h1
    · obtain ⟨x, r', hx, rfl⟩ := simpleOp_reg ho'
      rcases hrd with h1 | ⟨_, _, h1, _⟩ | ⟨r, h1, h2⟩
      · cases h1
      · cases h1
      · refine .inr ⟨r, h1, fun hm => ?_, h2⟩
        have hrr : r' = r := by cases h1; rfl
        subst hrr
        exact pool_free hI.al (hfr r' hm) x hx
  · split at h
    case h_2 => cases h
    rename_i v fr'
    obtain ⟨c, hcg, h⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hcv, hsrc, hfr1⟩ := h
    subst hcv hfr1 hsrc
    have hok' : GOk ctx e v fr' :=
      ⟨hfn, fun r h => pool_dreg (hfr r h), fun r h => readsReg_free (pool_free hI.al (hfr r h)) e⟩
    refine sim_gen hG hT hTab hF e v fr' c k hcg hc hok' hwf σ s Q hI ?_ herr
    intro vb s1 hvb hv1 hX1
    exact hok vb s1 hvb hX1 (fun r h => List.mem_cons_of_mem _ h) (List.nodup_cons.mp hfn).2
      (.inr ⟨v, rfl, (List.nodup_cons.mp hfn).1, hv1⟩)

/-- `A.u64[i] := e` through the register stack (`genSt`), for a word array `a'` whose
descriptor words `[ln]`, `[bs]` the code does not change. -/
theorem sim_genStW {ctx : Ctx} {F : Nat} (hT : ctx.tab = G.tab) (hF : 8 * F + 8 < maxOff)
    {ln bs : AddrExpr} {a' : ArrId} (ha : a' < G.tab.nw) {i e : Expr} {code : Program}
    (hg : genSt ctx ln bs i e ctx.pool = some code) {k : Nat} (hc : Code code k)
    (hwi : Expr.wf ctx.nl G.tab i = true) (hwe : Expr.wf ctx.nl G.tab e = true)
    {σ : St} {d : MachineData} {Q : MachineState → Prop} (hI : Inv G ctx F σ d)
    (hD : ∀ s', XPost ctx.pool d s' → MemW s' ln (UInt64.ofNat (σ.mem.arr64 a').size) ∧
      MemW s' bs (UInt64.ofNat (G.b64 a')))
    (hok : ∀ j vb s', evalP σ i = .ok j → evalP σ e = .ok vb → j.toNat < (σ.mem.arr64 a').size →
      Inv G ctx F { σ with mem := σ.mem.set64 a' j vb } s' → SPost G F d s' → Ev Q s' (at_ (k + code.length)))
    (herr : ∀ s', ((∃ x, evalP σ i = .error x) ∨ (∃ x, evalP σ e = .error x) ∨
      ∃ j, evalP σ i = .ok j ∧ ¬ j.toNat < (σ.mem.arr64 a').size) → GPost G (top d F) d s' →
      Ev Q s' (label errorL)) :
    Ev Q d (at_ k) := by
  unfold genSt at hg
  split at hg
  · cases hg
  rename_i cv src fr1 hv
  have hpool : ∀ r ∈ ctx.pool, r ∈ ctx.pool := fun r h => h
  have step1 : ∀ rest, code = cv ++ rest → (∀ vb s1, evalP σ e = .ok vb → XPost ctx.pool d s1 →
      (∀ r ∈ fr1, r ∈ ctx.pool) → fr1.Nodup →
      (src = .imm (.int64 vb.toInt64) ∨ ∃ r, src = oR r ∧ r ∉ fr1 ∧ s1.regs.get64 r = vb.toBitVec) →
      Code rest (k + cv.length) → Ev Q s1 (at_ (k + cv.length))) → Ev Q d (at_ k) := by
    intro rest hcode cont
    subst hcode
    exact sim_genStV hG hTab hT hF hv hc.left hpool (pool_nodup ctx) hwe hI
      (fun vb s1 hvb hX1 hfr1 hfn1 hsrc => cont vb s1 hvb hX1 hfr1 hfn1 hsrc hc.right)
      (fun s1 he hX => herr s1 (.inr (.inl he)) (CPost.ofX hI hX hpool).2.1.gpost)
  split at hg
  · -- a constant index
    rename_i kk
    split at hg
    case isFalse => cases hg
    rename_i hk
    split at hg
    case h_2 => cases hg
    rename_i t rest
    cases hg
    refine step1 _ rfl ?_
    intro vb s1 hvb hX1 hfr1 hfn1 hsrc hc2
    have hC1 := CPost.ofX hI hX1 hpool
    have hsrc' : ∀ (s2 : MachineData) (W : List Reg64), XPost W s1 s2 → (∀ r ∈ W, r ∈ t :: rest) →
        ∀ u ∈ t :: rest, src = .imm (.int64 vb.toInt64) ∨ ∃ r, src = oR r ∧ r ≠ u ∧ s2.regs.get64 r = vb.toBitVec := by
      intro s2 W hX hW u hu
      rcases hsrc with h1 | ⟨r, h1, h2, h3⟩
      · exact .inl h1
      · refine .inr ⟨r, h1, fun e => h2 (e ▸ hu), ?_⟩
        rw [hX.keep r fun h => h2 (hW r h)]; exact h3
    have hDX : ∀ s2 (W : List Reg64), XPost W s1 s2 → (∀ r ∈ W, r ∈ t :: rest) →
        MemW s2 ln (UInt64.ofNat (σ.mem.arr64 a').size) ∧ ∀ st, MemW { s2 with status := st } bs (UInt64.ofNat (G.b64 a')) :=
      fun s2 W hX hW => ⟨(hD s2 ((hX1.trans hX).mono fun r h => (List.mem_append.mp h).elim id
        fun h => hfr1 r (hW r h))).1, fun st => (hD _ (((hX1.trans hX).mono fun r h => (List.mem_append.mp h).elim id
        fun h => hfr1 r (hW r h)).flags st)).2⟩
    have ht : t ∈ ctx.pool := hfr1 t List.mem_cons_self
    refine genSt_tailWK hG ha hk hc2 hC1.1 hC1.2.1 ht
      (hsrc' s1 [] (XPost.refl _ s1) (fun r h => by simp at h) t List.mem_cons_self)
      (hDX s1 [] (XPost.refl _ s1) (fun r h => by simp at h)).1 (hDX s1 [] (XPost.refl _ s1) (fun r h => by simp at h)).2
      (fun s' hj hI' hS' => ev_congr (hok kk vb s' rfl hvb hj hI' hS') (by simp; omega))
      (fun s' hj hG' => herr s' (.inr (.inr ⟨kk, rfl, hj⟩)) hG')
  · rename_i hnk
    split at hg
    · -- the index in a local's register
      rename_i r hr
      split at hg
      case h_2 => cases hg
      rename_i t rest
      cases hg
      refine step1 _ rfl ?_
      intro vb s1 hvb hX1 hfr1 hfn1 hsrc hc2
      have hC1 := CPost.ofX hI hX1 hpool
      have hsrc' : ∀ (s2 : MachineData) (W : List Reg64), XPost W s1 s2 → (∀ r ∈ W, r ∈ t :: rest) →
          ∀ u ∈ t :: rest, src = .imm (.int64 vb.toInt64) ∨ ∃ r, src = oR r ∧ r ≠ u ∧ s2.regs.get64 r = vb.toBitVec := by
        intro s2 W hX hW u hu
        rcases hsrc with h1 | ⟨r, h1, h2, h3⟩
        · exact .inl h1
        · refine .inr ⟨r, h1, fun e => h2 (e ▸ hu), ?_⟩
          rw [hX.keep r fun h => h2 (hW r h)]; exact h3
      have hDX : ∀ s2 (W : List Reg64), XPost W s1 s2 → (∀ r ∈ W, r ∈ t :: rest) →
          MemW s2 ln (UInt64.ofNat (σ.mem.arr64 a').size) ∧ ∀ st, MemW { s2 with status := st } bs (UInt64.ofNat (G.b64 a')) :=
        fun s2 W hX hW => ⟨(hD s2 ((hX1.trans hX).mono fun r h => (List.mem_append.mp h).elim id
          fun h => hfr1 r (hW r h))).1, fun st => (hD _ (((hX1.trans hX).mono fun r h => (List.mem_append.mp h).elim id
          fun h => hfr1 r (hW r h)).flags st)).2⟩
      obtain ⟨x, rfl, hx⟩ : ∃ x, i = .var x ∧ ctx.alloc.lookup x = some r := by
        cases i <;> simp_all [regOf]
      have hxl : x < ctx.nl := by simpa [Expr.wf] using hwi
      have ht : t ∈ ctx.pool := hfr1 t List.mem_cons_self
      have htr : t ≠ r := fun e => pool_free hI.al ht x (e ▸ hx)
      have hr1 : s1.regs.get64 r = (σ.loc x).toBitVec := by
        rw [hX1.keep r fun h => pool_free hI.al h x hx]; exact hI.reg x hxl r hx
      refine genSt_tailWX hG ha hc2 hC1.1 hC1.2.1 ht htr hr1
        (hsrc' s1 [] (XPost.refl _ s1) (fun r h => by simp at h) t List.mem_cons_self)
        (hDX s1 [] (XPost.refl _ s1) (fun r h => by simp at h)).1 (hDX s1 [] (XPost.refl _ s1) (fun r h => by simp at h)).2
        (fun s' hj hI' hS' => ev_congr (hok _ vb s' rfl hvb hj hI' hS') (by simp; omega))
        (fun s' hj hG' => herr s' (.inr (.inr ⟨_, rfl, hj⟩)) hG')
    · -- the index into a scratch register
      split at hg
      case h_2 => cases hg
      rename_i xr t fr2
      obtain ⟨ci, hci, hg⟩ := Option.map_eq_some_iff.mp hg
      cases hg
      refine step1 _ (List.append_assoc _ _ _) ?_
      intro vb s1 hvb hX1 hfr1 hfn1 hsrc hc2
      have hC1 := CPost.ofX hI hX1 hpool
      have hsrc' : ∀ (s2 : MachineData) (W : List Reg64), XPost W s1 s2 → (∀ r ∈ W, r ∈ xr :: t :: fr2) →
          ∀ u ∈ xr :: t :: fr2, src = .imm (.int64 vb.toInt64) ∨ ∃ r, src = oR r ∧ r ≠ u ∧ s2.regs.get64 r = vb.toBitVec := by
        intro s2 W hX hW u hu
        rcases hsrc with h1 | ⟨r, h1, h2, h3⟩
        · exact .inl h1
        · refine .inr ⟨r, h1, fun e => h2 (e ▸ hu), ?_⟩
          rw [hX.keep r fun h => h2 (hW r h)]; exact h3
      have hDX : ∀ s2 (W : List Reg64), XPost W s1 s2 → (∀ r ∈ W, r ∈ xr :: t :: fr2) →
          MemW s2 ln (UInt64.ofNat (σ.mem.arr64 a').size) ∧ ∀ st, MemW { s2 with status := st } bs (UInt64.ofNat (G.b64 a')) :=
        fun s2 W hX hW => ⟨(hD s2 ((hX1.trans hX).mono fun r h => (List.mem_append.mp h).elim id
          fun h => hfr1 r (hW r h))).1, fun st => (hD _ (((hX1.trans hX).mono fun r h => (List.mem_append.mp h).elim id
          fun h => hfr1 r (hW r h)).flags st)).2⟩
      have hxP : ∀ r ∈ xr :: t :: fr2, r ∈ ctx.pool := fun r h => hfr1 r h
      have hoki : GOk ctx i xr (t :: fr2) :=
        ⟨hfn1, fun r h => pool_dreg (hxP r h), fun r h => readsReg_free (pool_free hI.al (hxP r h)) i⟩
      have ht : t ∈ ctx.pool := hxP t (List.mem_cons_of_mem _ List.mem_cons_self)
      have htx : t ≠ xr := fun e => (List.nodup_cons.mp hfn1).1 (e ▸ List.mem_cons_self)
      refine sim_gen hG hT hTab hF i xr (t :: fr2) ci _ hci hc2.left hoki hwi σ s1 Q hC1.1 ?_
        (fun s2 he hX2 => herr s2 (.inl he) (hC1.2.1.trans (CPost.ofX hC1.1 hX2 hxP).2.1).gpost)
      intro j s2 hj hx2 hX2
      have hC2 := CPost.ofX hC1.1 hX2 hxP
      have hc3 := hc2.right
      refine genSt_tailWX hG ha hc3 hC2.1 (hC1.2.1.trans hC2.2.1) ht htx hx2
        (hsrc' s2 _ hX2 (fun r h => h) t (List.mem_cons_of_mem _ List.mem_cons_self))
        (hDX s2 _ hX2 (fun r h => h)).1 (hDX s2 _ hX2 (fun r h => h)).2
        (fun s' hj' hI' hS' => ev_congr (hok j vb s' hj hvb hj' hI' hS') (by simp; omega))
        (fun s' hj' hG' => herr s' (.inr (.inr ⟨j, hj, hj'⟩)) hG')

/-- The bounds check and the store of `A.u64[i] := e`, from `rax = i`, `rdx = e`. -/
theorem sim_st64_tail {ctx : Ctx} {F : Nat} (hT : ctx.tab = G.tab) (hF : 8 * F + 8 < maxOff)
    {a : ArrId} (ha : a < G.tab.nw) {i e : Expr} {σ : St} {d s3 : MachineData} {vi ve : Word}
    {kT kend : Nat} {Q : MachineState → Prop}
    (hcR : Code [i64 (.cmp (.reg (rr .rax)) (oM (mb .r15 (ctx.tab.len64 a)))), jccL .nc errorL,
       movRM .rcx (mb .r15 (ctx.tab.base64 a)), movMR (mbi .rcx .rax .W64) .rdx] kT)
    (hkend : kend = kT + 4) (hvi : evalP σ i = .ok vi) (hve : evalP σ e = .ok ve)
    (hI : Inv G ctx F σ d) (hE13 : EPost ctx.nl F 0 d s3) (hrax : s3.regs.rax = vi)
    (hrdx : s3.regs.rdx = ve) (hK : Conts G ctx F d (stepRun p K (.st64 a i e) σ) kend Q) :
    Ev Q s3 (at_ kT) := by
  have hF' := hF; simp only [maxOff] at hF'
  have hTab' := hTab; simp only [maxOff] at hTab'
  have hsp := hI.hi
  have hhi := hG.hi_le
  have hI3 := hI.ofE hG hE13
  have hsz := hI3.mem.size64 a ha
  have hend := hG.end64 a ha
  have hlt : G.s64 a < UInt64.size := by simp [UInt64.size]; omega
  have hw64 := G.tab.wpos_lt ha
  refine ev_cmpRM hcR.head ⟨by simp [Tab.len64]; lomega, by simp [hT, Tab.len64]; lomega⟩
    (v := UInt64.ofNat (G.s64 a)) ?_ ?_
  · rw [hI3.r15, hT]; exact hI3.mem.len64 a ha
  refine ev_jcc hcR.tail.head (fun hcc => ?_) (fun hcc => ?_)
  · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_true',
      decide_eq_false_iff_not, UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' hlt, hrax] at hcc
    refine hK.err _ ⟨.oob, ?_, by simp⟩ ⟨by simp [hE13.rbp], ?_⟩
    · rw [step_st64_run, hvi]; simp only [hve]
      rw [ite_eq_right (by rw [hsz]; simpa using hcc)]
    · exact Pres.of_only hE13.mem (by have := hI.lo; omega) (by simp only [top]; omega)
  · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_false',
      decide_eq_true_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' hlt, hrax] at hcc
    have hvi' : vi.toNat < G.s64 a := by simpa using hcc
    refine ev_movRM hcR.tail.tail.head ⟨by simp [Tab.base64]; lomega,
      by simp [hT, Tab.base64]; lomega⟩ (v := UInt64.ofNat (G.b64 a)) ?_ ?_
    · simp only [Reg64s.get64_r15, UInt64.toNat_toBitVec]
      rw [hI3.r15, hT]; exact hI3.mem.base64 a ha
    have haddr : (UInt64.ofNat (G.b64 a)).toBitVec + vi.toBitVec * 8 = A (G.b64 a + 8 * vi.toNat) := by
      apply BitVec.eq_of_toNat_eq
      simp [A, BitVec.toNat_add, BitVec.toNat_mul]
      omega
    refine ev_st64 hcR.tail.tail.tail.head ?_ ?_
    · simp only [Reg64s.set64_rcx, UInt64.toBitVec_ofBitVec, hrax]
      rw [haddr]
      have := hI3.mem.get64 a ha vi.toNat (by omega)
      simp [this]
    simp only [Reg64s.set64_rcx, UInt64.toBitVec_ofBitVec, hrax, hrdx]
    rw [haddr]
    have hvb : vi.toNat < (σ.mem.arr64 a).size := by rw [hsz]; exact hvi'
    have hIs := hI3.store64 hG ha hvb ve
    refine ev_congr (hK.normal { σ with mem := σ.mem.set64 a vi ve } _ ?_ (hIs.of_regs rfl (by simp) (by simp) (by alloc_keep))
      ⟨by simp [hE13.rsp], by simp [hE13.rbp], by simp [hE13.r15], by simp [hE13.r14], ?_⟩) ?_
    · rw [step_st64_run, hvi]; simp only [hve]
      rw [ite_eq_left hvb]
    · exact (Pres.of_only hE13.mem (by have := hI.lo; omega) (by simp only [top]; omega)).trans
        (Pres.store64 hG ha hvi' _)
    · omega

theorem sim_st64 (a : ArrId) (i e : Expr) : SimS p G sk (stepRun p K) P (.st64 a i e) := by
  intro ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨ha, hwi⟩, hwe⟩ := hwf
  simp only [tempsS] at htmp
  simp only [compileS, List.append_assoc, List.cons_append, List.nil_append] at hc hK
  have hF' := hF; simp only [maxOff] at hF'
  have hTab' := hTab; simp only [maxOff] at hTab'
  have hsp := hI.hi
  have hhi := hG.hi_le
  cases hgs : genSt ctx (mb .r15 (ctx.tab.len64 a)) (mb .r15 (ctx.tab.base64 a)) i e ctx.pool
  case some code =>
    simp only [hgs] at hc hK
    refine sim_genStW hG hTab hT hF ha hgs hc hwi hwe hI
      (fun s' hX => descW_plain hTab hT ha (CPost.ofX hI hX (fun r h => h)).1) ?_ ?_
    · intro j vb s' hj hvb hjs hI' hS'
      exact hK.normal _ s' (by rw [step_st64_run, hj]; simp only [hvb]; rw [ite_eq_left hjs]) hI' hS'
    · intro s' he hG'
      refine hK.err s' ?_ hG'
      rcases he with ⟨x, hx⟩ | ⟨x, hx⟩ | ⟨j, hj, hn⟩
      · exact ⟨x, by rw [step_st64_run, hx], by rw [evalP_error hx]; simp⟩
      · cases hi : evalP σ i with
        | error y => exact ⟨y, by rw [step_st64_run, hi], by rw [evalP_error hi]; simp⟩
        | ok j => exact ⟨x, by rw [step_st64_run, hi]; simp only [hx], by rw [evalP_error hx]; simp⟩
      · cases he : evalP σ e with
        | error y => exact ⟨y, by rw [step_st64_run, hj]; simp only [he], by rw [evalP_error he]; simp⟩
        | ok v => exact ⟨.oob, by rw [step_st64_run, hj]; simp only [he]; rw [ite_eq_right hn], by simp⟩
  simp only [hgs] at hc hK
  cases hl : loadInto ctx .rdx e
  case some code =>
    simp only [hl, List.append_assoc, List.length_append, List.length_cons, List.length_nil] at hc hK
    refine sim_expr hG ctx hT hTab F hF i 0 k hc.left hwi (htmp.mono (tempsE_bin_left .add i e)) σ d Q hI ?_ ?_
    · intro vi s1 hvi hrax1 hE1
      have hI1 : Inv G ctx F σ s1 :=
        hI.ofE hG hE1
      have hc1 := hc.right
      obtain ⟨ve, hve, hlen, hld⟩ := sim_loadInto (r := .rdx) hT hTab hF hI1 hwe hl hc1.left
      refine hld Q ?_
      have hcT := hc1.right
      rw [hlen] at hcT
      exact sim_st64_tail hG hTab p K hT hF ha hcT (by rw [hlen]; omega) hvi hve hI
        (hE1.trans (EPost.regs' (by simp) _) (Nat.le_refl _)) (by simp [hrax1]) (by simp) hK
    · intro s1 herr1 hE1
      obtain ⟨x, hx⟩ := herr1
      refine hK.err s1 ⟨x, ?_, by rw [evalP_error hx]; simp⟩ (hE1.spost (G := G) hI.lo).gpost
      rw [step_st64_run]; simp only [hx]
  simp only [hl, List.append_assoc, List.cons_append, List.nil_append] at hc hK
  have hc1 := hc.right
  have hns : Expr.isSimple e = false := by
    cases hs : Expr.isSimple e
    · rfl
    · have := loadInto_isSome (ctx := ctx) (r := .rdx) hs; simp [hl] at this
  simp only [hns, Bool.false_eq_true, ite_false] at htmp
  replace htmp := htmp.le (by omega)
  refine sim_expr hG ctx hT hTab F hF i 0 k hc.left hwi (.inr (by omega)) σ d Q hI ?_ ?_
  · intro vi s1 hvi hrax1 hE1
    have hI1 : Inv G ctx F σ s1 :=
      hI.ofE hG hE1
    have hoff : SmallOff (8 * ((ctx.nl : Int) + ((0 : Nat) : Int))) := ⟨by omega, by omega⟩
    refine ev_movMR hc1.head hoff ?_ ?_
    · rw [slot_addr _ (ctx.nl + 0) _ (by omega)]; exact hI1.mapped (by omega)
    rw [slot_addr _ (ctx.nl + 0) _ (by omega)]
    have hE2 := hE1.trans (EPost.store (v := s1.regs.get64 .rax) (j := ctx.nl + 0) (s := s1)
      (by omega) (by omega) (by rw [hE1.rsp]; omega)) (Nat.le_refl _)
    have hI2 := hI.ofE hG hE2
    have hc2 := hc1.tail
    refine sim_expr hG ctx hT hTab F hF e (0 + 1) _ hc2.left hwe (.inr (by omega)) σ _ Q hI2 ?_ ?_
    · intro ve s3 hve hrax3 hE3
      have h1rsp := congrArg UInt64.toNat hE1.rsp
      have h2rsp := congrArg UInt64.toNat hE2.rsp
      have h3rsp := congrArg UInt64.toNat hE3.rsp
      have hE13 := hE2.trans hE3 (by omega)
      have hcR := hc2.right
      refine ev_movRR hcR.head ?_
      refine ev_movRM hcR.tail.head hoff (v := vi) ?_ ?_
      · rw [slot_addr _ (ctx.nl + 0) _ (by omega)]
        simp only [Reg64s.set64_rdx]
        rw [hE3.rsp, hE3.mem.rdW_eq (by omega) (by omega)]
        simp only [hE1.rsp, rdW_wrW_same, Reg64s.get64_rax, hrax1, UInt64.ofBitVec_toBitVec]
      exact sim_st64_tail hG hTab p K hT hF ha hcR.tail.tail
        (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]; omega) hvi hve hI
        (hE13.of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)) (by simp) (by simp [hrax3]) hK
    · intro s3 herr3 hE3
      obtain ⟨x, hx⟩ := herr3
      refine hK.err s3 ⟨x, ?_, by rw [evalP_error hx]; simp⟩
        (((hE2.trans hE3 (by omega)).spost (G := G) hI.lo).gpost)
      rw [step_st64_run, hvi]; simp only [hx]
  · intro s1 herr1 hE1
    obtain ⟨x, hx⟩ := herr1
    refine hK.err s1 ⟨x, ?_, by rw [evalP_error hx]; simp⟩ (hE1.spost (G := G) hI.lo).gpost
    rw [step_st64_run]; simp only [hx]

/-- The descriptor block, the bounds check and the store of `a⟨t⟩.u64[i] := e`, from
`rcx = t`, `rax = i`, `rdx = e`. -/
theorem sim_st64t_core {ctx : Ctx} {F : Nat} (hT : ctx.tab = G.tab) (hF : 8 * F + 8 < maxOff)
    {a : ArrId} (ha : a < G.tab.wK) {t i e : Expr} {σ : St} {d s4 : MachineData}
    {u vi ve : Word} {kT kend : Nat} {Q : MachineState → Prop}
    {R : Reg64} (_hRa : R ≠ .rax) (_hRd : R ≠ .rdx)
    (hcT : Code [i64 (.cmp (.reg (rr .rax)) (oM (tdesc R (ctx.tab.len64 a)))), jccL .nc errorL,
       movRM .rcx (tdesc R (ctx.tab.base64 a)), movMR (mbi .rcx .rax .W64) .rdx] kT)
    (hkend : kend = kT + 4) (hvt : evalP σ t = .ok u) (hvi : evalP σ i = .ok vi) (hve : evalP σ e = .ok ve)
    (hI : Inv G ctx F σ d) (hE : EPost ctx.nl F 0 d s4) (hR : s4.regs.get64 R = (u &&& 1).toBitVec)
    (hrax : s4.regs.rax = vi) (hrdx : s4.regs.rdx = ve)
    (hK : Conts G ctx F d (stepRun p K (.st64t a t i e) σ) kend Q) :
    Ev Q s4 (at_ kT) := by
  have hF' := hF; simp only [maxOff] at hF'
  have hTab' := hTab; simp only [maxOff] at hTab'
  have hsp := hI.hi
  have hhi := hG.hi_le
  have hI4 := hI.ofE hG hE
  have ha' := (G.tab.wK_spec ha).2
  have hta : tierA a u < G.tab.nw := Nat.lt_of_le_of_lt (tierA_le a u) ha'
  have hw := G.tab.wpos_lt (Nat.lt_of_le_of_lt (Nat.le_add_right a tierOff) ha')
  have hb := tier_bit u
  have hr15 := hI4.r15
  have hoff := tier_off G.tab ha u
  have hsz := hI4.mem.size64 _ hta
  have hend := hG.end64 _ hta
  have hlt : G.s64 (tierA a u) < UInt64.size := by simp [UInt64.size]; omega
  have hD : ∀ x : Int, s4.regs.r15.toNat + 8 * (s4.regs.get64 R).toNat + x.toNat =
      G.T + 8 * (u &&& 1).toNat + x.toNat := by
    intro x; rw [hR, UInt64.toNat_toBitVec, hr15]
  have hraxD : ∀ v, (s4.regs.set64 .rcx v).rax = vi := fun v => by rw [← hrax]; rfl
  have hrdxD : ∀ v, (s4.regs.set64 .rcx v).rdx = ve := fun v => by rw [← hrdx]; rfl
  have hE' : ∀ v st', EPost ctx.nl F 0 d { s4 with regs := s4.regs.set64 .rcx v, status := st' } :=
    fun v st' => hE.trans (EPost.regs (by simp) _ _) (Nat.le_refl _)
  refine ev_cmpRMt hcT.head ⟨by simp [Tab.len64]; lomega, by simp [hT, Tab.len64]; lomega⟩
    (v := UInt64.ofNat (G.s64 (tierA a u))) ?_ ?_
  · rw [hD, show G.T + 8 * (u &&& 1).toNat + (ctx.tab.len64 a).toNat =
      G.T + (G.tab.len64 (tierA a u)).toNat by rw [hT]; omega]
    exact hI4.mem.len64 _ hta
  refine ev_jcc hcT.tail.head (fun hcc => ?_) (fun hcc => ?_)
  · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_true',
      decide_eq_false_iff_not, UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' hlt, hrax] at hcc
    have hE5 := hE.trans (EPost.flags (s := s4) (cmpFlags s4.regs.rax.toBitVec (UInt64.ofNat (G.s64 (tierA a u))).toBitVec)) (Nat.le_refl _)
    refine hK.err _ ⟨.oob, ?_, by simp⟩ ⟨by simp; exact hE.rbp, ?_⟩
    · rw [step_st64t_run, hvt]; simp only [hvi, hve]
      rw [ite_eq_right (by rw [hsz]; simpa using hcc)]
    · exact Pres.of_only hE5.mem (by have := hI.lo; omega) (by simp only [top]; omega)
  · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_false',
      decide_eq_true_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' hlt, hrax] at hcc
    have hvi' : vi.toNat < G.s64 (tierA a u) := by simpa using hcc
    refine ev_movRMt hcT.tail.tail.head ⟨by simp [Tab.base64]; lomega,
      by simp [hT, Tab.base64]; lomega⟩ (v := UInt64.ofNat (G.b64 (tierA a u))) ?_ ?_
    · rw [show ∀ st, ({ s4 with status := st } : MachineData).regs = s4.regs from fun _ => rfl, hD,
        show G.T + 8 * (u &&& 1).toNat + (ctx.tab.base64 a).toNat =
        G.T + (G.tab.base64 (tierA a u)).toNat by rw [hT]; omega]
      exact hI4.mem.base64 _ hta
    have haddr : (UInt64.ofNat (G.b64 (tierA a u))).toBitVec + vi.toBitVec * 8 =
        A (G.b64 (tierA a u) + 8 * vi.toNat) := by
      apply BitVec.eq_of_toNat_eq
      simp [A, BitVec.toNat_add, BitVec.toNat_mul]
      omega
    refine ev_st64 hcT.tail.tail.tail.head ?_ ?_
    · simp only [Reg64s.set64_rcx, UInt64.toBitVec_ofBitVec, hrax]
      rw [haddr]
      have := hI4.mem.get64 _ hta vi.toNat (by omega)
      simp [this]
    simp only [Reg64s.set64_rcx, UInt64.toBitVec_ofBitVec, hrax, hrdx]
    rw [haddr]
    have hvb : vi.toNat < (σ.mem.arr64 (tierA a u)).size := by rw [hsz]; exact hvi'
    have hIs := hI4.store64 hG hta hvb ve
    refine ev_congr (hK.normal { σ with mem := σ.mem.set64 (tierA a u) vi ve } _ ?_
      (hIs.of_regs rfl (by simp) (by simp) (by alloc_keep))
      ⟨by simp [hE.rsp], by simp [hE.rbp], by simp [hE.r15], by simp [hE.r14], ?_⟩) ?_
    · rw [step_st64t_run, hvt]; simp only [hvi, hve]
      rw [ite_eq_left hvb]
    · exact (Pres.of_only hE.mem (by have := hI.lo; omega) (by simp only [top]; omega)).trans
        (Pres.store64 hG hta hvi' _)
    · omega

/-- The tier, the bounds check and the store of `a⟨t⟩.u64[i] := e`, from `rcx = t`, `rax = i`,
`rdx = e`. -/
theorem sim_st64t_tail {ctx : Ctx} {F : Nat} (hT : ctx.tab = G.tab) (hF : 8 * F + 8 < maxOff)
    {a : ArrId} (ha : a < G.tab.wK) {t i e : Expr} {σ : St} {d s4 : MachineData}
    {u vi ve : Word} {kT kend : Nat} {Q : MachineState → Prop}
    (hcR : Code (tierDesc .rcx ++ [i64 (.cmp (.reg (rr .rax)) (oM (tdesc .rcx (ctx.tab.len64 a)))), jccL .nc errorL,
       movRM .rcx (tdesc .rcx (ctx.tab.base64 a)), movMR (mbi .rcx .rax .W64) .rdx]) kT)
    (hkend : kend = kT + 5) (hvt : evalP σ t = .ok u) (hvi : evalP σ i = .ok vi) (hve : evalP σ e = .ok ve)
    (hI : Inv G ctx F σ d) (hE : EPost ctx.nl F 0 d s4) (hrcx : s4.regs.get64 .rcx = u.toBitVec)
    (hrax : s4.regs.rax = vi) (hrdx : s4.regs.rdx = ve)
    (hK : Conts G ctx F d (stepRun p K (.st64t a t i e) σ) kend Q) :
    Ev Q s4 (at_ kT) := by
  refine sim_tierDesc (r := .rcx) hcR.left hrcx fun st => ?_
  exact sim_st64t_core hG hTab p K hT hF ha (R := .rcx) (by decide) (by decide) hcR.right
    (by omega) hvt hvi hve hI
    (hE.trans (EPost.regs (by simp) _ _) (Nat.le_refl _)) (by rw [rget_set, ite_eq_left rfl])
    (by rw [← hrax]; rfl) (by rw [← hrdx]; rfl) hK

theorem sim_st64t (a : ArrId) (t i e : Expr) : SimS p G sk (stepRun p K) P (.st64t a t i e) := by
  intro ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨⟨⟨ha, hst⟩, hwt⟩, hwi⟩, hwe⟩ := hwf
  obtain ⟨ld, hld⟩ := Option.isSome_iff_exists.mp (loadInto_isSome (ctx := ctx) (r := .rcx) hst)
  obtain ⟨u0, hu0⟩ := evalP_simple hst σ
  have hldl : ld.length = 1 := by
    unfold loadInto at hld
    split at hld
    · cases hld; rfl
    · obtain ⟨o, -, rfl⟩ := Option.map_eq_some_iff.mp hld; rfl
  simp only [tempsS] at htmp
  simp only [compileS] at hc hK
  cases hgs : (if ctx.isT t then
      genSt ctx (tdesc .rsi (ctx.tab.len64 a)) (tdesc .rsi (ctx.tab.base64 a)) i e ctx.pool else none)
  case some code =>
    simp only [hgs] at hc hK
    split at hgs
    case isFalse => cases hgs
    rename_i hTt
    obtain ⟨x, rfl, hx⟩ : ∃ x, t = .var x ∧ ctx.treg = some x := by
      cases t <;> simp_all [Ctx.isT]
    have hrsi : ∀ s', XPost ctx.pool d s' → s'.regs.get64 .rsi = (σ.loc x &&& 1).toBitVec := by
      intro s' hX
      rw [hX.keep .rsi fun h => (pool_dreg h).rsi (by simp [hx]) rfl]
      simp [Reg64s.get64, hI.tr x hx]
    refine sim_genStW hG hTab hT hF (Nat.lt_of_le_of_lt (tierA_le a _) (G.tab.wK_spec ha).2) hgs hc hwi hwe hI
      (fun s' hX => descW_tier hTab hT ha (CPost.ofX hI hX (fun r h => h)).1 (hrsi s' hX)) ?_ ?_
    · intro j vb s' hj hvb hjs hI' hS'
      exact hK.normal _ s' (by rw [step_st64t_run]; simp only [evalP, hj, hvb]; rw [ite_eq_left hjs]) hI' hS'
    · intro s' he hG'
      refine hK.err s' ?_ hG'
      rcases he with ⟨x, hx⟩ | ⟨x, hx⟩ | ⟨j, hj, hn⟩
      · exact ⟨x, by rw [step_st64t_run]; simp only [evalP, hx], by rw [evalP_error hx]; simp⟩
      · cases hi : evalP σ i with
        | error y => exact ⟨y, by rw [step_st64t_run]; simp only [evalP, hi], by rw [evalP_error hi]; simp⟩
        | ok j => exact ⟨x, by rw [step_st64t_run]; simp only [evalP, hi]; simp only [hx], by rw [evalP_error hx]; simp⟩
      · cases he : evalP σ e with
        | error y => exact ⟨y, by rw [step_st64t_run]; simp only [evalP, hj]; simp only [he], by rw [evalP_error he]; simp⟩
        | ok v => exact ⟨.oob, by rw [step_st64t_run]; simp only [evalP, hj]; simp only [he]; rw [ite_eq_right hn], by simp⟩
  simp only [hgs] at hc hK
  simp only [hld, Option.getD_some, List.append_assoc, List.cons_append,
    List.nil_append] at hc hK
  have hF' := hF; simp only [maxOff] at hF'
  have hTab' := hTab; simp only [maxOff] at hTab'
  have hsp := hI.hi
  have hhi := hG.hi_le
  -- from `rax = vi`, `rdx = ve` at `s3`: the tier into `rcx`, then the tail
  have fin : ∀ (s3 : MachineData) (vi ve : Word) (kT : Nat), evalP σ i = .ok vi → evalP σ e = .ok ve →
      EPost ctx.nl F 0 d s3 → s3.regs.rax = vi → s3.regs.rdx = ve →
      Code (if ctx.isT t = true then
        [i64 (.cmp (.reg (rr .rax)) (oM (tdesc .rsi (ctx.tab.len64 a)))), jccL .nc errorL,
         movRM .rcx (tdesc .rsi (ctx.tab.base64 a)), movMR (mbi .rcx .rax .W64) .rdx]
       else ld ++ (tierDesc .rcx ++ [i64 (.cmp (.reg (rr .rax)) (oM (tdesc .rcx (ctx.tab.len64 a)))), jccL .nc errorL,
       movRM .rcx (tdesc .rcx (ctx.tab.base64 a)), movMR (mbi .rcx .rax .W64) .rdx])) kT →
      ∀ kend, Conts G ctx F d (stepRun p K (.st64t a t i e) σ) kend Q →
      kend = kT + (if ctx.isT t = true then 4 else 6) →
      Ev Q s3 (at_ kT) := by
    intro s3 vi ve kT hvi hve hE3 hrax3 hrdx3 hcT kend hKk hkend
    have hI3 := hI.ofE hG hE3
    by_cases hTt : ctx.isT t = true
    · simp only [hTt, ite_true] at hcT hkend
      cases t with
      | var x =>
        have hx : ctx.treg = some x := by simpa [Ctx.isT] using hTt
        exact sim_st64t_core hG hTab p K hT hF ha (R := .rsi) (u := σ.loc x) (by decide) (by decide) hcT hkend
          rfl hvi hve hI hE3 (by simp [Reg64s.get64, hI3.tr x hx]) hrax3 hrdx3 hKk
      | _ => simp [Ctx.isT] at hTt
    simp only [hTt, Bool.false_eq_true, ite_false] at hcT hkend
    obtain ⟨u, hu, hlen, hldr⟩ := sim_loadInto (r := .rcx) hT hTab hF hI3 hwt hld hcT.left
    refine hldr Q ?_
    have hcT2 := hcT.right
    rw [hlen] at hcT2
    exact sim_st64t_tail hG hTab p K hT hF ha hcT2 (by omega) hu hvi hve hI
      (hE3.trans (EPost.regs' (r := .rcx) (by simp) _) (Nat.le_refl _)) (by rw [rget_set, ite_eq_left rfl])
      (by rw [← hrax3]; rfl) (by rw [← hrdx3]; rfl) hKk
  cases hl : loadInto ctx .rdx e
  case some code =>
    simp only [hl, List.append_assoc, List.length_append] at hc hK
    refine sim_expr hG ctx hT hTab F hF i 0 k hc.left hwi (htmp.mono (tempsE_bin_left .add i e)) σ d Q hI ?_ ?_
    · intro vi s1 hvi hrax1 hE1
      have hI1 : Inv G ctx F σ s1 :=
        hI.ofE hG hE1
      have hc1 := hc.right
      obtain ⟨ve, hve, hlen, hlde⟩ := sim_loadInto (r := .rdx) hT hTab hF hI1 hwe hl hc1.left
      refine hlde Q ?_
      have hcT := hc1.right
      rw [hlen] at hcT
      exact fin _ vi ve _ hvi hve (hE1.trans (EPost.regs' (r := .rdx) (by simp) _) (Nat.le_refl _))
        (by rw [← hrax1]; rfl) rfl hcT _ hK (by rw [hlen]; split <;> simp_all [tierDesc] <;> omega)
    · intro s1 herr1 hE1
      obtain ⟨x, hx⟩ := herr1
      refine hK.err s1 ⟨x, ?_, by rw [evalP_error hx]; simp⟩ (hE1.spost (G := G) hI.lo).gpost
      rw [step_st64t_run, hu0]; simp only [hx]
  simp only [hl, List.append_assoc, List.cons_append, List.nil_append] at hc hK
  have hc1 := hc.right
  have hns : Expr.isSimple e = false := by
    cases hs : Expr.isSimple e
    · rfl
    · have := loadInto_isSome (ctx := ctx) (r := .rdx) hs; simp [hl] at this
  simp only [hns, Bool.false_eq_true, ite_false] at htmp
  replace htmp := htmp.le (by omega)
  refine sim_expr hG ctx hT hTab F hF i 0 k hc.left hwi (.inr (by omega)) σ d Q hI ?_ ?_
  · intro vi s1 hvi hrax1 hE1
    have hI1 : Inv G ctx F σ s1 :=
      hI.ofE hG hE1
    have hoff : SmallOff (8 * ((ctx.nl : Int) + ((0 : Nat) : Int))) := ⟨by omega, by omega⟩
    refine ev_movMR hc1.head hoff ?_ ?_
    · rw [slot_addr _ (ctx.nl + 0) _ (by omega)]; exact hI1.mapped (by omega)
    rw [slot_addr _ (ctx.nl + 0) _ (by omega)]
    have hE2 := hE1.trans (EPost.store (v := s1.regs.get64 .rax) (j := ctx.nl + 0) (s := s1)
      (by omega) (by omega) (by rw [hE1.rsp]; omega)) (Nat.le_refl _)
    have hI2 := hI.ofE hG hE2
    have hc2 := hc1.tail
    refine sim_expr hG ctx hT hTab F hF e (0 + 1) _ hc2.left hwe (.inr (by omega)) σ _ Q hI2 ?_ ?_
    · intro ve s3 hve hrax3 hE3
      have h1rsp := congrArg UInt64.toNat hE1.rsp
      have h2rsp := congrArg UInt64.toNat hE2.rsp
      have h3rsp := congrArg UInt64.toNat hE3.rsp
      have hE13 := hE2.trans hE3 (by omega)
      have hcR := hc2.right
      refine ev_movRR hcR.head ?_
      refine ev_movRM hcR.tail.head hoff (v := vi) ?_ ?_
      · rw [slot_addr _ (ctx.nl + 0) _ (by omega)]
        simp only [Reg64s.set64_rdx]
        rw [hE3.rsp, hE3.mem.rdW_eq (by omega) (by omega)]
        simp only [hE1.rsp, rdW_wrW_same, Reg64s.get64_rax, hrax1, UInt64.ofBitVec_toBitVec]
      exact fin _ vi ve _ hvi hve
        (hE13.of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)) (by simp)
        (by simp [hrax3]) hcR.tail.tail _ hK
        (by split <;> simp_all [tierDesc] <;> omega)
    · intro s3 herr3 hE3
      obtain ⟨x, hx⟩ := herr3
      refine hK.err s3 ⟨x, ?_, by rw [evalP_error hx]; simp⟩
        (((hE2.trans hE3 (by omega)).spost (G := G) hI.lo).gpost)
      rw [step_st64t_run, hu0, hvi]; simp only [hx]
  · intro s1 herr1 hE1
    obtain ⟨x, hx⟩ := herr1
    refine hK.err s1 ⟨x, ?_, by rw [evalP_error hx]; simp⟩ (hE1.spost (G := G) hI.lo).gpost
    rw [step_st64t_run, hu0]; simp only [hx]

/-- The bounds check and the store of `A.u8[i] := e`, from `rax = i`, `rdx = e`. -/
theorem sim_st8_tail {ctx : Ctx} {F : Nat} (hT : ctx.tab = G.tab) (hF : 8 * F + 8 < maxOff)
    {a : ArrId} (ha : a < G.tab.nb) {i e : Expr} {σ : St} {d s3 : MachineData} {vi ve : Word}
    {kT kend : Nat} {Q : MachineState → Prop}
    (hcR : Code [i64 (.cmp (.reg (rr .rax)) (oM (mb .r15 (ctx.tab.len8 a)))), jccL .nc errorL,
       movRM .rcx (mb .r15 (ctx.tab.base8 a)),
       i8 (.mov (.mem (mbi .rcx .rax .W8)) (.regOrMem (.reg (.low .rdx .W8))))] kT)
    (hkend : kend = kT + 4) (hvi : evalP σ i = .ok vi) (hve : evalP σ e = .ok ve)
    (hI : Inv G ctx F σ d) (hE13 : EPost ctx.nl F 0 d s3) (hrax : s3.regs.rax = vi)
    (hrdx : s3.regs.rdx = ve) (hK : Conts G ctx F d (stepRun p K (.st8 a i e) σ) kend Q) :
    Ev Q s3 (at_ kT) := by
  have hF' := hF; simp only [maxOff] at hF'
  have hTab' := hTab; simp only [maxOff] at hTab'
  have hsp := hI.hi
  have hhi := hG.hi_le
  have hI3 := hI.ofE hG hE13
  have hsz := hI3.mem.size8 a ha
  have hend := hG.end8 a ha
  have hlt : G.s8 a < UInt64.size := by simp [UInt64.size]; omega
  refine ev_cmpRM hcR.head ⟨by simp [Tab.len8]; lomega, by simp [Tab.len8]; lomega⟩
    (v := UInt64.ofNat (G.s8 a)) ?_ ?_
  · rw [hI3.r15, hT]; exact hI3.mem.len8 a ha
  refine ev_jcc hcR.tail.head (fun hcc => ?_) (fun hcc => ?_)
  · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_true',
      decide_eq_false_iff_not, UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' hlt, hrax] at hcc
    refine hK.err _ ⟨.oob, ?_, by simp⟩ ⟨by simp [hE13.rbp], ?_⟩
    · rw [step_st8_run, hvi]; simp only [hve]
      rw [ite_eq_right (by rw [hsz]; simpa using hcc)]
    · exact Pres.of_only hE13.mem (by have := hI.lo; omega) (by simp only [top]; omega)
  · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_false',
      decide_eq_true_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' hlt, hrax] at hcc
    have hvi' : vi.toNat < G.s8 a := by simpa using hcc
    refine ev_movRM hcR.tail.tail.head ⟨by simp [Tab.base8]; lomega,
      by simp [Tab.base8]; lomega⟩ (v := UInt64.ofNat (G.b8 a)) ?_ ?_
    · simp only [Reg64s.get64_r15, UInt64.toNat_toBitVec]
      rw [hI3.r15, hT]; exact hI3.mem.base8 a ha
    have haddr : (UInt64.ofNat (G.b8 a)).toBitVec + vi.toBitVec = A (G.b8 a + vi.toNat) := by
      apply BitVec.eq_of_toNat_eq
      simp [A, BitVec.toNat_add]
      (try omega)
    have hvb : vi.toNat < (σ.mem.arr8 a).size := by rw [hsz]; exact hvi'
    refine ev_st8 hcR.tail.tail.tail.head ?_ ?_
    · simp only [Reg64s.set64_rcx, UInt64.toBitVec_ofBitVec, hrax]
      rw [haddr]
      have := hI3.mem.get8 a ha vi.toNat hvb
      rw [this]; rfl
    simp only [Reg64s.set64_rcx, UInt64.toBitVec_ofBitVec, hrax]
    rw [haddr]
    refine ev_congr (hK.normal { σ with mem := σ.mem.set8 a vi ve } _ ?_
      ((hI3.store8 hG ha hvb ve _ ?_).of_regs rfl (by simp) (by simp) ?_)
      ⟨by simp [hE13.rsp], by simp [hE13.rbp], by simp [hE13.r15], by simp [hE13.r14], ?_⟩) ?_
    · rw [step_st8_run, hvi]; simp only [hve]
      rw [ite_eq_left hvb]
    · rw [byte_val, ← hrdx]
    · alloc_keep
    · exact (Pres.of_only hE13.mem (by have := hI.lo; omega) (by simp only [top]; omega)).trans
        (Pres.store8 hG ha hvi' _)
    · omega

theorem sim_st8 (a : ArrId) (i e : Expr) : SimS p G sk (stepRun p K) P (.st8 a i e) := by
  intro ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨ha, hwi⟩, hwe⟩ := hwf
  simp only [tempsS] at htmp
  simp only [compileS, List.append_assoc, List.cons_append, List.nil_append] at hc hK
  have hF' := hF; simp only [maxOff] at hF'
  have hTab' := hTab; simp only [maxOff] at hTab'
  have hsp := hI.hi
  have hhi := hG.hi_le
  cases hl : loadInto ctx .rdx e
  case some code =>
    simp only [hl, List.append_assoc, List.length_append, List.length_cons, List.length_nil] at hc hK
    refine sim_expr hG ctx hT hTab F hF i 0 k hc.left hwi (htmp.mono (tempsE_bin_left .add i e)) σ d Q hI ?_ ?_
    · intro vi s1 hvi hrax1 hE1
      have hI1 : Inv G ctx F σ s1 :=
        hI.ofE hG hE1
      have hc1 := hc.right
      obtain ⟨ve, hve, hlen, hld⟩ := sim_loadInto (r := .rdx) hT hTab hF hI1 hwe hl hc1.left
      refine hld Q ?_
      have hcT := hc1.right
      rw [hlen] at hcT
      exact sim_st8_tail hG hTab p K hT hF ha hcT (by rw [hlen]; omega) hvi hve hI
        (hE1.trans (EPost.regs' (by simp) _) (Nat.le_refl _)) (by simp [hrax1]) (by simp) hK
    · intro s1 herr1 hE1
      obtain ⟨x, hx⟩ := herr1
      refine hK.err s1 ⟨x, ?_, by rw [evalP_error hx]; simp⟩ (hE1.spost (G := G) hI.lo).gpost
      rw [step_st8_run]; simp only [hx]
  simp only [hl, List.append_assoc, List.cons_append, List.nil_append] at hc hK
  have hc1 := hc.right
  have hns : Expr.isSimple e = false := by
    cases hs : Expr.isSimple e
    · rfl
    · have := loadInto_isSome (ctx := ctx) (r := .rdx) hs; simp [hl] at this
  simp only [hns, Bool.false_eq_true, ite_false] at htmp
  replace htmp := htmp.le (by omega)
  refine sim_expr hG ctx hT hTab F hF i 0 k hc.left hwi (.inr (by omega)) σ d Q hI ?_ ?_
  · intro vi s1 hvi hrax1 hE1
    have hI1 : Inv G ctx F σ s1 :=
      hI.ofE hG hE1
    have hoff : SmallOff (8 * ((ctx.nl : Int) + ((0 : Nat) : Int))) := ⟨by omega, by omega⟩
    refine ev_movMR hc1.head hoff ?_ ?_
    · rw [slot_addr _ (ctx.nl + 0) _ (by omega)]; exact hI1.mapped (by omega)
    rw [slot_addr _ (ctx.nl + 0) _ (by omega)]
    have hE2 := hE1.trans (EPost.store (v := s1.regs.get64 .rax) (j := ctx.nl + 0) (s := s1)
      (by omega) (by omega) (by rw [hE1.rsp]; omega)) (Nat.le_refl _)
    have hI2 := hI.ofE hG hE2
    have hc2 := hc1.tail
    refine sim_expr hG ctx hT hTab F hF e (0 + 1) _ hc2.left hwe (.inr (by omega)) σ _ Q hI2 ?_ ?_
    · intro ve s3 hve hrax3 hE3
      have h1rsp := congrArg UInt64.toNat hE1.rsp
      have h2rsp := congrArg UInt64.toNat hE2.rsp
      have h3rsp := congrArg UInt64.toNat hE3.rsp
      have hE13 := hE2.trans hE3 (by omega)
      have hcR := hc2.right
      refine ev_movRR hcR.head ?_
      refine ev_movRM hcR.tail.head hoff (v := vi) ?_ ?_
      · rw [slot_addr _ (ctx.nl + 0) _ (by omega)]
        simp only [Reg64s.set64_rdx]
        rw [hE3.rsp, hE3.mem.rdW_eq (by omega) (by omega)]
        simp only [hE1.rsp, rdW_wrW_same, Reg64s.get64_rax, hrax1, UInt64.ofBitVec_toBitVec]
      exact sim_st8_tail hG hTab p K hT hF ha hcR.tail.tail
        (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]; omega) hvi hve hI
        (hE13.of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)) (by simp) (by simp [hrax3]) hK
    · intro s3 herr3 hE3
      obtain ⟨x, hx⟩ := herr3
      refine hK.err s3 ⟨x, ?_, by rw [evalP_error hx]; simp⟩
        (((hE2.trans hE3 (by omega)).spost (G := G) hI.lo).gpost)
      rw [step_st8_run, hvi]; simp only [hx]
  · intro s1 herr1 hE1
    obtain ⟨x, hx⟩ := herr1
    refine hK.err s1 ⟨x, ?_, by rw [evalP_error hx]; simp⟩ (hE1.spost (G := G) hI.lo).gpost
    rw [step_st8_run]; simp only [hx]

theorem sim_gset (g : GVar) (e : Expr) : SimS p G sk (stepRun p K) P (.gset g e) := by
  intro ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
  simp only [compileS] at hc hK
  simp only [tempsS] at htmp
  have hF' := hF; simp only [maxOff] at hF'
  have hTab' := hTab; simp only [maxOff] at hTab'
  refine sim_expr hG ctx hT hTab F hF e 0 k hc.left hwf.2 (by omega) σ d Q hI ?_ ?_
  · intro v s1 hv hrax hE1
    have hI1 := hI.ofE hG hE1
    have haddr : (s1.regs.get64 .r15).toNat + (ctx.tab.globOff g).toNat = G.globAddr g := by
      rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI1.r15, hT, Layout.globAddr_toNat]
    have hg := hwf.1
    have := hG.tab_end
    have hT' : G.globAddr g + 8 ≤ G.tabEnd := by
      simp only [Layout.tabEnd, Layout.globAddr, Layout.globStart]; omega
    refine ev_movMR hc.right.head ⟨by simp [Tab.globOff, Tab.globBase]; lomega,
      by simp [hT, Tab.globOff, Tab.globBase]; lomega⟩ ?_ ?_
    · rw [haddr, hI1.mem.glob g hg]; rfl
    rw [haddr]
    have hv' : s1.regs.get64 .rax = v.toBitVec := by simp [hrax]
    rw [hv']
    refine ev_congr (hK.normal (σ.setG g v) _ ?_ (hI1.storeG hG hg v) ?_) ?_
    · simp [step_gset_run, hv]; rfl
    · exact (hE1.spost hI.lo).trans ⟨rfl, rfl, rfl, Nat.le_refl _, Pres.storeG hG hg _⟩
    · simp; omega
  · intro s1 herr hE1
    obtain ⟨y, hy⟩ := herr
    refine hK.err s1 ⟨y, by simp [step_gset_run, hy]; rfl, by rw [evalP_error hy]; simp⟩
      (hE1.spost hI.lo).gpost


end


end L.Compiler
