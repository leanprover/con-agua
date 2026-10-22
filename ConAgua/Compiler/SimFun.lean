module

public import ConAgua.Compiler.SimCall
public import ConAgua.L.Logic

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

theorem zeroLocals_length (j m : Nat) : (zeroLocals j m).length = m := by
  induction m generalizing j with
  | zero => rfl
  | succ m ih => simp [zeroLocals, ih]

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

theorem sim_zero (sp : Nat) (Q : MachineState → Prop) :
    ∀ (m j k : Nat) (s : MachineData), Code (zeroLocals j m) k → 8 * (j + m) < 2 ^ 31 →
    s.regs.rsp.toNat = sp → sp + 8 * (j + m) ≤ 2 ^ 64 →
    (∀ i, j ≤ i → i < j + m → (rdW s.dmem (A (sp + 8 * i))).isSome) →
    (∀ s', s'.regs = s.regs →
      Only (sp + 8 * j) (sp + 8 * (j + m)) s.dmem s'.dmem →
      (∀ i, j ≤ i → i < j + m → rdW s'.dmem (A (sp + 8 * i)) = some 0) →
      Ev Q s' (at_ (k + m))) →
    Ev Q s (at_ k) := by
  intro m
  induction m with
  | zero =>
    intro j k s _ _ _ _ _ hK
    exact hK s rfl (Only.refl _ _ _) (fun i h1 h2 => absurd h2 (by omega))
  | succ m ih =>
    intro j k s hc hoff hsp hov hmap hK
    simp only [zeroLocals] at hc
    refine ev_movMI hc.head ⟨by omega, by omega⟩ ?_ ?_
    · simp only [Reg64s.set64_rax, Reg64s.get64_rsp, UInt64.toNat_toBitVec, toNat_eight_mul]
      rw [hsp]; exact hmap j (Nat.le_refl _) (by omega)
    simp only [Reg64s.get64_rsp, UInt64.toNat_toBitVec, toNat_eight_mul]
    rw [hsp]
    refine ih (j + 1) _ _ hc.tail (by omega) (by simp [hsp]) (by omega) ?_ ?_
    · intro i h1 h2
      simp only
      rw [rdW_wrW_A (by omega) (by omega) (by omega)]
      exact hmap i (by omega) (by omega)
    · intro s' h1 hO hsl
      refine ev_congr (hK s' h1 ((Only.wrW (by omega)).union hO (by omega) (by omega) (by omega) (by omega)) ?_) (by omega)
      intro i h1i h2i
      by_cases hij : i = j
      · subst hij
        rw [hO.rdW_eq (by omega) (by omega)]
        simp [rdW_wrW_same]
      · exact hsl i (by omega) (by omega)

end

section
variable [Host] {G : Layout} (hG : G.Ok) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff) (p : Prog)
include hG hTab

theorem funSim (hwfp : ∀ f fd, p.lookup f = some fd → FunDecl.wf p G.tab fd = true) (n : Nat)
    (hE : ExecSim p G n) : FunSim p G n := by
  intro f fd kf hlk hkf vs σ d ra Q hvl hra hargs hap1 hap2 hlo hhi h15 hmem hfuel hKret hKerr hKexh
  have hap1' := hap1
  have hwf := hwfp f fd hlk
  simp only [FunDecl.wf_eq, FunDecl.wfSpec, Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨hnp, hbody⟩, hFoff⟩ := hwf
  simp only [maxOff] at hFoff
  have hhi2 := hG.hi_le
  simp only [compileFn, List.append_assoc, List.cons_append, List.nil_append] at hkf
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
  · simp only [Reg64s.set64_rax, Reg64s.get64_rax, Reg64s.get64_rsp, CondCode.interp, cmpFlags_cf,
      decide_eq_false_iff_not] at hcc
    have hlo' : (UInt64.ofNat G.lo).toNat = G.lo := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
    have hgap : 8 * frameWords fd + 8 ≤ d.regs.rsp.toNat - G.lo := by
      simp only [BitVec.toNat_sub, UInt64.toNat_toBitVec, hlo'] at hcc
      have : (Int64.ofInt (8 * ↑(frameWords fd) + 8)).toBitVec.toNat = 8 * frameWords fd + 8 := by
        simp [Int64.toBitVec_ofInt]; omega
      rw [this] at hcc
      omega
    have hF8 := hgap
    have hnlF : fd.nlocals ≤ frameWords fd := by simp [frameWords]
    suffices H : ∀ s4 : MachineData, s4.regs.rsp.toNat = d.regs.rsp.toNat - 8 * frameWords fd →
        s4.regs.rsi = d.regs.rsi → s4.regs.r15 = d.regs.r15 → s4.regs.rbp = d.regs.rbp →
        s4.regs.r14 = d.regs.r14 → s4.dmem = d.dmem → Ev Q s4 (at_ (kf + 1 + 1 + 1 + 1 + 1 + 1)) by
      refine ev_subRI c1.tail.tail.tail.tail.head fun st2 => H _ ?_ (by simp) (by simp) (by simp) (by simp) rfl
      simp [Int64.toBitVec_ofInt, BitVec.toNat_sub]
      have hm : ((8 : UInt64) * OfNat.ofNat (frameWords fd)).toNat = 8 * frameWords fd := by
        simp [UInt64.toNat_mul]
        rw [UInt64.toNat_ofNat_of_lt (by simp [UInt64.size]; omega)]
        omega
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hm]; omega), hm]
    intro s4 h4sp h4si h415 h4bp h414 h4m
    have c2 := c1.tail.tail.tail.tail.tail
    have hlenF : vs.length ≤ frameWords fd := by omega
    refine sim_copy vs (d.regs.rsp.toNat - 8 * frameWords fd) d.regs.rsi.toNat Q fd.nparams 0 _ s4 c2.left
      (by omega) (by omega) h4sp (by rw [h4si]) (fun j hj _ => by rw [h4m]; exact hargs j hj) (by omega) (by omega)
      (by omega)
      (fun j _ hj => isSome_rdW fun i hi => by
        rw [h4m, A_add]; exact hmem.stack _ ⟨by omega, by omega⟩) ?_
    intro s5 h5sp h5si h515 h5bp h514 h5O h5sl
    refine ev_congr (sim_zero (d.regs.rsp.toNat - 8 * frameWords fd) Q (fd.nlocals - fd.nparams) fd.nparams _ s5
      c2.right.left (by omega) (by rw [h5sp, h4sp]) (by omega) ?_ ?_) (by rw [copyParams_length])
    · intro i h1 h2
      refine isSome_rdW fun j hj => ?_
      rw [A_add]
      refine h5O.grows _ ?_
      rw [h4m]; exact hmem.stack _ ⟨by omega, by omega⟩
    intro s6 h6r h6O h6z
    have h5sp' := congrArg UInt64.toNat h5sp
    have hsp6 : s6.regs.rsp.toNat = d.regs.rsp.toNat - 8 * frameWords fd := by
      rw [h6r]; omega
    have hm5 : MemRel G σ.mem s5.dmem :=
      MemRel.only hG (h4m ▸ hmem) h5O fun z h1 h2 => ⟨by omega, by omega⟩
    have hm6 : MemRel G σ.mem s6.dmem :=
      MemRel.only hG hm5 h6O fun z h1 h2 => ⟨by omega, by omega⟩
    have hI6 : Inv G fd.nlocals (frameWords fd) { σ with loc := Locals.init vs } s6 := by
      refine ⟨by rw [h6r, h515, h415]; exact h15, by omega, by omega, hnlF, fun x hx => ?_, hm6⟩
      rw [hsp6]
      by_cases hxp : x < fd.nparams
      · rw [h6O.rdW_eq (by omega) (by omega), h5sl x (by omega) (Nat.zero_le _) (by omega)]
        simp [Locals.init, List.getD, hvl, hxp]
      · rw [h6z x (by omega) (by omega)]
        have : vs.length ≤ x := by omega
        simp [Locals.init, List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
    have c3 := c2.right.right.right
    have hP6 : Pres G d.regs.rsp.toNat d.dmem s6.dmem :=
      (Pres.of_only (h4m ▸ h5O) (by omega) (by omega)).trans (Pres.of_only h6O (by omega) (by omega))
    have h6bp : s6.regs.rbp = d.regs.rbp := by rw [h6r, h5bp, h4bp]
    have h615 : s6.regs.r15 = d.regs.r15 := by rw [h6r, h515, h415]
    have h614 : s6.regs.r14 = d.regs.r14 := by rw [h6r, h514, h414]
    have htop : top s6 (frameWords fd) = d.regs.rsp.toNat := by simp only [top]; omega
    -- the epilogue, from label `.R`
    have cR := c3.tail.right
    have hepi : ∀ (r : List Word) (σ2 : St) (d2 : MachineData),
        (invoke p (exec p n) f vs).run σ = .ok (r, { σ2 with loc := σ.loc }) →
        MemRel G σ2.mem d2.dmem → SPost G (frameWords fd) s6 d2 → ResOut G r d2 →
        Ev Q d2 (at_ (kf + 1 + 1 + 1 + 1 + 1 + 1 + (copyParams 0 fd.nparams).length +
          (zeroLocals fd.nparams (fd.nlocals - fd.nparams)).length +
          (compileS { tab := G.tab, fn := f, nl := fd.nlocals, brk := lbl f "" "Z" } "" fd.body).length + 1 +
          (loadRes { tab := G.tab, fn := f, nl := fd.nlocals, brk := lbl f "" "Z" } 0 0 G.tab.nres).length)) := by
      intro r σ2 d2 hrun hm2 hS2 hrax
      have hP2 : Pres G d.regs.rsp.toNat d.dmem d2.dmem := hP6.trans (htop ▸ hS2.mem)
      have h2sp : d2.regs.rsp.toNat = d.regs.rsp.toNat - 8 * frameWords fd := by
        rw [congrArg UInt64.toNat hS2.rsp]; exact hsp6
      refine ev_label cR.head ?_
      refine ev_addRI cR.tail.head fun st => ?_
      have hadd' : d2.regs.rsp.toBitVec + (Int64.ofInt (8 * ↑(frameWords fd))).toBitVec = A d.regs.rsp.toNat := by
        rw [show (8 * (frameWords fd : Int)) = ((8 * frameWords fd : Nat) : Int) by push_cast; rfl,
          int64_ofInt_toBitVec]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, A]
        omega
      have hadd : (UInt64.ofBitVec (d2.regs.rsp.toBitVec + (Int64.ofInt (8 * ↑(frameWords fd))).toBitVec)).toNat
          = d.regs.rsp.toNat := by
        rw [hadd']; simp [A]
      refine ev_ret cR.tail.tail.head (ra := ra) ?_ ?_
      · simp only [Reg64s.set64_rsp, Reg64s.get64_rsp]
        rw [hadd', rdW_of_pres hG hP2 (by omega) (by omega) (by omega)]; exact hra
      · refine hKret r { σ2 with loc := σ.loc } _ hrun hm2 rfl ?_ ?_ ?_ ?_ ?_ hP2
        · simp only [Reg64s.set64_rsp, Reg64s.get64_rsp, UInt64.toBitVec_ofBitVec, hadd']
          simp only [UInt64.toNat_ofBitVec, BitVec.toNat_add, A, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
          omega
        · simp; exact hS2.rbp.trans h6bp
        · simp; exact hS2.r15.trans h615
        · simp; have := hS2.r14; rw [h614] at this; exact this
        · exact ⟨(hrax.1.set64 (r := .rsp) (by simp) _).set64 (r := .rsp) (by simp) _, hrax.2⟩
    have hrun : ∀ r σ2, (exec p n fd.body).run { σ with loc := Locals.init vs } = .ok (r, σ2) →
        (invoke p (exec p n) f vs).run σ = .ok (r.retVal, { σ2 with loc := σ.loc }) := by
      intro r σ2 h
      rw [invoke_eq vs hlk, callFn_run, h]
    -- falling off the end, or `break` outside a loop: no results
    have hZ : ∀ σ2 d2, (exec p n fd.body).run { σ with loc := Locals.init vs } = .ok (.normal, σ2) ∨
        (exec p n fd.body).run { σ with loc := Locals.init vs } = .ok (.brk, σ2) →
        Inv G fd.nlocals (frameWords fd) σ2 d2 → SPost G (frameWords fd) s6 d2 →
        Ev Q d2 (at_ (kf + 1 + 1 + 1 + 1 + 1 + 1 + (copyParams 0 fd.nparams).length +
          (zeroLocals fd.nparams (fd.nlocals - fd.nparams)).length +
          (compileS { tab := G.tab, fn := f, nl := fd.nlocals, brk := lbl f "" "Z" } "" fd.body).length)) := by
      intro σ2 d2 hr hI2 hS2
      refine ev_label c3.head ?_
      have hTab' := hTab; simp only [maxOff] at hTab'
      have hI2hi := hI2.hi
      simp only [frameWords] at hFoff hI2hi
      refine sim_loadRes hG _ rfl [] Q (by omega) G.tab.nres 0 _ d2 c3.tail.left (by omega)
        (by simp; omega) hI2.r15 hI2.lo (by simp; omega)
        (fun x hx => hI2.mem.res x hx) (fun j hj => absurd hj (by simp)) (fun j hj => absurd hj (Nat.not_lt_zero _))
        (fun j _ hj => absurd hj (Nat.not_lt_zero _)) ?_
      intro s3 h1 h2 h3 h4 hO hR hM
      refine hepi [] σ2 s3 ?_ (hI2.mem.only_res hG hO (fun x a b => Layout.inRes_of a b))
        (hS2.trans ⟨h1, h2, h4, by rw [h3]; exact Nat.le_refl _, Pres.of_res hO fun x a b => Layout.inRes_of a b⟩)
        ⟨fun j hj => hR j (by omega), fun j h1 h2 => hM j h1 (by omega)⟩
      rcases hr with hr | hr <;> exact hrun _ _ hr
    refine ev_congr (j := kf + 1 + 1 + 1 + 1 + 1 + 1 + (copyParams 0 fd.nparams).length +
      (zeroLocals fd.nparams (fd.nlocals - fd.nparams)).length) ?_ (by rw [zeroLocals_length])
    refine hE fd.body { tab := G.tab, fn := f, nl := fd.nlocals, brk := lbl f "" "Z" } (frameWords fd) "" _ rfl
      (by simp only [maxOff]; omega) c2.right.right.left hbody (by simp [frameWords]) _ s6 Q hI6
      (by rw [h614]; exact hfuel) ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro σ2 d2 hr hI2 hS2
      exact hZ σ2 d2 (.inl hr) hI2 hS2
    · intro σ2 d2 hr hI2 hS2
      show Ev Q d2 (label (Ctx.endL { tab := G.tab, fn := f, nl := fd.nlocals, brk := lbl f "" "Z" }))
      rw [Code.label (i := 0) c3 rfl, Nat.add_zero]
      exact hZ σ2 d2 (.inr hr) hI2 hS2
    · intro v σ2 d2 hr hI2 hS2 hv
      rw [Code.label (i := 0) cR rfl, Nat.add_zero]
      exact hepi v σ2 d2 (hrun _ _ hr) hI2.mem hS2 hv
    · intro d2 ⟨e, hr, hne⟩ hG2
      refine hKerr d2 ⟨e, ?_, hne⟩ ⟨hG2.rbp.trans h6bp, hP6.trans (htop ▸ hG2.mem)⟩
      rw [invoke_eq vs hlk, callFn_run]
      have : (exec p n fd.body).run { σ with loc := Locals.init vs } = .error e := hr
      rw [this]
    · intro d2 hG2
      exact hKexh d2 ⟨hG2.rbp.trans h6bp, hP6.trans (htop ▸ hG2.mem)⟩

end

end L.Compiler
