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
def FunSim [Host] (p : Prog) (G : Layout) (t : NTree) (n : Nat) : Prop :=
  ∀ (f : FnName) (fd : FunDecl) (kf : Nat), p.lookup f = some fd → Code (compileFn G.tab t f fd) kf →
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
      d'.regs.r15 = d.regs.r15 → d'.regs.r14.toNat ≤ d.regs.r14.toNat → ResOut G (Stmt.nret fd.body) r d' →
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

theorem resOff_toNat (t : Tab) (i : Nat) :
    (t.resOff i).toNat = 16 + 16 * (t.nb + t.nw) + 8 * t.romWords + 8 * (i - maxRes) := by
  simp only [Tab.resOff, Tab.resBase]; omega

/-- The address of result slot `i`, as the code computes it from `r15`. -/
theorem res_addr {G : Layout} {R : Reg64s} (h15 : R.r15.toNat = G.T) (i : Nat) :
    A ((R.get64 .r15).toNat + (G.tab.resOff i).toNat) = A (G.resAddr i) := by
  simp only [Reg64s.get64_r15, UInt64.toNat_toBitVec, h15, resOff_toNat, Layout.resAddr]; congr 1; omega

theorem resAddr_cell {G : Layout} {i : Nat} (h1 : maxRes ≤ i) (h2 : i < G.tab.nres) :
    ∀ t < 8, G.InRes (G.resAddr i + t) := fun t ht => by
  simp only [Layout.InRes, Layout.resAddr, Tab.nxres]; omega

theorem rres_set64_rcx (R : Reg64s) (v : BitVec 64) (j : Nat) : rres (R.set64 .rcx v) j = rres R j :=
  rres_set64 R (by simp) v j

section
variable [Host]

/-- Setting results `i, …, i + n - 1` from the temporaries holding `vs` (and `0` past the end of
`vs`): registers below `maxRes`, the result area from `maxRes` on. The results are those of `ws`,
which agrees with `vs` from `i` on (the trampoline: the entry's results below `i`, zeroes). -/
theorem sim_loadRes {G : Layout} (hG : G.Ok) (ctx : Ctx) (hT : ctx.tab = G.tab) (vs ws : List Word)
    (Q : MachineState → Prop)
    (hres : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres < 2 ^ 31) :
    ∀ (n i k : Nat) (s : MachineData), Code (loadRes ctx vs.length i n) k → i + n ≤ G.tab.nres →
    8 * (ctx.nl + vs.length) < 2 ^ 31 → s.regs.r15.toNat = G.T → G.lo ≤ s.regs.rsp.toNat →
    s.regs.rsp.toNat + 8 * (ctx.nl + vs.length) ≤ G.hi →
    (∀ x, G.InRes x → (s.dmem.get? (A x)).isSome) →
    (∀ j (h : j < vs.length), rdW s.dmem (A (s.regs.rsp.toNat + 8 * (ctx.nl + j))) = some vs[j]) →
    (∀ j < i, j < maxRes → rres s.regs j = ws.getD j 0) →
    (∀ j, maxRes ≤ j → j < i → rdW s.dmem (A (G.resAddr j)) = some (ws.getD j 0)) →
    (∀ j, i ≤ j → ws.getD j 0 = vs.getD j 0) →
    (∀ s' : MachineData, s'.regs.rsp = s.regs.rsp → s'.regs.rbp = s.regs.rbp → s'.regs.r14 = s.regs.r14 →
      s'.regs.r15 = s.regs.r15 → Only (G.resAddr maxRes) (G.resAddr G.tab.nres) s.dmem s'.dmem →
      (∀ j < i + n, j < maxRes → rres s'.regs j = ws.getD j 0) →
      (∀ j, maxRes ≤ j → j < i + n → rdW s'.dmem (A (G.resAddr j)) = some (ws.getD j 0)) →
      Ev Q s' (at_ (k + (loadRes ctx vs.length i n).length))) →
    Ev Q s (at_ k) := by
  have hhi := hG.hi_le
  intro n
  induction n with
  | zero =>
    intro i k s _ _ _ _ _ _ _ _ hpre hpm _ h
    exact ev_congr (h s rfl rfl rfl rfl (Only.refl _ _ _) (fun j hj => hpre j (by omega))
      (fun j h1 h2 => hpm j h1 (by omega))) (by simp [loadRes])
  | succ n ih =>
    intro i k s hc hn hoff h15 hlo hhis hmap hsl hpre hpm hw h
    simp only [loadRes] at hc
    -- after one result: the state `s2` holds result `i`
    have hnext : ∀ (m : Nat) (s2 : MachineData), Code (loadRes ctx vs.length (i + 1) n) (k + m) →
        (loadRes ctx vs.length i (n + 1)).length = m + (loadRes ctx vs.length (i + 1) n).length →
        s2.regs.rsp = s.regs.rsp → s2.regs.rbp = s.regs.rbp → s2.regs.r14 = s.regs.r14 →
        s2.regs.r15 = s.regs.r15 → Only (G.resAddr maxRes) (G.resAddr G.tab.nres) s.dmem s2.dmem →
        (∀ j, j ≠ i → j < maxRes → rres s2.regs j = rres s.regs j) →
        (i < maxRes → rres s2.regs i = vs.getD i 0) →
        (∀ j, j ≠ i → maxRes ≤ j → j < i → rdW s2.dmem (A (G.resAddr j)) = rdW s.dmem (A (G.resAddr j))) →
        (maxRes ≤ i → rdW s2.dmem (A (G.resAddr i)) = some (vs.getD i 0)) →
        (∀ j (h : j < vs.length), rdW s2.dmem (A (s.regs.rsp.toNat + 8 * (ctx.nl + j))) = some vs[j]) →
        Ev Q s2 (at_ (k + m)) := by
      intro m s2 hc2 hlen r1 r2 r3 r4 hO hr hri hm hmi hsl2
      refine ih (i + 1) (k + m) s2 hc2 (by omega) hoff (by rw [r4]; exact h15) (by rw [r1]; exact hlo)
        (by rw [r1]; exact hhis) (fun x hx => hO.grows _ (hmap x hx)) (fun j hj => by rw [r1]; exact hsl2 j hj)
        ?_ ?_ (fun j hj => hw j (by omega)) ?_
      · intro j hj hjm
        by_cases hji : j = i
        · subst hji; rw [hw _ (Nat.le_refl _)]; exact hri hjm
        · rw [hr j hji hjm]; exact hpre j (by omega) hjm
      · intro j h1 h2
        by_cases hji : j = i
        · subst hji; rw [hw _ (Nat.le_refl _)]; exact hmi h1
        · rw [hm j hji h1 (by omega)]; exact hpm j h1 (by omega)
      · intro s' q1 q2 q3 q4 hO' hR hM
        refine ev_congr (h s' (q1.trans r1) (q2.trans r2) (q3.trans r3) (q4.trans r4) (hO.trans hO' (Nat.le_refl _) (Nat.le_refl _))
          (fun j hj => hR j (by omega)) (fun j h1 h2 => hM j h1 (by omega))) (by rw [hlen]; omega)
    by_cases him : i < maxRes
    · simp only [him, if_true, List.singleton_append] at hc
      have hstep : ∀ v : Word, v = vs.getD i 0 →
          Ev Q { s with regs := s.regs.set64 (resReg i) v.toBitVec } (at_ (k + 1)) := by
        intro v hv
        obtain ⟨h1, h2, h3, h4⟩ := resReg_keeps s.regs i v.toBitVec
        refine hnext 1 _ hc.tail (by simp [loadRes, him]; omega) h1 h2 h3 h4 (Only.refl _ _ _)
          (fun j hj hjm => by rw [rres_set64_resReg _ him hjm, if_neg hj])
          (fun _ => by rw [rres_set64_resReg _ him him, if_pos rfl]; simp [hv])
          (fun _ _ _ _ => rfl) (fun h => absurd h (by omega)) hsl
      by_cases hi : i < vs.length
      · simp only [hi, if_true] at hc
        refine ev_movRM hc.head ⟨by omega, by omega⟩ (v := vs[i]) ?_ (hstep _ (by simp [hi]))
        rw [slot_addr _ (ctx.nl + i) _ (by omega)]; exact hsl i hi
      · simp only [hi, if_false] at hc
        exact ev_movRI hc.head (hstep 0 (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi)]; rfl))
    · simp only [him, if_false] at hc
      have hcell := resAddr_cell (G := G) (i := i) (by omega) (by omega)
      have hcellv : ∀ (j : Nat), j < vs.length → s.regs.rsp.toNat + 8 * (ctx.nl + j) + 8 ≤ G.resAddr i ∨
          G.resAddr i + 8 ≤ s.regs.rsp.toNat + 8 * (ctx.nl + j) := fun j hj =>
        hG.res_stack_disj hcell fun t ht => ⟨by omega, by omega⟩
      have hend : G.resAddr i + 8 ≤ 2 ^ 64 := by
        have := hG.tab_end; simp only [Layout.tabEnd, Tab.nxres] at this
        simp only [Layout.resAddr]; omega
      have hroff : SmallOff (G.tab.resOff i) := by
        rw [Tab.resOff, Tab.resBase]; simp only [Tab.nxres] at hres; constructor <;> omega
      have hmapped : (rdW s.dmem (A (G.resAddr i))).isSome :=
        isSome_rdW fun t ht => by rw [A_add]; exact hmap _ (hcell t ht)
      -- the write of `v` to the slot
      have hwr : ∀ (m : Nat) (s2 : MachineData) (v : BitVec 64), UInt64.ofBitVec v = vs.getD i 0 →
          Code (loadRes ctx vs.length (i + 1) n) (k + m) →
          (loadRes ctx vs.length i (n + 1)).length = m + (loadRes ctx vs.length (i + 1) n).length →
          s2.dmem = wrW s.dmem (A (G.resAddr i)) v →
          s2.regs.rsp = s.regs.rsp → s2.regs.rbp = s.regs.rbp → s2.regs.r14 = s.regs.r14 →
          s2.regs.r15 = s.regs.r15 → (∀ j, rres s2.regs j = rres s.regs j) → Ev Q s2 (at_ (k + m)) := by
        intro m s2 v hv hc2 hlen hd r1 r2 r3 r4 hr
        refine hnext m s2 hc2 hlen r1 r2 r3 r4 ?_ (fun j _ _ => hr j) (fun h => absurd h him) ?_ ?_ ?_
        · rw [hd]
          refine (Only.wrW hend).mono ?_ ?_ <;> simp only [Layout.resAddr, Tab.nxres] <;> omega
        · intro j hji h1 h2
          rw [hd, rdW_wrW_A hend (by simp only [Layout.resAddr] at hend ⊢; omega)
            (by simp only [Layout.resAddr]; omega)]
        · intro _; rw [hd, rdW_wrW_same]; simp [hv]
        · intro j hj
          rw [hd, rdW_wrW_A hend (by omega) (hcellv j hj)]; exact hsl j hj
      by_cases hi : i < vs.length
      · simp only [hi, if_true, List.cons_append, List.nil_append] at hc
        refine ev_movRM hc.head ⟨by omega, by omega⟩ (v := vs[i]) ?_ ?_
        · rw [slot_addr _ (ctx.nl + i) _ (by omega)]; exact hsl i hi
        refine ev_movMR (hT ▸ hc.tail.head) hroff ?_ ?_
        · rw [res_addr (by simpa using h15)]; exact hmapped
        rw [res_addr (by simpa using h15)]
        exact hwr 2 _ _ (by simp [hi]) hc.tail.tail (by simp [loadRes, him, hi]; omega) rfl rfl rfl rfl rfl
          (fun j => rres_set64_rcx _ _ j)
      · simp only [hi, if_false, List.singleton_append] at hc
        refine ev_movMI (hT ▸ hc.head) hroff ?_ ?_
        · rw [res_addr h15]; exact hmapped
        rw [res_addr h15]
        exact hwr 1 _ _ (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi)]; rfl)
          hc.tail (by simp [loadRes, him, hi]; omega) rfl rfl rfl rfl rfl (fun _ => rfl)

/-- Storing results `i, i + 1, …` into the locals `xs`. -/
theorem sim_storeRes {G : Layout} (hG : G.Ok) (nl F : Nat) (Q : MachineState → Prop)
    (hres : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres < 2 ^ 31) :
    ∀ (xs : List Var) (i k : Nat) (σ : St) (rs : List Word) (s : MachineData),
    Code (storeRes G.tab xs i) k → xs.all (· < nl) = true → i + xs.length ≤ G.tab.nres → 8 * nl < 2 ^ 31 →
    Inv G nl F σ s → (∀ j < xs.length, i + j < maxRes → rres s.regs (i + j) = rs.getD j 0) →
    (∀ j < xs.length, maxRes ≤ i + j → rdW s.dmem (A (G.resAddr (i + j))) = some (rs.getD j 0)) →
    (∀ s', Inv G nl F (σ.setLocs xs rs) s' → s'.regs.rsp = s.regs.rsp → s'.regs.rbp = s.regs.rbp →
      s'.regs.r14 = s.regs.r14 → s'.regs.r15 = s.regs.r15 →
      Pres G (top s F) s.dmem s'.dmem → Ev Q s' (at_ (k + (storeRes G.tab xs i).length))) →
    Ev Q s (at_ k) := by
  intro xs
  induction xs with
  | nil =>
    intro i k σ rs s _ _ _ _ hI _ _ h
    exact ev_congr (h s hI rfl rfl rfl rfl (Pres.refl _ _)) (by simp [storeRes])
  | cons x xs ih =>
    intro i k σ rs s hc hxs hn hoff hI hres' hrm h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hxs
    simp only [storeRes] at hc
    have hx := hxs.1
    have := hI.nlF
    have hhi := hI.hi
    have hhi2 := hG.hi_le
    have hlo := hI.lo
    -- after storing `v` into `x`
    have hnext : ∀ (m : Nat) (s1 : MachineData) (v : Word), v = rs.headD 0 →
        Code (storeRes G.tab xs (i + 1)) (k + m) →
        (storeRes G.tab (x :: xs) i).length = m + (storeRes G.tab xs (i + 1)).length →
        s1.regs.rsp = s.regs.rsp → s1.regs.rbp = s.regs.rbp → s1.regs.r14 = s.regs.r14 →
        s1.regs.r15 = s.regs.r15 → (∀ j, rres s1.regs j = rres s.regs j) → s1.dmem = s.dmem →
        Ev Q { s1 with dmem := wrW s1.dmem (A (s1.regs.rsp.toNat + 8 * x)) v.toBitVec } (at_ (k + m)) := by
      intro m s1 v hv hc2 hlen r1 r2 r3 r4 hr hd
      have hI1 : Inv G nl F σ s1 := hI.of_regs hd r1 r4
      have hI2 := hI1.setLoc hG hx v
      have hsp := congrArg UInt64.toNat r1
      refine ih (i + 1) (k + m) _ rs.tail _ hc2 hxs.2 (by simp at hn; omega) hoff hI2 ?_ ?_ ?_
      · intro j hj hjm
        have := hres' (j + 1) (by simp; omega) (by omega)
        rw [show i + 1 + j = i + (j + 1) by omega]
        simp only at this ⊢
        rw [hr, this]
        cases rs <;> simp
      · intro j hj hjm
        have := hrm (j + 1) (by simp; omega) (by omega)
        have hcell := resAddr_cell (G := G) (i := i + (j + 1)) (by omega) (by simp at hn; omega)
        have hte := hG.tab_end; simp only [Layout.tabEnd, Tab.nxres] at hte
        simp only
        rw [show i + 1 + j = i + (j + 1) by omega, rdW_wrW_A (by lomega)
          (by simp only [Layout.resAddr]; simp at hn; omega)
          (hG.res_stack_disj hcell fun t ht => ⟨by lomega, by lomega⟩).symm, hd, this]
        cases rs <;> simp
      · intro s' hI' q1 q2 q3 q4 hP
        have hw : Pres G (top s F) s.dmem (wrW s1.dmem (A (s1.regs.rsp.toNat + 8 * x)) v.toBitVec) := by
          rw [hd, hsp]; exact Pres.of_only (Only.wrW (by lomega)) (by omega) (by simp only [top]; lomega)
        refine ev_congr (h s' (by simpa [St.setLocs, hv] using hI') (q1.trans r1) (q2.trans r2) (q3.trans r3)
          (q4.trans r4) (hw.trans (by simpa [top, r1] using hP))) (by rw [hlen]; omega)
    by_cases him : i < maxRes
    · simp only [him, if_true, List.singleton_append] at hc
      refine ev_movMR hc.head ⟨by lomega, by lomega⟩ ?_ ?_
      · rw [slot_addr _ x _ (by omega)]; exact hI.mapped (by lomega)
      rw [slot_addr _ x _ (by omega)]
      have hv : s.regs.get64 (resReg i) = (rs.headD 0).toBitVec := by
        have h0 := hres' 0 (by simp) (by omega)
        rw [Nat.add_zero] at h0
        rw [← rres_eq_get64 _ him, h0]
        cases rs <;> rfl
      rw [hv]
      exact hnext 1 s (rs.headD 0) rfl hc.tail (by simp [storeRes, him]; omega) rfl rfl rfl rfl
        (fun _ => rfl) rfl
    · simp only [him, if_false, List.cons_append, List.nil_append] at hc
      have hroff : SmallOff (G.tab.resOff i) := by
        rw [Tab.resOff, Tab.resBase]; simp only [Tab.nxres] at hres hn ⊢; simp at hn; constructor <;> omega
      refine ev_movRM hc.head hroff (v := rs.headD 0) ?_ ?_
      · rw [res_addr hI.r15]; have := hrm 0 (by simp) (by omega); rw [Nat.add_zero] at this
        rw [this]; cases rs <;> rfl
      refine ev_movMR hc.tail.head ⟨by lomega, by lomega⟩ ?_ ?_
      · rw [slot_addr _ x _ (by omega)]; exact hI.mapped (by lomega)
      rw [slot_addr _ x _ (by omega)]
      exact ev_congr (hnext 2 { s with regs := s.regs.set64 .rcx (rs.headD 0).toBitVec } (rs.headD 0) rfl
        hc.tail.tail (by simp [storeRes, him]; omega) rfl rfl rfl rfl (fun j => rres_set64_rcx _ _ j) rfl) rfl

/-- Zeroing the locals `xs`. -/
theorem sim_zeroVars {G : Layout} (hG : G.Ok) (nl F : Nat) (Q : MachineState → Prop) :
    ∀ (xs : List Var) (k : Nat) (σ : St) (s : MachineData),
    Code (zeroVars xs) k → xs.all (· < nl) = true → 8 * nl < 2 ^ 31 → Inv G nl F σ s →
    (∀ s', Inv G nl F (σ.setLocs xs []) s' → s'.regs = s.regs →
      Pres G (top s F) s.dmem s'.dmem → Ev Q s' (at_ (k + xs.length))) →
    Ev Q s (at_ k) := by
  intro xs
  induction xs with
  | nil =>
    intro k σ s _ _ _ hI h
    exact ev_congr (h s hI rfl (Pres.refl _ _)) (by simp)
  | cons x xs ih =>
    intro k σ s hc hxs hoff hI h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hxs
    simp only [zeroVars] at hc
    have hx := hxs.1
    have := hI.nlF
    have hhi := hI.hi
    have hhi2 := hG.hi_le
    have hlo := hI.lo
    refine ev_movMI hc.head ⟨by lomega, by lomega⟩ ?_ ?_
    · rw [slot_addr _ x _ (by omega)]; exact hI.mapped (by lomega)
    rw [slot_addr _ x _ (by omega)]
    have hI2 := hI.setLoc hG hx 0
    have h0 : (Int64.ofInt 0).toBitVec = (0 : Word).toBitVec := rfl
    rw [h0]
    refine ih (k + 1) _ _ hc.tail hxs.2 hoff hI2 ?_
    intro s' hI' hr hP
    refine ev_congr (h s' (by simpa [St.setLocs] using hI') hr ?_) (by simp; omega)
    have hw : Pres G (top s F) s.dmem (wrW s.dmem (A (s.regs.rsp.toNat + 8 * x)) (0 : Word).toBitVec) :=
      Pres.of_only (Only.wrW (by lomega)) (by omega) (by simp only [top]; lomega)
    exact hw.trans (by simpa [top] using hP)

theorem zeroVars_length (xs : List Var) : (zeroVars xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [zeroVars, ih]

/-- A call's results: the callee's `c` of them, then zeroes. -/
theorem St.setLocs_take_drop (xs : List Var) (σ : St) (r : List Word) (c : Nat) (h : r.length ≤ c) :
    σ.setLocs xs r = (σ.setLocs (xs.take c) r).setLocs (xs.drop c) [] := by
  induction xs generalizing σ r c with
  | nil => simp [St.setLocs]
  | cons x xs ih =>
    cases c with
    | zero =>
      have : r = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simp [St.setLocs]
    | succ c =>
      simp only [List.take_succ_cons, List.drop_succ_cons, St.setLocs]
      exact ih _ _ _ (by simp; omega)

end
section
variable [Host] {G : Layout} (hG : G.Ok) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff) (p : Prog)
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
      (fun hr => hG.notStack_of_res hr ⟨by omega, by omega⟩)
      fun hg => hG.notStack_of_tab hg.tab ⟨by omega, by omega⟩

theorem sim_ret (K : Stmt → M Sig) (P : Nat → Prop) (es : List Expr) :
    SimS p G (stepRun p K) P (.ret es) := by
  intro ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨hargs, hlen⟩ := hwf
  simp only [compileS, List.append_assoc] at hc hK
  simp only [tempsS] at htmp
  have hF' := hF; simp only [maxOff] at hF'
  have hTab' := hTab; simp only [maxOff] at hTab'
  have hlenT := tempsArgs_ge 0 es
  refine sim_args hG hTab ctx hT F hF es 0 k hc.left hargs htmp σ d Q hI ?_ ?_
  · intro vs s1 hvs hE1 hslots
    have hvl := evalArgsP_length hvs
    have hI1 := hI.only hG (hE1.mem.mono (by omega) (Nat.le_refl _)) hE1.rsp hE1.r15
    have hc2 := hc.right
    rw [← hvl] at hc2
    have h1sp := congrArg UInt64.toNat hE1.rsp
    have hnr := hN.le
    have hnret : es.length ≤ ctx.nr := hN.ret
    refine sim_loadRes hG ctx hT vs vs Q (by omega) ctx.nr 0 _ s1 hc2.left (by omega)
      (by rw [hvl]; omega) hI1.r15 hI1.lo (by rw [h1sp, hvl]; have := hI.hi; omega)
      (fun x hx => hI1.mem.res x hx) (fun j hj => by rw [h1sp]; simpa [h1sp] using hslots j hj)
      (fun j hj => absurd hj (Nat.not_lt_zero _)) (fun j _ hj => absurd hj (Nat.not_lt_zero _))
      (fun _ _ => rfl) ?_
    intro s2 h1 h2 h3 h4 hO hR hM
    have hj := hc2.right
    refine ev_jmp hj.head (hK.ret vs σ s2 (by simp [step_ret_run, hvs]; rfl)
      (hI1.only_res hG hO (fun x a b => Layout.inRes_of a b) h1 h4) ((hE1.spost hI.lo).trans ?_)
      ⟨fun j hj => hR j (by omega), fun j h1 h2 => hM j h1 (by omega), by omega⟩)
    exact ⟨h1, h2, h4, by rw [h3]; exact Nat.le_refl _, Pres.of_res hO fun x a b => Layout.inRes_of a b⟩
  · intro s1 herr hE1
    obtain ⟨y, hy⟩ := herr
    refine hK.err s1 ⟨y, by simp [step_ret_run, hy]; rfl, by rw [evalArgsP_error hy]; simp⟩
      (hE1.spost hI.lo).gpost

theorem sim_call (t : NTree) (n : Nat) (hFun : FunSim p G t n)
    (hProg : ∀ f fd, p.lookup f = some fd → ∃ kf, Code (compileFn G.tab t f fd) kf)
    (xs : List Var) (f : FnName) (args : List Expr) :
    SimS p G (stepRun p (exec p n)) (· ≤ n) (.call xs f args) := by
  intro ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨⟨hxs, hxl⟩, hargs⟩, hfd⟩ := hwf
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
        have hTab' := hTab; simp only [maxOff] at hTab'
        have hcS := hcR.tail.tail.tail.tail
        have hcn : nrOf ctx.nrt ctx.tab f = Stmt.nret fd.body := hT ▸ hN.callee f fd hlk
        rw [hcn, hT] at hcS
        have hxl' : xs.length ≤ G.tab.nres := hxl
        have hxs1 : (xs.take (Stmt.nret fd.body)).all (· < ctx.nl) = true :=
          List.all_eq_true.mpr fun y hy => List.all_eq_true.mp hxs y (List.mem_of_mem_take hy)
        have hxs2 : (xs.drop (Stmt.nret fd.body)).all (· < ctx.nl) = true :=
          List.all_eq_true.mpr fun y hy => List.all_eq_true.mp hxs y (List.mem_of_mem_drop hy)
        have htk := List.length_take_le' (Stmt.nret fd.body) xs
        refine sim_storeRes hG ctx.nl F Q (by omega) _ 0 _ σ' r d' hcS.left hxs1
          (by rw [Nat.zero_add]; exact Nat.le_trans htk hxl') (by omega) hId
          (fun j hj hm => by rw [Nat.zero_add] at hm ⊢; exact hrax.1 j (by simp at hj; omega) hm)
          (fun j hj hm => by rw [Nat.zero_add] at hm ⊢; exact hrax.2.1 j hm (by simp at hj; omega)) ?_
        intro s1' hI1' p1 p2 p3 p4 hP1
        refine sim_zeroVars hG ctx.nl F Q _ _ _ s1' hcS.right hxs2 (by omega) hI1' ?_
        intro s' hI'' hr' hP2
        rw [← St.setLocs_take_drop xs σ' r _ hrax.2.2] at hI''
        have q1 : s'.regs.rsp = d'.regs.rsp := by rw [hr', p1]
        have q2 : s'.regs.rbp = d'.regs.rbp := by rw [hr', p2]
        have q3 : s'.regs.r14 = d'.regs.r14 := by rw [hr', p3]
        have q4 : s'.regs.r15 = d'.regs.r15 := by rw [hr', p4]
        have hP' : Pres G (top d' F) d'.dmem s'.dmem := hP1.trans (by simpa [top, p1] using hP2)
        refine ev_congr (hK.normal (σ'.setLocs xs r) _ ?_ hI'' ?_) ?_
        · rw [step_call_run, hvs]; simp only [hinv]
        · refine ⟨by rw [q1]; exact hrsp'', by rw [q2]; exact hrbp.trans hE1.rbp,
            by rw [q4]; exact hr15.trans hE1.r15, ?_, ?_⟩
          · show s'.regs.r14.toNat ≤ d.regs.r14.toNat
            rw [q3]
            have := congrArg UInt64.toNat hE1.r14
            have h1 : ({ toBitVec := s1.regs.r14.toBitVec - 1 } : UInt64).toNat = s1.regs.r14.toNat - 1 :=
              u64_sub_one_toNat hpos
            rw [h1] at hr14; omega
          · refine (Pres.of_only hE1.mem (by have := hI.lo; omega) (by simp only [top]; omega)).trans ?_
            refine (hpres1.mono (by simp only [top]; omega)).trans ?_
            refine (hpres.mono (by simp only [top]; omega)).trans ?_
            exact hP'.mono (by simp only [top]; rw [hrsp']; omega)
        · simp only [List.length_append, List.length_cons, zeroVars_length, hT, hN.callee f fd hlk]
          omega
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
