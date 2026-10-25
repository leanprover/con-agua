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

/-- The arguments `vs` of a call, where the callee finds them: at most 9 in the argument
registers, more in memory at `rsi`, outside the callee's frame. -/
def ArgsIn (G : Layout) (d : MachineData) (vs : List Word) : Prop :=
  (vs.length ≤ argRegs.length → ∀ i (h : i < vs.length), d.regs.get64 (argRegs.getD i .rax) = vs[i].toBitVec) ∧
  (argRegs.length < vs.length →
    (∀ i (h : i < vs.length), rdW d.dmem (A (d.regs.rsi.toNat + 8 * i)) = some vs[i]) ∧
    (d.regs.rsp.toNat + 8 ≤ d.regs.rsi.toNat ∨ d.regs.rsi.toNat + 8 * vs.length ≤ G.lo) ∧
    d.regs.rsi.toNat + 8 * vs.length < 2 ^ 64)

/-- The simulation of every call of a function of `p` under `exec p n`, with fewer than `n` units
of machine fuel. -/
def FunSim [Host] (p : Prog) (G : Layout) (t : NTree) (n : Nat) : Prop :=
  ∀ (f : FnName) (fd : FunDecl) (kf : Nat), p.lookup f = some fd → Code (compileFn G.tab t f fd) kf →
  ∀ (vs : List Word) (σ : St) (d : MachineData) (ra : Word) (Q : MachineState → Prop),
    vs.length = fd.nparams →
    rdW d.dmem (A d.regs.rsp.toNat) = some ra → ArgsIn G d vs →
    G.lo ≤ d.regs.rsp.toNat → d.regs.rsp.toNat + 8 ≤ G.hi →
    d.regs.r15.toNat = G.T → MemRel G σ.mem d.dmem → d.regs.r14.toNat < n →
    (∀ r σ' d', (invoke p (exec p n) f vs).run σ = .ok (r, σ') → MemRel G σ'.mem d'.dmem →
      σ'.loc = σ.loc → d'.regs.rsp.toNat = d.regs.rsp.toNat + 8 → d'.regs.rbp = d.regs.rbp →
      d'.regs.r15 = d.regs.r15 → d'.regs.r14.toNat ≤ d.regs.r14.toNat → ResOut G (Stmt.nret fd.body) r d' →
      Pres G d.regs.rsp.toNat d.dmem d'.dmem → Ev Q d' (Int64.ofBitVec ra.toBitVec)) →
    (∀ d', (∃ x, (invoke p (exec p n) f vs).run σ = .error x ∧ x.plain) →
      GPost G d.regs.rsp.toNat d d' → Ev Q d' (label errorL)) →
    (∀ d' k, (invoke p (exec p n) f vs).run σ = .error (.abort k) →
      GPost G d.regs.rsp.toNat d d' → d'.regs.rbx = k → Ev Q d' (label abortL)) →
    (∀ d', GPost G d.regs.rsp.toNat d d' → Ev Q d' (label exhaustedL)) →
    Ev Q d (at_ kf)

theorem bv_sub8 (x : UInt64) (h : 8 ≤ x.toNat) : x.toBitVec - 8 = A (x.toNat - 8) := by
  apply BitVec.eq_of_toNat_eq
  simp [A, BitVec.toNat_sub]
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
    (0 < vs.length → 8 * (ctx.nl + vs.length) < 2 ^ 31) → s.regs.r15.toNat = G.T → G.lo ≤ s.regs.rsp.toNat →
    (0 < vs.length → s.regs.rsp.toNat + 8 * (ctx.nl + vs.length) ≤ G.hi) →
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
        have hoff := hoff (by omega)
        refine ev_movRM hc.head ⟨by omega, by omega⟩ (v := vs[i]) ?_ (hstep _ (by simp [hi]))
        rw [slot_addr _ (ctx.nl + i) _ (by omega)]; exact hsl i hi
      · simp only [hi, if_false] at hc
        exact ev_movRI hc.head (hstep 0 (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi)]; rfl))
    · simp only [him, if_false] at hc
      have hcell := resAddr_cell (G := G) (i := i) (by omega) (by omega)
      have hcellv : ∀ (j : Nat), j < vs.length → s.regs.rsp.toNat + 8 * (ctx.nl + j) + 8 ≤ G.resAddr i ∨
          G.resAddr i + 8 ≤ s.regs.rsp.toNat + 8 * (ctx.nl + j) := fun j hj => by
        have := hhis (by omega)
        exact hG.res_stack_disj hcell fun t ht => ⟨by omega, by omega⟩
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
        have hoff := hoff (by omega)
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
theorem sim_storeRes {G : Layout} (hG : G.Ok) (ctx : Ctx) (hal : ctx.alloc = []) (htn : ctx.treg = none) (F : Nat) (Q : MachineState → Prop)
    (hres : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres < 2 ^ 31) :
    ∀ (xs : List Var) (i k : Nat) (σ : St) (rs : List Word) (s : MachineData),
    Code (storeRes G.tab xs i) k → xs.all (· < ctx.nl) = true → i + xs.length ≤ G.tab.nres → 8 * ctx.nl < 2 ^ 31 →
    Inv G ctx F σ s → (∀ j < xs.length, i + j < maxRes → rres s.regs (i + j) = rs.getD j 0) →
    (∀ j < xs.length, maxRes ≤ i + j → rdW s.dmem (A (G.resAddr (i + j))) = some (rs.getD j 0)) →
    (∀ s', Inv G ctx F (σ.setLocs xs rs) s' → s'.regs.rsp = s.regs.rsp → s'.regs.rbp = s.regs.rbp →
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
    have := hI.slot x hx (by simp [hal])
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
      have hI1 : Inv G ctx F σ s1 := hI.of_regs0 hal hd r1 r4 (fun h => absurd htn h)
      have hI2 := hI1.setLoc hG hx (by simp [hal]) v (by simp [htn])
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
theorem sim_zeroVars {G : Layout} (hG : G.Ok) (ctx : Ctx) (hal : ctx.alloc = []) (htn : ctx.treg = none) (F : Nat) (Q : MachineState → Prop) :
    ∀ (xs : List Var) (k : Nat) (σ : St) (s : MachineData),
    Code (zeroVars xs) k → xs.all (· < ctx.nl) = true → 8 * ctx.nl < 2 ^ 31 → Inv G ctx F σ s →
    (∀ s', Inv G ctx F (σ.setLocs xs []) s' → s'.regs = s.regs →
      Pres G (top s F) s.dmem s'.dmem → Ev Q s' (at_ (k + xs.length))) →
    Ev Q s (at_ k) := by
  intro xs
  induction xs with
  | nil =>
    exact fun k σ s _ _ _ hI h => ev_congr (h s hI rfl (Pres.refl _ _)) (by simp)
  | cons x xs ih =>
    intro k σ s hc hxs hoff hI h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hxs
    simp only [zeroVars] at hc
    have hx := hxs.1
    have := hI.slot x hx (by simp [hal])
    have hhi := hI.hi
    have hhi2 := hG.hi_le
    have hlo := hI.lo
    refine ev_movMI hc.head ⟨by lomega, by lomega⟩ ?_ ?_
    · rw [slot_addr _ x _ (by omega)]; exact hI.mapped (by lomega)
    rw [slot_addr _ x _ (by omega)]
    have hI2 := hI.setLoc hG hx (by simp [hal]) 0 (by simp [htn])
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
theorem resReg_alloc {j : Nat} (h1 : 1 ≤ j) (h2 : j < maxRes) : resReg j ∈ allocRegs := by
  simp only [maxRes] at h2
  have : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [resReg, allocRegs, argRegs]

theorem resReg_inj {i j : Nat} (hi : i < maxRes) (hj : j < maxRes) (h : resReg i = resReg j) : i = j := by
  simp only [maxRes] at hi hj
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [resReg]

theorem zeroRes_length (i n : Nat) : (zeroRes i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [zeroRes, ih]

section
variable [Host] {G : Layout} (hG : G.Ok) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff) (p : Prog)
include hG hTab

omit hG hTab in
/-- Results `i, …, i + n - 1` (registers) set to `0`. -/
theorem sim_zeroRes (Q : MachineState → Prop) :
    ∀ (n i k : Nat) (s : MachineData), Code (zeroRes i n) k → i + n ≤ maxRes →
    (∀ s', s'.dmem = s.dmem → s'.regs.rsp = s.regs.rsp → s'.regs.rbp = s.regs.rbp →
      s'.regs.r14 = s.regs.r14 → s'.regs.r15 = s.regs.r15 →
      (∀ j, i ≤ j → j < i + n → rres s'.regs j = 0) →
      (∀ j < maxRes, (j < i ∨ i + n ≤ j) → rres s'.regs j = rres s.regs j) →
      Ev Q s' (at_ (k + n))) → Ev Q s (at_ k) := by
  intro n
  induction n with
  | zero =>
    exact fun i k s _ _ h => h s rfl rfl rfl rfl rfl (fun j h1 h2 => absurd h2 (by omega)) (fun _ _ _ => rfl)
  | succ n ih =>
    intro i k s hc hn h
    simp only [zeroRes] at hc
    refine ev_movRI hc.head ?_
    obtain ⟨h1, h2, h3, h4⟩ := resReg_keeps s.regs i (0 : Word).toBitVec
    refine ih (i + 1) (k + 1) _ hc.tail (by omega) ?_
    intro s' hd q1 q2 q3 q4 hz hk
    refine ev_congr (h s' hd (q1.trans h1) (q2.trans h2) (q3.trans h3) (q4.trans h4) ?_ ?_) (by omega)
    · intro j hj1 hj2
      by_cases hji : j = i
      · subst hji
        rw [hk j (by omega) (.inl (by omega)), rres_set64_resReg _ (by omega) (by omega), if_pos rfl]
      · exact hz j (by omega) (by omega)
    · intro j hj hor
      rw [hk j hj (by omega), rres_set64_resReg _ (by omega) hj, if_neg (by omega)]

/-- Arguments into the registers `rs`, in a function that keeps no locals in registers, with
scratch `fr`. -/
theorem sim_regArgs (ctx : Ctx) (hT : ctx.tab = G.tab) (F : Nat) (hF : 8 * F + 8 < maxOff)
    (hal : ctx.alloc = []) (htn : ctx.treg = none) :
    ∀ (args : List Expr) (fr rs : List Reg64) (k : Nat), args.length ≤ rs.length → (∀ r ∈ rs, r ∈ allocRegs) →
    rs.Nodup → (∀ r ∈ fr, r ∈ ctx.pool) → fr.Nodup → Code (compileRegArgs ctx fr rs args) k →
    args.all (Expr.wf ctx.nl G.tab) = true → TmpFit ctx.nl F 0 (tempsEs args) →
    ∀ (σ : St) (s : MachineData) (Q : MachineState → Prop), Inv G ctx F σ s →
    (∀ vs s', evalArgsP σ args = .ok vs → RPost ctx.nl F (fun r => r ∈ rs ∨ r ∈ fr) s s' → Inv G ctx F σ s' →
      (∀ i (h : i < vs.length), s'.regs.get64 (rs.getD i .rax) = vs[i].toBitVec) →
      Ev Q s' (at_ (k + (compileRegArgs ctx fr rs args).length))) →
    (∀ s', (∃ x, evalArgsP σ args = .error x) → RPost ctx.nl F (fun r => r ∈ rs ∨ r ∈ fr) s s' →
      Ev Q s' (label errorL)) →
    Ev Q s (at_ k) := by
  intro args
  induction args with
  | nil =>
    intro fr rs k _ _ _ _ _ _ _ _ σ s Q hI hok _
    exact ev_congr (hok [] s rfl (RPost.refl _ _ _ _) hI (fun i h => absurd h (by simp)))
      (by cases rs <;> simp [compileRegArgs])
  | cons e es ih =>
    intro fr rs k hlen hrs hnd hfr hfn hc hwf htmp σ s Q hI hok herr
    cases rs with
    | nil => simp at hlen
    | cons r rs =>
    simp only [List.all_cons, Bool.and_eq_true] at hwf
    simp only [tempsEs] at htmp
    simp only [compileRegArgs] at hc hok
    have hr := hrs r List.mem_cons_self
    have hne := allocRegs_ne hr
    have hnr : r ∉ rs := (List.nodup_cons.mp hnd).1
    have hfr' : ∀ r' ∈ fr.filter (· != r), r' ∈ ctx.pool := fun r' h => hfr r' (mem_filter_sub r' h)
    have hfn' : (fr.filter (· != r)).Nodup := List.Nodup.sublist List.filter_sublist hfn
    have hW : ∀ r', (r' = r ∨ r' ∈ fr.filter (· != r)) → r' ∈ r :: rs ∨ r' ∈ fr := fun r' h =>
      h.elim (fun h => .inl (h ▸ List.mem_cons_self)) (fun h => .inr (mem_filter_sub r' h))
    refine sim_valInto hG hTab ctx hT F hF hr (fun h => absurd htn h) hfr' hfn' (by simp) e k hc.left hwf.1
      (fun _ => htmp.mono (Nat.le_max_left _ _)) σ s Q hI ?_
      (fun s' he hR => herr s' (by obtain ⟨x, hx⟩ := he; exact ⟨x, by simp [evalArgsP, hx]; rfl⟩)
        (hR.mono hW))
    intro v s1 hv hr1 hR1 hI1
    rw [hal, St.setReg_nil] at hI1
    refine ih (fr.filter (· != r)) rs _ (by simp at hlen; omega) (fun r' h => hrs r' (List.mem_cons_of_mem _ h))
      (List.nodup_cons.mp hnd).2 hfr' hfn' hc.right hwf.2 (htmp.mono (Nat.le_max_right _ _)) σ s1 Q hI1 ?_ ?_
    · intro vs s2 hvs hR2 hI2 hregs
      refine ev_congr (hok (v :: vs) s2 (by simp [evalArgsP, hv, hvs]; rfl)
        ((hR1.trans hR2).mono fun r' h => h.elim (hW r') (fun h => h.elim
          (fun h => .inl (List.mem_cons_of_mem _ h)) (fun h => .inr (mem_filter_sub r' h)))) hI2 ?_) ?_
      · intro i hi
        cases i with
        | zero =>
          simp only [List.getD_cons_zero, List.getElem_cons_zero]
          rw [hR2.keep r hne.1 hne.2.1 hne.2.2.1 (fun h => h.elim hnr (fun h => by simp at h))]; exact hr1
        | succ i => simpa using hregs i (by simpa using hi)
      · simp only [List.length_append]; omega
    · exact fun s2 ⟨x, hx⟩ hR2 => herr s2 ⟨x, by simp [evalArgsP, hv, hx]; rfl⟩
        ((hR1.trans hR2).mono fun r' h => h.elim (hW r') (fun h => h.elim
          (fun h => .inl (List.mem_cons_of_mem _ h)) (fun h => .inr (mem_filter_sub r' h))))

/-- Results `i, i + 1, …` of a `return` straight into their registers (`retRegs`), with scratch
`fr` and ghost states: the values do not read the registers written before them (`retSafe`). -/
theorem sim_retRegs (ctx : Ctx) (hT : ctx.tab = G.tab) (F : Nat) (hF : 8 * F + 8 < maxOff)
    (σ0 : St) (e0 : Expr) (Q : MachineState → Prop) :
    ∀ (rest : List Expr) (fr : List Reg64) (i k : Nat) (σ : St) (s : MachineData),
    (∀ r ∈ fr, r ∈ ctx.pool) → fr.Nodup →
    Code (retRegs ctx fr i rest) k → rest.all (Expr.wf ctx.nl G.tab) = true → TmpFit ctx.nl F 0 (tempsRR ctx.g fr i rest) →
    1 ≤ i → i + rest.length ≤ maxRes → retSafe ctx.alloc e0 i rest = true →
    Inv G ctx F σ s → σ.mem = σ0.mem → evalP σ e0 = evalP σ0 e0 → (∀ e ∈ rest, evalP σ e = evalP σ0 e) →
    (∀ vs σ' s', evalArgsP σ0 rest = .ok vs → Inv G ctx F σ' s' → σ'.mem = σ0.mem →
      evalP σ' e0 = evalP σ0 e0 →
      RPost ctx.nl F (fun r => (∃ j, i ≤ j ∧ j < i + rest.length ∧ r = resReg j) ∨ r ∈ fr) s s' →
      (∀ j (h : j < vs.length), s'.regs.get64 (resReg (i + j)) = vs[j].toBitVec) →
      Ev Q s' (at_ (k + (retRegs ctx fr i rest).length))) →
    (∀ s', (∃ x, evalArgsP σ0 rest = .error x) →
      RPost ctx.nl F (fun r => (∃ j, i ≤ j ∧ j < i + rest.length ∧ r = resReg j) ∨ r ∈ fr) s s' →
      Ev Q s' (label errorL)) →
    Ev Q s (at_ k) := by
  intro rest
  induction rest with
  | nil =>
    intro fr i k σ s _ _ _ _ _ _ _ _ hI hm he0 _ hok _
    exact ev_congr (hok [] σ s rfl hI hm he0 (RPost.refl _ _ _ _) (fun j h => absurd h (by simp)))
      (by simp [retRegs])
  | cons e rest ih =>
    intro fr i k σ s hfr hfn hc hwf htmp hi1 hin hsafe hI hm he0 hes hok herr
    simp only [List.all_cons, Bool.and_eq_true] at hwf
    simp only [tempsRR, genInto_g] at htmp
    simp only [retRegs] at hc hok
    simp only [retSafe, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at hsafe
    simp only [List.length_cons] at hin
    have hr := resReg_alloc (j := i) hi1 (by omega)
    have hne := allocRegs_ne hr
    have hev : evalP σ e = evalP σ0 e := hes e List.mem_cons_self
    have hfr' : ∀ r' ∈ fr.filter (· != resReg i), r' ∈ ctx.pool := fun r' h => hfr r' (mem_filter_sub r' h)
    have hfn' : (fr.filter (· != resReg i)).Nodup := List.Nodup.sublist List.filter_sublist hfn
    have hW : ∀ r', (r' = resReg i ∨ r' ∈ fr.filter (· != resReg i)) →
        (∃ j, i ≤ j ∧ j < i + (rest.length + 1) ∧ r' = resReg j) ∨ r' ∈ fr := fun r' h =>
      h.elim (fun h => .inl ⟨i, Nat.le_refl _, by omega, h⟩) (fun h => .inr (mem_filter_sub r' h))
    refine sim_valInto hG hTab ctx hT F hF hr (fun _ => by unfold resReg; split <;> decide) hfr' hfn' (by simp)
      e k hc.left hwf.1 (fun h => htmp.mono (by simp only [h, Option.isSome_none, Bool.false_eq_true, ite_false]; omega)) σ s Q hI ?_
      (fun s' he hR => herr s' (by obtain ⟨x, hx⟩ := he; rw [hev] at hx; exact ⟨x, by simp [evalArgsP, hx]; rfl⟩)
        (hR.mono fun r' h => by simpa using hW r' h))
    intro v s1 hv hr1 hR1 hI1
    have hnr : ∀ e' ∈ e0 :: rest, Expr.readsReg ctx.alloc (resReg i) e' = false := fun e' h => by
      have := hsafe.1 e' h; simpa using this
    have hv0 : evalP σ0 e = .ok v := hev ▸ hv
    have hW2 : ∀ r', ((∃ j, i + 1 ≤ j ∧ j < i + 1 + rest.length ∧ r' = resReg j) ∨ r' ∈ fr.filter (· != resReg i)) →
        (∃ j, i ≤ j ∧ j < i + (rest.length + 1) ∧ r' = resReg j) ∨ r' ∈ fr := fun r' h =>
      h.elim (fun ⟨j, h1, h2, h3⟩ => .inl ⟨j, by omega, by omega, h3⟩) (fun h => .inr (mem_filter_sub r' h))
    refine ih (fr.filter (· != resReg i)) (i + 1) _ (σ.setReg ctx.alloc (resReg i) v) s1 hfr' hfn' hc.right hwf.2
      (htmp.mono (Nat.le_max_right _ _)) (by omega) (by omega) hsafe.2 hI1 hm
      (by rw [evalP_setReg _ (hnr e0 List.mem_cons_self), he0])
      (fun e' h => by rw [evalP_setReg _ (hnr e' (List.mem_cons_of_mem _ h)), hes e' (List.mem_cons_of_mem _ h)])
      ?_ ?_
    · intro vs σ' s2 hvs hI2 hm2 he2 hR2 hregs
      refine ev_congr (hok (v :: vs) σ' s2 (by simp [evalArgsP, hv0, hvs]; rfl) hI2 hm2 he2
        ((hR1.trans hR2).mono fun r' h => by
          simpa using h.elim (hW r') (hW2 r')) ?_) ?_
      · intro j hj
        cases j with
        | zero =>
          simp only [Nat.add_zero, List.getElem_cons_zero]
          rw [hR2.keep _ hne.1 hne.2.1 hne.2.2.1 fun h => h.elim (fun ⟨j', h1, h2, h3⟩ => by
            have := resReg_inj (by omega) (by omega) h3; omega) (fun h => by simp at h)]
          exact hr1
        | succ j =>
          have := hregs j (by simpa using hj)
          simpa [show i + 1 + j = i + (j + 1) by omega] using this
      · simp only [List.length_append]; omega
    · exact fun s2 ⟨x, hx⟩ hR2 => herr s2 ⟨x, by simp [evalArgsP, hv0, hx]; rfl⟩
        ((hR1.trans hR2).mono fun r' h => by simpa using h.elim (hW r') (hW2 r'))

omit [Host] hG hTab in
/-- The scratch registers left after `retRegs` hold no result register it wrote. -/
theorem retFree_sub : ∀ (rest : List Expr) (fr : List Reg64) (i : Nat) (r : Reg64), r ∈ retFree fr i rest →
    r ∈ fr ∧ ∀ j, i ≤ j → j < i + rest.length → r ≠ resReg j
  | [], fr, i, r, h => ⟨h, fun j h1 h2 => absurd h2 (by simp; omega)⟩
  | _ :: rest, fr, i, r, h => by
    obtain ⟨h1, h2⟩ := retFree_sub rest _ (i + 1) r h
    simp only [List.mem_filter, bne_iff_ne, ne_eq] at h1
    refine ⟨h1.1, fun j hj1 hj2 => ?_⟩
    rcases Nat.eq_or_lt_of_le hj1 with rfl | hj
    · exact h1.2
    · exact h2 j hj (by simp at hj2; omega)

omit [Host] hG hTab in
theorem retFree_sublist : ∀ (rest : List Expr) (fr : List Reg64) (i : Nat), (retFree fr i rest).Sublist fr
  | [], fr, i => List.Sublist.refl fr
  | _ :: rest, fr, i => (retFree_sublist rest _ (i + 1)).trans List.filter_sublist

/-- `rax := e` (`valRax`) with scratch `fr`. -/
theorem sim_valRax (ctx : Ctx) (hT : ctx.tab = G.tab) (F : Nat) (hF : 8 * F + 8 < maxOff)
    {fr : List Reg64} (hfr : ∀ r' ∈ fr, r' ∈ ctx.pool) (hfn : fr.Nodup) (hrf : Reg64.rax ∉ fr)
    (e : Expr) (k : Nat) (hc : Code (valRax ctx fr e) k)
    (hwf : Expr.wf ctx.nl G.tab e = true) (htmp : gen ctx e .rax fr = none → TmpFit ctx.nl F 0 (tempsE e))
    (σ : St) (s : MachineData) (Q : MachineState → Prop) (hI : Inv G ctx F σ s)
    (hok : ∀ v s', evalP σ e = .ok v → s'.regs.rax = v → RPost ctx.nl F (· ∈ fr) s s' →
      Inv G ctx F σ s' → Ev Q s' (at_ (k + (valRax ctx fr e).length)))
    (herr : ∀ s', (∃ x, evalP σ e = .error x) → RPost ctx.nl F (· ∈ fr) s s' → Ev Q s' (label errorL)) :
    Ev Q s (at_ k) := by
  have hfree : ∀ r' ∈ fr, ∀ x, ctx.alloc.lookup x ≠ some r' := fun r' h => pool_free hI.al (hfr r' h)
  have hpool : Reg64.rax ∈ ctx.pool := by simp [Ctx.pool]
  unfold valRax at hc hok
  cases hg : gen ctx e .rax fr
  case some code =>
    simp only [hg] at hc hok
    have hok' : GOk ctx e .rax fr :=
      ⟨List.nodup_cons.mpr ⟨hrf, hfn⟩,
       fun r' h => by
         rcases List.mem_cons.mp h with rfl | h
         · exact pool_dreg hpool
         · exact pool_dreg (hfr r' h),
       fun r' h => by
         rcases List.mem_cons.mp h with rfl | h
         · exact readsReg_free (pool_free hI.al hpool) e
         · exact readsReg_free (hfree r' h) e⟩
    have hW : ∀ r' ∈ Reg64.rax :: fr, r' ∈ ctx.pool := fun r' h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact hpool
      · exact hfr r' h
    refine sim_gen hG hT hTab hF e .rax fr code k hg hc hok' hwf σ s Q hI ?_ ?_
    · intro v s1 hv hr1 hX1
      have hI1 := hI.ghost hX1 hok'.dr
      rw [St.ghost_free (fun r' h => pool_free hI.al (hW r' h))] at hI1
      exact hok v s1 hv (UInt64.toBitVec_inj.mp (by simpa using hr1))
        (RPost.ofX hX1 hok'.dr fun r' h => by
          rcases List.mem_cons.mp h with rfl | h
          · exact .inr (.inl rfl)
          · exact .inl h) hI1
    · exact fun s1 he hX1 => herr s1 he (RPost.ofX hX1 hok'.dr fun r' h => by
          rcases List.mem_cons.mp h with rfl | h
          · exact .inr (.inl rfl)
          · exact .inl h)
  simp only [hg] at hc hok
  exact sim_expr hG ctx hT hTab F hF e 0 k hc hwf (htmp hg) σ s Q hI
    (fun v s' hv hr hE => hok v s' hv hr (hE.rpost _) (hI.ofE hG hE)) (fun s' he hE => herr s' he (hE.rpost _))

theorem sim_args (ctx : Ctx) (hT : ctx.tab = G.tab) (F : Nat) (hF : 8 * F + 8 < maxOff) :
    ∀ (args : List Expr) (i k : Nat), Code (compileArgs ctx i args) k →
    args.all (Expr.wf ctx.nl G.tab) = true → ctx.nl + tempsArgs i args ≤ F →
    ∀ (σ : St) (s : MachineData) (Q : MachineState → Prop), Inv G ctx F σ s →
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
    refine sim_expr hG ctx hT hTab F hF e i k hc.left hwf.1 (.inr (by omega)) σ s Q hI ?_ ?_
    · intro v s1 hv hrax1 hE1
      have hI1 : Inv G ctx F σ s1 :=
        hI.ofE hG hE1
      have hoff : SmallOff (8 * ((ctx.nl : Int) + (i : Int))) := ⟨by omega, by omega⟩
      refine ev_movMR hc.right.head hoff ?_ ?_
      · rw [slot_addr _ (ctx.nl + i) _ (by omega)]; exact hI1.mapped (by omega)
      rw [slot_addr _ (ctx.nl + i) _ (by omega)]
      have hE2 := hE1.trans (EPost.store (v := s1.regs.get64 .rax) (j := ctx.nl + i) (s := s1)
        (by omega) (by omega) (by rw [hE1.rsp]; omega)) (Nat.le_refl _)
      have hI2 := hI.ofE hG hE2
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
      · exact fun s3 ⟨x, hx⟩ hE3 => herr s3 ⟨x, by simp [evalArgsP, hv, hx]; rfl⟩ (hE2.trans hE3 (by omega))
    · exact fun s1 ⟨x, hx⟩ hE1 => herr s1 ⟨x, by simp [evalArgsP, hx]; rfl⟩ hE1

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
  simp only [compileS] at hc hK
  simp only [tempsS] at htmp
  have hF' := hF; simp only [maxOff] at hF'
  have hTab' := hTab; simp only [maxOff] at hTab'
  have hnr := hN.le
  have hnret : es.length ≤ ctx.nr := hN.ret
  simp only [Ctx.g_alloc] at htmp
  by_cases hok : retOk ctx.alloc es ctx.nr = true
  · simp only [hok, ite_true] at htmp
    cases es with
    | nil =>
      simp only [retDirect, hok, ite_true, List.append_assoc] at hc hK
      have hn6 : ctx.nr ≤ maxRes := by simpa [retOk] using hok
      refine sim_zeroRes Q ctx.nr 0 k d hc.left (by omega) ?_
      intro s' hd h1 h2 h3 h4 hz _
      have hc2 := hc.right
      rw [zeroRes_length] at hc2
      refine ev_jmp hc2.head (hK.ret [] σ s' (by simp [step_ret_run, evalArgsP]; rfl) (hd ▸ hI.mem)
        ⟨h1, h2, h4, by rw [h3]; exact Nat.le_refl _, by rw [hd]; exact Pres.refl _ _⟩
        ⟨fun j hj hm => by rw [hz j (Nat.zero_le _) (by omega)]; simp, fun j h1 h2 => absurd h2 (by omega),
          by simp⟩)
    | cons e0 rest =>
      simp only [retDirect, hok, ite_true, List.append_assoc] at hc hK
      have hok' := hok
      simp only [retOk, Bool.and_eq_true, decide_eq_true_eq, List.length_cons] at hok'
      obtain ⟨⟨hn6, hl⟩, hsafe⟩ := hok'
      simp only [List.all_cons, Bool.and_eq_true] at hargs
      simp only [tempsRet, gen_g] at htmp
      have hfr0 : ∀ r ∈ (retFree ctx.pool 1 rest).filter (· != .rax), r ∈ ctx.pool ∧
          ∀ j, 1 ≤ j → j < 1 + rest.length → r ≠ resReg j := fun r h =>
        retFree_sub rest ctx.pool 1 r (mem_filter_sub r h)
      refine sim_retRegs hG hTab ctx hT F hF σ e0 Q rest ctx.pool 1 k σ d (fun r h => h) (pool_nodup ctx)
        hc.left hargs.2
        (htmp.mono (Nat.le_max_left _ _)) (Nat.le_refl _) (by omega) hsafe hI rfl rfl (fun _ _ => rfl) ?_ ?_
      · intro vs σ' s1 hvs hI1 hm1 he1 hR1 hregs
        have hvl := evalArgsP_length hvs
        have hc2 := hc.right
        refine sim_valRax hG hTab ctx hT F hF (fun r h => (hfr0 r h).1)
          (List.Nodup.sublist (List.filter_sublist.trans (retFree_sublist rest ctx.pool 1)) (pool_nodup ctx))
          (by simp) e0 _ hc2.left hargs.1 (fun h => htmp.mono (by
            simp only [Ctx.g_pool, h, Option.isSome_none, Bool.false_eq_true, ite_false]; omega))
          σ' s1 Q hI1 ?_ ?_
        · intro v0 s2 hv0 hrax hE2 hI2
          rw [he1] at hv0
          have hc3 := hc2.right
          refine sim_zeroRes Q _ _ _ s2 hc3.left (by omega) ?_
          intro s3 hd q1 q2 q3 q4 hz hkeep
          have hc4 := hc3.right
          rw [zeroRes_length] at hc4
          refine ev_jmp hc4.head (hK.ret (v0 :: vs) σ s3 (by simp [step_ret_run, evalArgsP, hv0, hvs]; rfl)
            (by rw [hd, ← hm1]; exact hI2.mem) ?_ ⟨?_, fun j h1 h2 => absurd h2 (by omega), by simp only [List.length_cons] at hl ⊢; omega⟩)
          · refine (hR1.spost hI.lo).trans ((hE2.spost hI1.lo).trans ?_)
            exact ⟨q1, q2, q4, by rw [q3]; exact Nat.le_refl _, by rw [hd]; exact Pres.refl _ _⟩
          · intro j hj hjm
            by_cases hjl : j < rest.length + 1
            · rw [hkeep j hjm (.inl hjl)]
              cases j with
              | zero => simp [rres, hrax]
              | succ j =>
                have hr := resReg_alloc (j := j + 1) (by omega) hjm
                have hne := allocRegs_ne hr
                apply UInt64.toBitVec_inj.mp
                rw [rres_eq_get64 _ hjm, hE2.keep _ hne.1 hne.2.1 hne.2.2.1
                  (fun h => (hfr0 _ h).2 (j + 1) (by omega) (by omega) rfl)]
                have := hregs j (by omega)
                rw [Nat.add_comm] at this
                rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
                simpa using this
            · have hl' := hl
              rw [hz j (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
        · intro s2 he hE2
          obtain ⟨x, hx⟩ := he
          rw [he1] at hx
          refine hK.err s2 ⟨x, by simp [step_ret_run, evalArgsP, hx]; rfl, by rw [evalP_error hx]; simp⟩
            ((hR1.spost hI.lo).trans_g (hE2.spost hI1.lo).gpost)
      · intro s1 he hR1
        obtain ⟨x, hx⟩ := he
        cases hv0 : evalP σ e0 with
        | error y =>
          exact hK.err s1 ⟨y, by simp [step_ret_run, evalArgsP, hv0]; rfl, by rw [evalP_error hv0]; simp⟩
            (hR1.spost hI.lo).gpost
        | ok v0 =>
          exact hK.err s1 ⟨x, by simp [step_ret_run, evalArgsP, hv0, hx]; rfl, by rw [evalArgsP_error hx]; simp⟩
            (hR1.spost hI.lo).gpost
  · have hrd : retDirect ctx es ctx.nr = none := by simp [retDirect, hok]
    simp only [hrd, List.append_assoc] at hc hK
    simp only [hok, Bool.false_eq_true, ite_false] at htmp
    replace htmp := htmp.le (by omega)
    have hlenT := tempsArgs_ge 0 es
    refine sim_args hG hTab ctx hT F hF es 0 k hc.left hargs (by omega) σ d Q hI ?_ ?_
    · intro vs s1 hvs hE1 hslots
      have hvl := evalArgsP_length hvs
      have hI1 := hI.ofE hG hE1
      have hc2 := hc.right
      rw [← hvl] at hc2
      have h1sp := congrArg UInt64.toNat hE1.rsp
      refine sim_loadRes hG ctx hT vs vs Q (by omega) ctx.nr 0 _ s1 hc2.left (by omega)
        (fun _ => by rw [hvl]; omega) hI1.r15 hI1.lo (fun _ => by rw [h1sp, hvl]; have := hI.hi; omega)
        (fun x hx => hI1.mem.res x hx) (fun j hj => by rw [h1sp]; simpa [h1sp] using hslots j hj)
        (fun j hj => absurd hj (Nat.not_lt_zero _)) (fun j _ hj => absurd hj (Nat.not_lt_zero _))
        (fun _ _ => rfl) ?_
      intro s2 h1 h2 h3 h4 hO hR hM
      have hj := hc2.right
      refine ev_jmp hj.head (hK.ret vs σ s2 (by simp [step_ret_run, hvs]; rfl)
        (hI1.mem.only_res hG hO (fun x a b => Layout.inRes_of a b)) ((hE1.spost hI.lo).trans ?_)
        ⟨fun j hj => hR j (by omega), fun j h1 h2 => hM j h1 (by omega), by omega⟩)
      exact ⟨h1, h2, h4, by rw [h3]; exact Nat.le_refl _, Pres.of_res hO fun x a b => Layout.inRes_of a b⟩
    · exact fun s1 ⟨y, hy⟩ hE1 => hK.err s1 ⟨y, by simp [step_ret_run, hy]; rfl, by rw [evalArgsP_error hy]; simp⟩
        (hE1.spost hI.lo).gpost

omit [Host] hG hTab in
theorem argRegs_getD_mem : ∀ i < argRegs.length, argRegs.getD i .rax ∈ allocRegs := by
  intro i hi
  refine argRegs_sub ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

omit [Host] hG hTab in
theorem compileFn_head (tab : Tab) (t : NTree) (f : FnName) (fd : FunDecl) :
    (compileFn tab t f fd)[0]? = some (.label (fnL f)) := by
  dsimp only [compileFn]; split <;> rfl

/-- A call, from the state `s1` with the arguments in place: fuel, `call`, the results into the
locals. -/
theorem sim_callTail (t : NTree) (n : Nat) (hFun : FunSim p G t n)
    (hProg : ∀ f fd, p.lookup f = some fd → ∃ kf, Code (compileFn G.tab t f fd) kf)
    (xs : List Var) (f : FnName) (args : List Expr) (fd : FunDecl) (hlk : p.lookup f = some fd)
    (ctx : Ctx) (F : Nat) (hT : ctx.tab = G.tab) (hF : 8 * F + 8 < maxOff) (hal : ctx.alloc = [])
    (htn : ctx.treg = none) (hxs : xs.all (· < ctx.nl) = true) (hxl : xs.length ≤ G.tab.nres) (hN : NrOk p G ctx (.call xs f args))
    (σ : St) (d s1 : MachineData) (Q : MachineState → Prop) (k1 : Nat) (vs : List Word)
    (hvs : evalArgsP σ args = .ok vs) (hvl : vs.length = fd.nparams)
    (hc : Code ([i64 (.sub (.reg (rr .r14)) (oI 1)), jccL .c exhaustedL,
       i64 (.call (.rel (.sub (.label (fnL f)) .after_current_instruction)))] ++
       (storeRes ctx.tab (xs.take (nrOf ctx.nrt ctx.tab f)) 0 ++ zeroVars (xs.drop (nrOf ctx.nrt ctx.tab f)))) k1)
    (hI : Inv G ctx F σ d) (hP : d.regs.r14.toNat ≤ n) (hS1 : SPost G F d s1) (hr14 : s1.regs.r14 = d.regs.r14)
    (hI1 : Inv G ctx F σ s1) (hlo8 : G.lo + 8 ≤ s1.regs.rsp.toNat) 
    (ha1 : vs.length ≤ argRegs.length → ∀ i (h : i < vs.length),
      s1.regs.get64 (argRegs.getD i .rax) = vs[i].toBitVec)
    (ha2 : argRegs.length < vs.length →
      (∀ i (h : i < vs.length), rdW s1.dmem (A (s1.regs.rsi.toNat + 8 * i)) = some vs[i]) ∧
      s1.regs.rsp.toNat ≤ s1.regs.rsi.toNat ∧ s1.regs.rsi.toNat + 8 * vs.length < 2 ^ 64)
    (kend : Nat) (hkend : kend = k1 + 3 + (storeRes ctx.tab (xs.take (nrOf ctx.nrt ctx.tab f)) 0).length +
        (zeroVars (xs.drop (nrOf ctx.nrt ctx.tab f))).length)
    (hK : Conts G ctx F d (stepRun p (exec p n) (.call xs f args) σ) kend Q) :
    Ev Q s1 (at_ k1) := by
  obtain ⟨kf, hkf⟩ := hProg f fd hlk
  have hlf := Code.label (i := 0) hkf (compileFn_head _ _ _ _)
  have hF' := hF; simp only [maxOff] at hF'
  have hsp := hI1.hi
  have hhi := hG.hi_le
  have h1rsp := congrArg UInt64.toNat hS1.rsp
  refine ev_sub1 hc.head fun st hst => ?_
  refine ev_jcc hc.tail.head (fun hcc => ?_) (fun hcc => ?_)
  · exact hK.exh _ (hS1.trans_g ⟨by simp, Pres.refl _ _⟩)
  · simp only [CondCode.interp] at hcc
    rw [hst] at hcc
    have h0 : s1.regs.r14 ≠ 0 := by intro h; simp [h] at hcc
    have hpos : 0 < s1.regs.r14.toNat := by
      rcases Nat.eq_zero_or_pos s1.regs.r14.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) h0
      · exact h
    have hsp8 : 8 ≤ s1.regs.rsp.toNat := by omega
    refine ev_call hc.tail.tail.head ?_ ?_
    · simp only [Reg64s.set64_r14]
      rw [bv_sub8 _ hsp8]
      refine isSome_rdW fun j hj => ?_
      rw [A_add]
      exact hI1.mem.stack _ ⟨by omega, by omega⟩
    rw [hlf, Nat.add_zero]
    refine hFun f fd kf hlk hkf vs σ _ (UInt64.ofBitVec (at_ (k1 + 1 + 1 + 1)).toBitVec) Q hvl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [Reg64s.set64_rsp, Reg64s.set64_r14, Reg64s.get64_rsp, Reg64s.get64_r14]
    · rw [bv_sub8 _ hsp8]
      rw [show (({ toBitVec := A (s1.regs.rsp.toNat - 8) } : UInt64).toNat) = s1.regs.rsp.toNat - 8 by
        addr_omega, rdW_wrW_same]
    · refine ⟨fun hl i hi => ?_, fun hl => ?_⟩
      · have hr : argRegs.getD i .rax ∈ allocRegs := argRegs_getD_mem i (by omega)
        rw [← ha1 hl i hi]
        generalize argRegs.getD i .rax = r at hr
        have hne := allocRegs_ne hr
        obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hne
        cases r <;> (first | exact absurd rfl n4 | exact absurd rfl n6 | rfl)
      · obtain ⟨hm1, hsi', hm3⟩ := ha2 hl
        refine ⟨fun i hi => ?_, ?_, ?_⟩
        · rw [bv_sub8 _ hsp8, rdW_wrW_A (by omega) (by addr_omega) (by addr_omega), ← hm1 i hi]
        · left; rw [bv_sub8 _ hsp8]; addr_omega
        · addr_omega
    · rw [bv_sub8 _ hsp8]; addr_omega
    · rw [bv_sub8 _ hsp8]; addr_omega
    · exact hI1.r15
    · rw [bv_sub8 _ hsp8]
      exact hI1.mem.only hG (Only.wrW (by omega)) fun z h1 h2 => ⟨by omega, by omega⟩
    · have h1 : ({ toBitVec := s1.regs.r14.toBitVec - 1 } : UInt64).toNat = s1.regs.r14.toNat - 1 :=
        u64_sub_one_toNat hpos
      rw [h1]; rw [hr14] at hpos ⊢; omega
    · intro r σ' d' hinv hmem hloc hrsp hrbp hr15 hr14' hrax hpres
      rw [Int64.ofBitVec_toBitVec]
      rw [bv_sub8 _ hsp8] at hpres hrsp
      have hrsp' : d'.regs.rsp.toNat = s1.regs.rsp.toNat := by addr_omega
      have hrsp'' : d'.regs.rsp = s1.regs.rsp := UInt64.toNat_inj.mp (by omega)
      have h4 : ({ toBitVec := A (s1.regs.rsp.toNat - 8) } : UInt64).toNat = s1.regs.rsp.toNat - 8 := by
        addr_omega
      rw [h4] at hpres
      have hpres1 : Pres G s1.regs.rsp.toNat s1.dmem
          (wrW s1.dmem (A (s1.regs.rsp.toNat - 8)) (at_ (k1 + 1 + 1 + 1)).toBitVec) :=
        Pres.of_only (Only.wrW (by omega)) (by omega) (by omega)
      have hId : Inv G ctx F σ' d' := by
        refine hI1.congr' hloc hrsp'' (by rw [hr15]) (fun x r h => by simp [hal] at h) (fun y hy hyn => ?_) hmem (fun h => absurd htn h)
        have := hI1.slot y hy hyn
        rw [rdW_of_pres hG hpres (by omega) (by omega) (by omega),
          rdW_of_pres hG hpres1 (by omega) (by omega) (by omega)]
      have hTab' := hTab; simp only [maxOff] at hTab'
      have hcS := hc.tail.tail.tail
      simp only [List.append_eq, List.nil_append] at hcS
      have hcn : nrOf ctx.nrt ctx.tab f = Stmt.nret fd.body := hT ▸ hN.callee f fd hlk
      rw [hcn, hT] at hcS
      have hxl' : xs.length ≤ G.tab.nres := hxl
      have hxs1 : (xs.take (Stmt.nret fd.body)).all (· < ctx.nl) = true :=
        List.all_eq_true.mpr fun y hy => List.all_eq_true.mp hxs y (List.mem_of_mem_take hy)
      have hxs2 : (xs.drop (Stmt.nret fd.body)).all (· < ctx.nl) = true :=
        List.all_eq_true.mpr fun y hy => List.all_eq_true.mp hxs y (List.mem_of_mem_drop hy)
      have htk := List.length_take_le' (Stmt.nret fd.body) xs
      have hnl : 8 * ctx.nl < 2 ^ 31 := by
        have : ctx.nl ≤ F := Classical.byContradiction fun h =>
          absurd (hI1.slot F (by omega) (by simp [hal])) (Nat.lt_irrefl _)
        omega
      refine sim_storeRes hG ctx hal htn F Q (by omega) _ 0 _ σ' r d' hcS.left hxs1
        (by rw [Nat.zero_add]; exact Nat.le_trans htk hxl') hnl hId
        (fun j hj hm => by rw [Nat.zero_add] at hm ⊢; exact hrax.1 j (by simp at hj; omega) hm)
        (fun j hj hm => by rw [Nat.zero_add] at hm ⊢; exact hrax.2.1 j hm (by simp at hj; omega)) ?_
      intro s1' hI1' p1 p2 p3 p4 hP1
      refine sim_zeroVars hG ctx hal htn F Q _ _ _ s1' hcS.right hxs2 hnl hI1' ?_
      intro s' hI'' hr' hP2
      rw [← St.setLocs_take_drop xs σ' r _ hrax.2.2] at hI''
      have q1 : s'.regs.rsp = d'.regs.rsp := by rw [hr', p1]
      have q2 : s'.regs.rbp = d'.regs.rbp := by rw [hr', p2]
      have q3 : s'.regs.r14 = d'.regs.r14 := by rw [hr', p3]
      have q4 : s'.regs.r15 = d'.regs.r15 := by rw [hr', p4]
      have hP' : Pres G (top d' F) d'.dmem s'.dmem := hP1.trans (by simpa [top, p1] using hP2)
      refine ev_congr (hK.normal (σ'.setLocs xs r) _ ?_ hI'' ?_) ?_
      · rw [step_call_run, hvs]; simp only [hinv]
      · refine hS1.trans ⟨by rw [q1]; exact hrsp'', by rw [q2]; exact hrbp, by rw [q4]; exact hr15, ?_, ?_⟩
        · show s'.regs.r14.toNat ≤ s1.regs.r14.toNat
          rw [q3]
          have h1 : ({ toBitVec := s1.regs.r14.toBitVec - 1 } : UInt64).toNat = s1.regs.r14.toNat - 1 :=
            u64_sub_one_toNat hpos
          rw [h1] at hr14'; omega
        · refine (hpres1.mono (by simp only [top]; omega)).trans ?_
          refine (hpres.mono (by simp only [top]; omega)).trans ?_
          exact hP'.mono (by simp only [top]; rw [hrsp']; omega)
      · rw [hkend]; simp only [List.length_append, List.length_cons, zeroVars_length, hT, hN.callee f fd hlk]
    all_goals
      intro d'
      have h4 : ({ toBitVec := A (s1.regs.rsp.toNat - 8) } : UInt64).toNat = s1.regs.rsp.toNat - 8 := by
        addr_omega
      have hchain : Pres G (top s1 F) s1.dmem
          (wrW s1.dmem (A (s1.regs.rsp.toNat - 8)) (at_ (k1 + 1 + 1 + 1)).toBitVec) :=
        Pres.of_only (Only.wrW (by omega)) (by omega) (by simp only [top]; omega)
    · intro ⟨y, hy, hne⟩ hG'
      rw [bv_sub8 _ hsp8, h4] at hG'
      exact hK.err d' ⟨y, by rw [step_call_run, hvs]; simp only [hy], hne⟩
        (hS1.trans_g ⟨hG'.rbp, hchain.trans (hG'.mem.mono (by simp only [top]; omega))⟩)
    · intro k hy hG' hrax
      rw [bv_sub8 _ hsp8, h4] at hG'
      exact hK.abrt d' k (by rw [step_call_run, hvs]; simp only [hy])
        (hS1.trans_g ⟨hG'.rbp, hchain.trans (hG'.mem.mono (by simp only [top]; omega))⟩) hrax
    · intro hG'
      rw [bv_sub8 _ hsp8, h4] at hG'
      exact hK.exh d' (hS1.trans_g ⟨hG'.rbp, hchain.trans (hG'.mem.mono (by simp only [top]; omega))⟩)

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
  have hleaf : ctx.leaf = false := by
    cases h : ctx.leaf
    · rfl
    · have := hN.leaf h; simp [Stmt.calls] at this
  have hal := hI.al.leaf hleaf
  have htn := hI.al.tleaf hleaf
  have hlo8 := hI.lo8 hleaf
  simp only [compileS, burnFuel, List.append_assoc, List.cons_append, List.nil_append,
    List.singleton_append] at hc hK
  simp only [tempsS] at htmp
  have hF' := hF; simp only [maxOff] at hF'
  have herr : ∀ s1 (W : Reg64 → Prop), (∃ x, evalArgsP σ args = .error x) → RPost ctx.nl F W d s1 →
      Ev Q s1 (label errorL) := fun s1 W he hR1 => by
    obtain ⟨y, hy⟩ := he
    exact hK.err s1 ⟨y, by simp [step_call_run, hy] <;> rfl, by rw [evalArgsP_error hy]; simp⟩
      (hR1.spost hI.lo).gpost
  by_cases hreg : args.length ≤ argRegs.length
  · simp only [hreg, ite_true] at hc hK htmp
    refine sim_regArgs hG hTab ctx hT F hF hal htn args ctx.pool argRegs k hreg (fun r h => argRegs_sub h) (by decide)
      (fun r h => h) (pool_nodup ctx) hc.left hargs
      htmp σ d Q hI ?_ (fun s1 he hR1 => herr s1 _ he hR1)
    intro vs s1 hvs hR1 hI1 hregs
    have hvl := evalArgsP_length hvs
    exact sim_callTail hG hTab p t n hFun hProg xs f args fd hlk ctx F hT hF hal htn hxs hxl hN σ d s1 Q _ vs hvs
      (by rw [hvl, hfd]) hc.right hI hP (hR1.spost hI.lo) hR1.r14 hI1 (by rw [hR1.rsp]; exact hlo8)
      (fun _ i hi => hregs i hi) (fun h => absurd h (by omega)) _
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hK
  · simp only [hreg, ite_false, List.append_assoc, List.singleton_append] at hc hK htmp
    have hlen := tempsArgs_ge 0 args
    replace htmp := htmp.le (by omega)
    refine sim_args hG hTab ctx hT F hF args 0 k hc.left hargs htmp σ d Q hI ?_
      (fun s1 he hE1 => herr s1 (fun _ => False) he (hE1.rpost _))
    intro vs s1 hvs hE1 hslots
    have hvl := evalArgsP_length hvs
    have h1rsp := congrArg UInt64.toNat hE1.rsp
    have hI1 := hI.ofE hG hE1
    have hsp := hI.hi
    have hhi := hG.hi_le
    have hcR := hc.right
    refine ev_lea hcR.head ⟨by omega, by omega⟩ ?_
    have hoff : (8 * ((ctx.nl : Int) + ((0 : Nat) : Int))).toNat = 8 * ctx.nl := by omega
    simp only [Reg64s.get64_rsp, UInt64.toNat_toBitVec, hoff]
    have hsi : (UInt64.ofBitVec (A (s1.regs.rsp.toNat + 8 * ctx.nl))).toNat = s1.regs.rsp.toNat + 8 * ctx.nl := by
      simp only [UInt64.toNat_ofBitVec, A, BitVec.toNat_ofNat]; omega
    have hS2 : SPost G F d { s1 with regs := s1.regs.set64 .rsi (A (s1.regs.rsp.toNat + 8 * ctx.nl)) } :=
      (hE1.spost hI.lo).trans ⟨by simp, by simp, by simp, by simp, Pres.refl _ _⟩
    refine sim_callTail hG hTab p t n hFun hProg xs f args fd hlk ctx F hT hF hal htn hxs hxl hN σ d _ Q _ vs hvs
      (by rw [hvl, hfd]) hcR.tail hI hP hS2 (by simp [hE1.r14]) (hI1.of_regs0 hal rfl (by simp) (by simp))
      (by simp only [Reg64s.set64_rsi]; rw [hE1.rsp]; exact hlo8) (fun h => absurd h (by omega)) (fun _ => ⟨?_, ?_, ?_⟩) _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hK
    · intro i hi
      have := hslots i hi
      simp only [Reg64s.set64_rsi, UInt64.toNat_mk', UInt64.toNat_ofBitVec, A, BitVec.toNat_ofNat]
      rw [← this]; congr 2; omega
    · simp only [Reg64s.set64_rsi, UInt64.toNat_mk', UInt64.toNat_ofBitVec, A, BitVec.toNat_ofNat]; omega
    · simp only [Reg64s.set64_rsi, UInt64.toNat_mk', UInt64.toNat_ofBitVec, A, BitVec.toNat_ofNat]
      have := hI.hi; omega

end

end L.Compiler
