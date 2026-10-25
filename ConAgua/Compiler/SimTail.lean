module

public import ConAgua.Compiler.SimFun

@[expose] public section

/-!
# Tail calls

`x⃗ := f(a⃗); return x⃗`, compiled by `tailCode`: the arguments into their registers, fuel, the
frame popped, a jump to `f`. `f` then returns to this function's caller: its simulation
(`FunSim`) does not depend on the caller's frame, so it is used with the return address above
this function's frame, and its results are this function's (`Conts.tail`).
-/

namespace L.Compiler

open L

attribute [local simp] Reg64s.set64_rax Reg64s.set64_rcx Reg64s.set64_rdx Reg64s.set64_rsi
  Reg64s.set64_rsp Reg64s.set64_r14

theorem retVars_eq : ∀ (es : List Expr) (xs : List Var), retVars es xs = true → es = xs.map Expr.var
  | [], [], _ => rfl
  | .var y :: es, x :: xs, h => by
    simp only [retVars, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, retVars_eq es xs h.2]; rfl

theorem nodupB_nodup : ∀ (l : List Var), nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [nodupB_cons] at h
    exact List.nodup_cons.mpr ⟨h.1, nodupB_nodup l h.2⟩

theorem St.setLocs_mem' : ∀ (xs : List Var) (σ : St) (r : List Word), (σ.setLocs xs r).mem = σ.mem
  | [], _, _ => rfl
  | x :: xs, σ, r => by rw [St.setLocs, St.setLocs_mem' xs]; rfl

theorem St.setLocs_loc_not_mem : ∀ (xs : List Var) (σ : St) (r : List Word) (y : Var), y ∉ xs →
    (σ.setLocs xs r).loc y = σ.loc y
  | [], _, _, _, _ => rfl
  | x :: xs, σ, r, y, h => by
    rw [St.setLocs, St.setLocs_loc_not_mem xs _ _ y (fun h' => h (List.mem_cons_of_mem _ h'))]
    have : y ≠ x := fun h' => h (h' ▸ List.mem_cons_self)
    simp [St.setLoc, this]

theorem St.setLocs_loc_get : ∀ (xs : List Var), xs.Nodup → ∀ (σ : St) (r : List Word) (i : Nat)
    (hi : i < xs.length), (σ.setLocs xs r).loc xs[i] = r.getD i 0
  | [], _, _, _, _, hi => absurd hi (by simp)
  | x :: xs, hnd, σ, r, i, hi => by
    rw [St.setLocs]
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      rw [St.setLocs_loc_not_mem xs _ _ x hx]
      cases r <;> simp [St.setLoc]
    | succ i =>
      simp only [List.getElem_cons_succ]
      rw [St.setLocs_loc_get xs hnd' _ _ i (by simp at hi; omega)]
      cases r <;> simp

theorem evalArgsP_vars (σ : St) : ∀ xs : List Var, evalArgsP σ (xs.map Expr.var) = .ok (xs.map σ.loc)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, evalArgsP, evalArgsP_vars σ xs]; rfl

/-- What `tailCode` accepts. -/
theorem tailCode_some {ctx : Ctx} {s u : Stmt} {code : Program} (h : tailCode ctx s u = some code) :
    ∃ xs f args es Fw, s = .call xs f args ∧ u = .ret es ∧ ctx.tailF = some Fw ∧ es = xs.map Expr.var ∧
      xs.Nodup ∧ xs.length = ctx.nr ∧ ctx.nr ≤ nrOf ctx.nrt ctx.tab f ∧ args.length ≤ argRegs.length ∧
      code = compileRegArgs ctx argRegs args ++ burnFuel ++
        [i64 (.add (.reg (rr .rsp)) (oI (8 * Fw))), jmpL (fnL f)] := by
  cases s <;> try (simp [tailCode] at h; done)
  rename_i xs f args
  cases u <;> try (simp [tailCode] at h; done)
  rename_i es
  simp only [tailCode] at h
  cases hF : ctx.tailF with
  | none => simp [hF] at h
  | some Fw =>
    simp only [hF] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
      cases h
      exact ⟨xs, f, args, es, Fw, rfl, rfl, rfl, retVars_eq es xs h1, nodupB_nodup xs h2, h3, h4, h5, rfl⟩
    · cases h

section
variable [Host] {G : Layout} (hG : G.Ok) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
  (p : Prog)
include hG hTab

theorem sim_tail (t : NTree) (n : Nat) (hFun : FunSim p G t n)
    (hProg : ∀ f fd, p.lookup f = some fd → ∃ kf, Code (compileFn G.tab t f fd) kf) (s u : Stmt) :
    SimSTail p G (stepRun p (exec p n)) (· ≤ n) s u := by
  intro ctx F k code hT hF htc hc hwf hN htmp σ d Q hI hP hK
  obtain ⟨xs, f, args, es, Fw, rfl, rfl, hFw, rfl, hnd, hxl, hnr, hreg, rfl⟩ := tailCode_some htc
  obtain ⟨hFwF, hKt⟩ := hK.tail Fw hFw
  have e := hFwF.symm
  subst e
  simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨⟨⟨hxs, hxl'⟩, hargs⟩, hfd⟩, -⟩ := hwf
  cases hlk : p.lookup f with
  | none => simp [hlk] at hfd
  | some fd =>
  simp only [hlk, beq_iff_eq] at hfd
  have hleaf : ctx.leaf = false := by
    cases h : ctx.leaf
    · rfl
    · have := hN.leaf h; simp [Stmt.calls] at this
  have hal := hI.al.leaf hleaf
  have hlo8 := hI.lo8 hleaf
  simp only [tempsS, hreg, ite_true] at htmp
  have hF' := hF; simp only [maxOff] at hF'
  have hhi := hG.hi_le
  have hsp := hI.hi
  have hcn : nrOf ctx.nrt ctx.tab f = Stmt.nret fd.body := hT ▸ hN.callee f fd hlk
  rw [hcn] at hnr
  -- the run of `x⃗ := f(a⃗); return x⃗`
  have hrun : ∀ vs, evalArgsP σ args = .ok vs → ∀ r σ', (invoke p (exec p n) f vs).run σ = .ok (r, σ') →
      stepRun p (exec p n) (.seq (.call xs f args) (.ret (xs.map Expr.var))) σ =
        .ok (.ret (xs.map (σ'.setLocs xs r).loc), σ'.setLocs xs r) := by
    intro vs hvs r σ' hinv
    rw [step_seq_run, step_call_run, hvs]
    simp only [hinv]
    rw [step_ret_run, evalArgsP_vars]; rfl
  simp only [burnFuel, List.append_assoc, List.cons_append, List.nil_append] at hc
  refine sim_regArgs hG hTab ctx hT F hF hal (hI.al.tleaf hleaf) args argRegs k hreg (fun r h => argRegs_sub h) (by decide) hc.left hargs
    (htmp.mono (Nat.le_max_left _ _)) σ d Q hI ?_ ?_
  · intro vs s1 hvs hR1 hI1 hregs
    have hvl := evalArgsP_length hvs
    have hc2 := hc.right
    have h1rsp := congrArg UInt64.toNat hR1.rsp
    have hS1 := hR1.spost (G := G) hI.lo
    refine ev_sub1 hc2.head fun st hst => ?_
    refine ev_jcc hc2.tail.head (fun hcc => ?_) (fun hcc => ?_)
    · exact hK.exh _ (hS1.trans_g ⟨by simp, Pres.refl _ _⟩)
    simp only [CondCode.interp] at hcc
    rw [hst] at hcc
    have h0 : s1.regs.r14 ≠ 0 := by intro h; simp [h] at hcc
    have hpos : 0 < s1.regs.r14.toNat := by
      rcases Nat.eq_zero_or_pos s1.regs.r14.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) h0
      · exact h
    refine ev_addRI hc2.tail.tail.head fun st2 => ?_
    refine ev_jmp hc2.tail.tail.tail.head ?_
    obtain ⟨kf, hkf⟩ := hProg f fd hlk
    rw [Code.label (i := 0) hkf (compileFn_head _ _ _ _), Nat.add_zero]
    -- the return address above the frame
    obtain ⟨ra, hra⟩ : ∃ ra, rdW s1.dmem (A (top s1 F)) = some ra := Option.isSome_iff_exists.mp
      (isSome_rdW fun j hj => by rw [A_add]; exact hI1.mem.stack _ ⟨by simp only [top]; omega, by simp only [top]; omega⟩)
    have hadd : s1.regs.rsp.toBitVec + (Int64.ofInt (8 * (F : Int))).toBitVec = A (top s1 F) := by
      rw [show (8 * (F : Int)) = ((8 * F : Nat) : Int) by push_cast; rfl, int64_ofInt_toBitVec]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, A, top]
      omega
    have htop : top s1 F = top d F := by simp only [top, hR1.rsp]
    have hP1 : Pres G (top d F) d.dmem s1.dmem := hS1.mem
    refine hFun f fd kf hlk hkf vs σ _ ra Q (by rw [hvl, hfd]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [Reg64s.set64_rsp, Reg64s.set64_r14, Reg64s.get64_rsp, Reg64s.get64_r14, hadd]
    · rw [show (({ toBitVec := A (top s1 F) } : UInt64).toNat) = top s1 F by
        simp only [top]; addr_omega]; exact hra
    · refine ⟨fun hl i hi => ?_, fun hl => absurd hl (by omega)⟩
      have hr : argRegs.getD i .rax ∈ allocRegs := argRegs_getD_mem i (by omega)
      rw [← hregs i hi]
      generalize argRegs.getD i .rax = r at hr
      have hne := allocRegs_ne hr
      obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hne
      cases r <;> (first | exact absurd rfl n4 | exact absurd rfl n6 | rfl)
    · simp only [top]; addr_omega
    · simp only [top]; addr_omega
    · exact hI1.r15
    · exact hI1.mem
    · have h1 : ({ toBitVec := s1.regs.r14.toBitVec - 1 } : UInt64).toNat = s1.regs.r14.toNat - 1 :=
        u64_sub_one_toNat hpos
      rw [h1, hR1.r14]; rw [hR1.r14] at hpos; omega
    · intro r σ' d' hinv hmem hloc hrsp hrbp hr15 hr14' hres hpres
      have hT0 : (({ toBitVec := A (top s1 F) } : UInt64).toNat) = top s1 F := by simp only [top]; addr_omega
      rw [hT0] at hpres hrsp
      refine hKt _ _ d' ra (hrun vs hvs r σ' hinv) (by rw [St.setLocs_mem']; exact hmem) ?_ ?_ ?_
      · refine ⟨by rw [hrsp, htop], ?_, ?_, ?_, ?_⟩
        · rw [hrbp]; exact hR1.rbp
        · rw [hr15]; exact hR1.r15
        · have h1 : ({ toBitVec := s1.regs.r14.toBitVec - 1 } : UInt64).toNat = s1.regs.r14.toNat - 1 :=
            u64_sub_one_toNat hpos
          simp only [h1] at hr14'; rw [hR1.r14] at hr14'; omega
        · exact hP1.trans (htop ▸ hpres)
      · have hget : ∀ i (hi : i < xs.length), (xs.map (σ'.setLocs xs r).loc).getD i 0 = r.getD i 0 := by
          intro i hi
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
          simp only [Option.map_some, Option.getD_some]
          exact St.setLocs_loc_get xs hnd σ' r i hi
        refine ⟨fun i hi hm => ?_, fun i h1 h2 => ?_, by simp [hxl]⟩
        · rw [hget i (by omega)]; exact hres.1 i (by omega) hm
        · rw [hget i (by omega)]; exact hres.2.1 i h1 (by omega)
      · rw [← htop, rdW_of_pres hG hpres (by simp only [top]; omega) (Nat.le_refl _) (by simp only [top]; omega)]
        exact hra
    all_goals
      have hT0 : (({ toBitVec := A (top s1 F) } : UInt64).toNat) = top s1 F := by simp only [top]; addr_omega
    · intro d' ⟨y, hy, hne⟩ hG'
      rw [hT0] at hG'
      refine hK.err d' ⟨y, by rw [step_seq_run, step_call_run, hvs]; simp only [hy], hne⟩
        ⟨by rw [hG'.rbp]; simp; exact hR1.rbp, hP1.trans (htop ▸ hG'.mem)⟩
    · intro d' hG'
      rw [hT0] at hG'
      exact hK.exh d' ⟨by rw [hG'.rbp]; simp; exact hR1.rbp, hP1.trans (htop ▸ hG'.mem)⟩
  · intro s1 he hR1
    obtain ⟨y, hy⟩ := he
    exact hK.err s1 ⟨y, by rw [step_seq_run, step_call_run, hy], by rw [evalArgsP_error hy]; simp⟩
      (hR1.spost hI.lo).gpost

end

end L.Compiler
