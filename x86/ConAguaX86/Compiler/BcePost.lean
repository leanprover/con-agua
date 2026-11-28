module

public import ConAguaX86.Compiler.RunEq
public import ConAguaX86.Compiler.BceSound
import ConAgua.L.Records

@[expose] public section

/-!
# Bounds-check elimination: the facts through the statements

**`fsound_exec`**: every run of `exec p n` keeps the arrays' sizes and the locals a statement does
not write, ends normally only with the facts after it (`postF`) true, and breaks only from a
statement with a `break` (`PostOk`). Induction on the fuel; one step (`fsound_step`) by induction
on the statement, with the loop's next iteration and the callees' bodies (`K`) by hypothesis. The
statement simulation (`SimStmt.lean`) uses it where one statement's code follows another's
(`sim_seq`) and at a loop's next iteration (`sim_while`).
-/

namespace L.Compiler

open L

/-! ## Sizes -/

theorem SameSizes.set8 (σ : St) (a : ArrId) (i v : Word) : SameSizes σ { σ with mem := σ.mem.set8 a i v } := by
  refine ⟨fun b => ?_, fun _ => rfl⟩
  by_cases h : b = a <;> simp [Mem.arr8, Mem.set8, h]

theorem SameSizes.set64 (σ : St) (a : TieredArray) (i v : Word) :
    SameSizes σ { σ with mem := σ.mem.set64 a i v } :=
  ⟨fun _ => rfl, fun _s => L.Mem.size64_set64 _ _ _ _ _⟩

theorem SameSizes.set32 (σ : St) (a : TieredArray) (i v : Word) :
    SameSizes σ { σ with mem := σ.mem.set32 a i v } :=
  ⟨fun _ => rfl, fun _s => L.Mem.size64_set64 _ _ _ _ _⟩

theorem SameSizes.setG (σ : St) (g : GVar) (v : Word) : SameSizes σ (σ.setG g v) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem Mem.size_copy64 (d : TieredArray) (s : TieredArray) :
    ∀ (n : Nat) (m : Mem) (di si : Word) (b : TieredArray), ((m.copy64 d di s si n).arr64 b).size = (m.arr64 b).size
  | 0, _, _, _, _ => rfl
  | n + 1, m, di, si, b => by
    simp only [Mem.copy64]; rw [Mem.size_copy64 d s n, L.Mem.size64_set64]

theorem Mem.size8_copy64 (d : TieredArray) (s : TieredArray) :
    ∀ (n : Nat) (m : Mem) (di si : Word) (a : ArrId), ((m.copy64 d di s si n).arr8 a).size = (m.arr8 a).size
  | 0, _, _, _, _ => rfl
  | n + 1, m, di, si, a => by simp only [Mem.copy64]; rw [Mem.size8_copy64 d s n]; rfl

theorem Mem.size_copy8w (d : TieredArray) (bs : Array UInt8) :
    ∀ (n : Nat) (m : Mem) (di si : Word) (b : TieredArray), ((m.copy8w d di bs si n).arr64 b).size = (m.arr64 b).size
  | 0, _, _, _, _ => rfl
  | n + 1, m, di, si, b => by
    simp only [Mem.copy8w]; rw [Mem.size_copy8w d bs n, L.Mem.size64_set64]

theorem Mem.size8_copy8w (d : TieredArray) (bs : Array UInt8) :
    ∀ (n : Nat) (m : Mem) (di si : Word) (a : ArrId), ((m.copy8w d di bs si n).arr8 a).size = (m.arr8 a).size
  | 0, _, _, _, _ => rfl
  | n + 1, m, di, si, a => by simp only [Mem.copy8w]; rw [Mem.size8_copy8w d bs n]; rfl

/-- The facts survive a change of the memory that keeps the sizes. -/
theorem Facts.Holds.memOnly {fa : Facts} {σ σ' : St} (h : fa.Holds σ) (hl : σ'.loc = σ.loc)
    (hs : SameSizes σ σ') : fa.Holds σ' :=
  h.frame (fun _ _ y _ => by rw [hl]) (fun _ _ => by rw [hl]) hs

theorem setLocs_loc_out : ∀ (xs : List Var) (σ : St) (r : List Word) (y : Var), y ∉ xs →
    (σ.setLocs xs r).loc y = σ.loc y
  | [], _, _, _, _ => rfl
  | x :: xs, σ, r, y, h => by
    rw [St.setLocs, setLocs_loc_out xs _ _ y (fun h' => h (List.mem_cons_of_mem _ h'))]
    have : y ≠ x := fun h' => h (h' ▸ List.mem_cons_self)
    simp [St.setLoc, this]

theorem setLocs_mem : ∀ (xs : List Var) (σ : St) (r : List Word), (σ.setLocs xs r).mem = σ.mem
  | [], _, _ => rfl
  | x :: xs, σ, r => by rw [St.setLocs, setLocs_mem xs]; rfl

theorem evalArgsP_each {σ : St} : ∀ {es : List Expr} {vs : List Word}, evalArgsP σ es = .ok vs →
    ∀ e ∈ es, ∃ v, evalP σ e = .ok v
  | [], _, _, _, h => by simp at h
  | e :: es, vs, h, e', he' => by
    simp only [evalArgsP] at h
    obtain ⟨v, hv, h⟩ := bind_ok h
    obtain ⟨ws, hws, -⟩ := bind_ok h
    rcases List.mem_cons.mp he' with rfl | hm
    · exact ⟨v, hv⟩
    · exact evalArgsP_each hws e' hm

theorem argsLoads_sound {σ : St} {es : List Expr} {vs : List Word} (h : evalArgsP σ es = .ok vs) :
    LoadsOk σ (es.flatMap Expr.loads) := fun f hf => by
  obtain ⟨e, he, hfe⟩ := List.mem_flatMap.mp hf
  obtain ⟨v, hv⟩ := evalArgsP_each h e he
  exact loads_sound hv f hfe

/-! ## One statement -/

/-- What a run of `s` from `σ` to `σ'` with signal `r` keeps, when the facts `fa` hold in `σ`: the
arrays' sizes, the locals `s` does not write; at a normal end the facts after `s`; a `break` only
from a statement with one. -/
structure PostOk (fa : Facts) (s : Stmt) (r : Sig) (σ σ' : St) : Prop where
  size : SameSizes σ σ'
  loc : ∀ y, y ∉ Stmt.writes s → σ'.loc y = σ.loc y
  post : r = .normal → FHolds (postF (some fa) s) σ'
  brk : r = .brk → Stmt.hasBrk s = true

/-- Every run of `run` keeps what `PostOk` says. -/
def FSound (run : Stmt → St → Except Err (Sig × St)) : Prop :=
  ∀ s σ (fa : Facts) r σ', run s σ = .ok (r, σ') → fa.Holds σ → PostOk fa s r σ σ'

/-- A statement that keeps the locals and the sizes and has no facts of its own. -/
theorem PostOk.same {fa : Facts} {s : Stmt} {σ σ' : St} (hf : fa.Holds σ) (hl : σ'.loc = σ.loc)
    (hs : SameSizes σ σ') (hp : postF (some fa) s = some fa) :
    PostOk fa s .normal σ σ' :=
  ⟨hs, fun y _ => by rw [hl], fun _ => by rw [hp]; exact hf.memOnly hl hs, fun h => by cases h⟩

/-- A statement that changes only the memory and keeps the sizes: the facts `f` after it, true
before it, stay true. -/
theorem PostOk.store {fa : Facts} {s : Stmt} {σ σ' : St} (hl : σ'.loc = σ.loc)
    (hs : SameSizes σ σ') {f : Facts} (hp : postF (some fa) s = some f) (hfh : f.Holds σ) :
    PostOk fa s .normal σ σ' :=
  ⟨hs, fun y _ => by rw [hl], fun _ => by rw [hp]; exact hfh.memOnly hl hs, fun h => by cases h⟩

theorem invoke_sizes {p : Prog} {K : Stmt → M Sig} (hK : FSound fun s σ => (K s).run σ) {f : FnName}
    {vs rs : List Word} {σ σ' : St} (h : (invoke p K f vs).run σ = .ok (rs, σ')) :
    σ'.loc = σ.loc ∧ SameSizes σ σ' := by
  simp only [invoke, lookupFn, StateT.run_bind] at h
  split at h
  · rename_i fd _
    simp only [pure, bind, Except.bind] at h
    have hcall : (callFn K fd vs).run σ = .ok (rs, σ') := h
    simp only [callFn, pure, Except.pure, bind, Except.bind, StateT.bind, StateT.run, StateT.pure, modify,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe, MonadStateOf.get, StateT.get, set,
      MonadStateOf.set, StateT.set] at hcall
    cases hr : K fd.body { σ with loc := Locals.init vs } with
    | error e => rw [hr] at hcall; cases hcall
    | ok q =>
      obtain ⟨r1, σ1⟩ := q
      rw [hr] at hcall
      cases hcall
      have := (hK fd.body { σ with loc := Locals.init vs } {} r1 σ1 hr (holds_empty _)).size
      exact ⟨rfl, this⟩
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

theorem warrP_ok_or {σ : St} (w : WArr) : (∃ a, warrP σ w = .ok a) ∨ ∃ e, warrP σ w = .error e := by
  cases warrP σ w with
  | ok a => exact .inl ⟨a, rfl⟩
  | error e => exact .inr ⟨e, rfl⟩

/-- **One step keeps the facts**, given that the next iterations and the callees (`K`) do. -/
theorem fsound_step (p : Prog) (K : Stmt → M Sig) (hK : FSound fun s σ => (K s).run σ) :
    FSound (stepRun p K) := by
  intro s
  induction s with
  | skip =>
    intro σ fa r σ' h hf
    rw [step_skip_run] at h; cases h
    exact PostOk.same hf rfl (SameSizes.refl _) rfl
  | set x e =>
    intro σ fa r σ' h hf
    rw [step_set_run] at h
    cases he : evalP σ e with
    | error x => rw [he] at h; cases h
    | ok v =>
      rw [he] at h; cases h
      exact ⟨SameSizes.of_mem rfl, fun y hy => by simp_all [St.setLoc, Stmt.writes],
        fun _ => hf.set he, fun h => by cases h⟩
  | st8 a i e =>
    intro σ fa r σ' h hf
    rw [step_st8_run] at h
    cases hi : evalP σ i with
    | error x => rw [hi] at h; cases h
    | ok j =>
      cases he : evalP σ e with
      | error x => rw [hi, he] at h; cases h
      | ok v =>
        rw [hi, he] at h
        simp only at h
        split at h
        · rename_i hj
          cases h
          refine PostOk.store rfl (SameSizes.set8 _ _ _ _) rfl ?_
          refine ((hf.addLoads ((loads_sound hi).append (loads_sound he))).addLt fun _ _ v' hv' => ?_)
          rw [hi] at hv'; cases hv'; exact hj
        · cases h
  | st64 a i e =>
    intro σ fa r σ' h hf
    rw [step_st64_run] at h
    cases hi : evalP σ i with
    | error x => rw [hi] at h; cases h
    | ok j =>
      cases he : evalP σ e with
      | error x => rw [hi, he] at h; cases h
      | ok v =>
        rw [hi, he] at h
        simp only at h
        split at h
        · rename_i hj
          cases h
          refine PostOk.store rfl (SameSizes.set64 _ _ _ _) rfl ?_
          refine ((hf.addLoads ((loads_sound hi).append (loads_sound he))).addLt fun _ _ v' hv' => ?_)
          rw [hi] at hv'; cases hv'; exact hj
        · cases h
  | st64t a t i e =>
    intro σ fa r σ' h hf
    rw [step_st64t_run] at h
    cases ht : evalP σ t with
    | error x => rw [ht] at h; cases h
    | ok u =>
      cases hi : evalP σ i with
      | error x => rw [ht, hi] at h; cases h
      | ok j =>
        cases he : evalP σ e with
        | error x => rw [ht, hi, he] at h; cases h
        | ok v =>
          rw [ht, hi, he] at h
          simp only at h
          split at h
          · rename_i hj
            cases h
            refine PostOk.store rfl (SameSizes.set64 _ _ _ _) rfl ?_
            have h1 := hf.addLoads (((loads_sound ht).append (loads_sound hi)).append (loads_sound he))
            cases hk : keyT a t with
            | none => exact h1
            | some k =>
              refine h1.addLt fun _ _ v' hv' => ?_
              rw [hi] at hv'; cases hv'; rw [keyT_len hk ht]; exact hj
          · cases h
  | st32t a t i e =>
    intro σ fa r σ' h hf
    rw [step_st32t_run] at h
    cases ht : evalP σ t with
    | error x => rw [ht] at h; cases h
    | ok u =>
      cases hi : evalP σ i with
      | error x => rw [ht, hi] at h; cases h
      | ok j =>
        cases he : evalP σ e with
        | error x => rw [ht, hi, he] at h; cases h
        | ok v =>
          rw [ht, hi, he] at h
          simp only at h
          split at h
          · rename_i hj
            cases h
            refine PostOk.store rfl (SameSizes.set32 _ _ _ _) rfl ?_
            have h1 := hf.addLoads (((loads_sound ht).append (loads_sound hi)).append (loads_sound he))
            cases hk : key32 a t with
            | none => exact h1
            | some k =>
              refine h1.addLt fun _ _ v' hv' => ?_
              rw [hi] at hv'; cases hv'; rw [key32_len hk ht]
              have hd : (j / 2).toNat = j.toNat / 2 := by simp [UInt64.toNat_div]
              omega
          · cases h
  | seq s t ihs iht =>
    intro σ fa r σ' h hf
    rw [step_seq_run] at h
    cases h1 : stepRun p K s σ with
    | error e => rw [h1] at h; cases h
    | ok q =>
      obtain ⟨r1, σ1⟩ := q
      rw [h1] at h
      have P1 := ihs σ fa r1 σ1 h1 hf
      cases r1 with
      | normal =>
        simp only at h
        have hp1 := P1.post rfl
        cases hq : postF (some fa) s with
        | none => rw [hq] at hp1; exact absurd hp1 id
        | some f =>
          rw [hq] at hp1
          have P2 := iht σ1 f r σ' h hp1
          refine ⟨P1.size.trans P2.size, fun y hy => ?_, fun hr => ?_, fun hr => ?_⟩
          · simp only [Stmt.writes, List.mem_append, not_or] at hy
            rw [P2.loc y hy.2, P1.loc y hy.1]
          · simp only [postF, hq]; exact P2.post hr
          · simp [Stmt.hasBrk, P2.brk hr]
      | brk =>
        simp only at h; cases h
        exact ⟨P1.size, fun y hy => P1.loc y (by simp_all [Stmt.writes]), (fun hr => by cases hr),
          fun _ => by simp [Stmt.hasBrk, P1.brk rfl]⟩
      | ret v =>
        simp only at h; cases h
        exact ⟨P1.size, fun y hy => P1.loc y (by simp_all [Stmt.writes]), (fun hr => by cases hr),
          (fun hr => by cases hr)⟩
  | ite c s t ihs iht =>
    intro σ fa r σ' h hf
    rw [step_ite_run] at h
    cases hc : evalCP σ c with
    | error e => rw [hc] at h; cases h
    | ok b =>
      cases b with
      | true =>
        rw [hc] at h
        have P := ihs σ _ r σ' h (hf.condAll hc)
        refine ⟨P.size, fun y hy => P.loc y (by simp_all [Stmt.writes]), fun hr => ?_,
          fun hr => by simp [Stmt.hasBrk, P.brk hr]⟩
        simp only [postF]; exact fholds_join (.inl (P.post hr))
      | false =>
        rw [hc] at h
        have P := iht σ _ r σ' h (hf.condAll hc)
        refine ⟨P.size, fun y hy => P.loc y (by simp_all [Stmt.writes]), fun hr => ?_,
          fun hr => by simp [Stmt.hasBrk, P.brk hr]⟩
        simp only [postF]; exact fholds_join (.inr (P.post hr))
  | «while» c s ih =>
    intro σ fa r σ' h hf
    rw [step_while_run] at h
    have hk0 := hf.killAll (Stmt.writes s) (σ' := σ) (fun _ _ => rfl) (SameSizes.refl _)
    cases hc : evalCP σ c with
    | error e => rw [hc] at h; cases h
    | ok b =>
      cases b with
      | false =>
        rw [hc] at h; cases h
        refine ⟨SameSizes.refl _, fun _ _ => rfl, fun _ => ?_, (fun hr => by cases hr)⟩
        simp only [postF]
        split
        · exact hk0
        · exact hk0.condAll hc
      | true =>
        rw [hc] at h
        simp only at h
        cases h1 : stepRun p K s σ with
        | error e => rw [h1] at h; cases h
        | ok q =>
          obtain ⟨r1, σ1⟩ := q
          rw [h1] at h
          have P1 := ih σ (fa.condAll c true) r1 σ1 h1 (hf.condAll hc)
          have hk1 : (fa.killAll (Stmt.writes s)).Holds σ1 := hf.killAll _ P1.loc P1.size
          cases r1 with
          | normal =>
            simp only at h
            have P2 := hK (.while c s) σ1 (fa.killAll (Stmt.writes s)) r σ' h hk1
            refine ⟨P1.size.trans P2.size, fun y hy => by rw [P2.loc y hy, P1.loc y hy], fun hr => ?_, P2.brk⟩
            have := P2.post hr
            simp only [postF, Facts.killAll_idem] at this ⊢
            exact this
          | brk =>
            simp only at h; cases h
            refine ⟨P1.size, P1.loc, fun _ => ?_, (fun hr => by cases hr)⟩
            simp only [postF, P1.brk rfl, ite_true]
            exact hk1
          | ret v =>
            simp only at h; cases h
            exact ⟨P1.size, P1.loc, (fun hr => by cases hr), (fun hr => by cases hr)⟩
  | brk =>
    intro σ fa r σ' h hf
    rw [step_brk_run] at h; cases h
    exact ⟨SameSizes.refl _, fun _ _ => rfl, (fun hr => by cases hr), fun _ => rfl⟩
  | ret es =>
    intro σ fa r σ' h hf
    rw [step_ret_run] at h
    cases he : evalArgsP σ es with
    | error e => rw [he] at h; cases h
    | ok vs =>
      rw [he] at h; cases h
      exact ⟨SameSizes.refl _, fun _ _ => rfl, (fun hr => by cases hr), (fun hr => by cases hr)⟩
  | call xs f args =>
    intro σ fa r σ' h hf
    rw [step_call_run] at h
    cases ha : evalArgsP σ args with
    | error e => rw [ha] at h; cases h
    | ok vs =>
      rw [ha] at h
      simp only at h
      cases hi : (invoke p K f vs).run σ with
      | error e => rw [hi] at h; cases h
      | ok q =>
        obtain ⟨rs, σ2⟩ := q
        rw [hi] at h; cases h
        obtain ⟨hl2, hs2⟩ := invoke_sizes hK hi
        have hs : SameSizes σ (σ2.setLocs xs rs) := by
          have := SameSizes.of_mem (σ := σ2) (σ' := σ2.setLocs xs rs) (setLocs_mem xs σ2 rs)
          exact hs2.trans this
        have hl : ∀ y, y ∉ xs → (σ2.setLocs xs rs).loc y = σ.loc y := fun y hy => by
          rw [setLocs_loc_out xs σ2 rs y hy, hl2]
        refine ⟨hs, fun y hy => hl y (by simpa [Stmt.writes] using hy), fun _ => ?_, (fun hr => by cases hr)⟩
        simp only [postF, fholds_some]
        exact (hf.addLoads (argsLoads_sound ha)).killAll xs hl hs
  | abort e =>
    intro σ fa r σ' h hf
    rw [step_abort_run] at h
    cases he : evalP σ e <;> rw [he] at h <;> cases h
  | gset g e =>
    intro σ fa r σ' h hf
    rw [step_gset_run] at h
    cases he : evalP σ e with
    | error x => rw [he] at h; cases h
    | ok v =>
      rw [he] at h; cases h
      exact PostOk.store rfl (SameSizes.setG _ _ _) rfl (hf.addLoads (loads_sound he))
  | copy64 d di s si n =>
    intro σ fa r σ' h hf
    rcases warrP_ok_or (σ := σ) d with ⟨da, hd⟩ | ⟨e, hd⟩ <;>
    rcases warrP_ok_or (σ := σ) s with ⟨sa, hs⟩ | ⟨e', hs⟩ <;>
    cases hi : evalP σ di <;> cases hj : evalP σ si <;> cases hn : evalP σ n <;>
    first
    | (rw [step_copy64_run p K σ d s di si n hd hs hi hj hn] at h
       split at h
       · cases h
         exact PostOk.same hf rfl ⟨fun a => Mem.size8_copy64 _ _ _ _ _ _ a, fun b => Mem.size_copy64 _ _ _ _ _ _ b⟩
           rfl
       · cases h)
    | (simp only [stepRun, step, StateT.run_bind, warr_run, evalE_run, hd] at h
       simp [Except.map, bind, Except.bind, hs, hi, hj, hn] at h)
  | copy8w d di s si n =>
    intro σ fa r σ' h hf
    rcases warrP_ok_or (σ := σ) d with ⟨da, hd⟩ | ⟨e, hd⟩ <;>
    cases hi : evalP σ di <;> cases hj : evalP σ si <;> cases hn : evalP σ n <;>
    first
    | (rw [step_copy8w_run p K σ d s di si n hd hi hj hn] at h
       split at h
       · cases h
         exact PostOk.same hf rfl ⟨fun a => Mem.size8_copy8w _ _ _ _ _ _ a, fun b => Mem.size_copy8w _ _ _ _ _ _ b⟩
           rfl
       · cases h)
    | (simp only [stepRun, step, StateT.run_bind, warr_run, evalE_run, hd] at h
       simp [Except.map, bind, Except.bind, hi, hj, hn] at h)
  | scan8 x s i e c =>
    intro σ fa r σ' h hf
    cases hi : evalP σ i <;> cases he : evalP σ e <;>
    first
    | (rw [step_scan8_run p K σ x s i e c hi he] at h
       split at h
       · cases h
         refine ⟨SameSizes.of_mem rfl, fun y hy => by simp_all [St.setLoc, Stmt.writes], fun _ => ?_,
           (fun hr => by cases hr)⟩
         simp only [postF, fholds_some]
         exact hf.kill x (fun y hy => by simp [St.setLoc, hy]) (SameSizes.of_mem rfl)
       · cases h)
    | (simp only [stepRun, step, StateT.run_bind, evalE_run, hi] at h
       simp [Except.map, bind, Except.bind, he] at h)

/-- **Every run of `exec p n` keeps the facts.** -/
theorem fsound_exec (p : Prog) : ∀ n, FSound fun s σ => (exec p n s).run σ
  | 0 => fun s σ fa r σ' h _ => by
    simp [exec, throw, throwThe, MonadExceptOf.throw, StateT.lift, StateT.run, bind,
      Except.bind] at h
  | n + 1 => fsound_step p (exec p n) (fsound_exec p n)

theorem fsound_stepExec (p : Prog) (n : Nat) : FSound (stepRun p (exec p n)) :=
  fsound_step p (exec p n) (fsound_exec p n)

/-! ## For the statement simulation -/

/-- The facts after `s`, at the end of a normal run of `s`. -/
theorem FSound.post {run : Stmt → St → Except Err (Sig × St)} (h : FSound run) {fa : Option Facts}
    {s : Stmt} {σ σ1 : St} (hf : FHolds fa σ) (hr : run s σ = .ok (.normal, σ1)) : FHolds (postF fa s) σ1 := by
  cases fa with
  | none => exact absurd hf id
  | some f => exact (h s σ f _ σ1 hr hf).post rfl

/-- The facts in the branch where `c` came out `pol`. -/
theorem fholds_condAll {fa : Option Facts} {σ : St} (hf : FHolds fa σ) {c : Cond} {pol : Bool}
    (hc : evalCP σ c = .ok pol) : FHolds (fa.map (·.condAll c pol)) σ := by
  cases fa with
  | none => exact absurd hf id
  | some f => exact hf.condAll hc

/-- The facts at the head of `while c s`, when it is entered. -/
theorem fholds_head {fa : Option Facts} {σ : St} (hf : FHolds fa σ) (s : Stmt) : FHolds (headF fa s) σ := by
  cases fa with
  | none => exact absurd hf id
  | some f => exact hf.killAll _ (fun _ _ => rfl) (SameSizes.refl _)

/-- The facts at the head of `while c s` hold again after a run of its body. -/
theorem fholds_head_after {run : Stmt → St → Except Err (Sig × St)} (h : FSound run) {fa : Option Facts}
    {s : Stmt} {σ σ1 : St} {r : Sig} (hf : FHolds (headF fa s) σ) (hr : run s σ = .ok (r, σ1)) :
    FHolds (headF fa s) σ1 := by
  cases fa with
  | none => exact absurd hf id
  | some f =>
    have P := h s σ _ r σ1 hr hf
    simp only [headF, Option.map_some, fholds_some] at hf ⊢
    rw [← Facts.killAll_idem]
    exact hf.killAll _ P.loc P.size

end L.Compiler
