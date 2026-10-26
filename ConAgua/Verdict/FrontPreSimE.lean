import ConAgua.Checker.PipePrelude

/-!
# The prelude simulation for errors (lane `verdicts-b`, helper `f2`)

`preSim` (`Checker/PreludeSim.lean`) relates the ok runs of a copied function `pre_f` to the ok
runs of `f` on the memory whose input is the prelude's bytes. Here the error runs: a run of
`pre_f` that fails with an error of nonzero code fails the same way as `f` on the renamed state
(`preSimE`). Only an `abort` has a nonzero code (`Err.code`); evaluation and the memory
operations fail only with `oob` (`NoAb`), so such an error comes from an `abort` statement (whose
value the copy computes as the original does, `ERel`) or from a callee (by induction on the fuel),
and every ok run before it is related by the ok simulation (`step_sim`, `invoke_sim_*`).
-/

namespace L.Checker

open L L.Compiler

/-! ## Computations that never abort -/

/-- Every error of `x` has code `0`. -/
def NoAb {α : Type} (x : M α) : Prop := ∀ s e, x.run s = .error e → e.code = 0

theorem NoAb.pure {α : Type} (a : α) : NoAb (Pure.pure a : M α) := by
  intro s e h; cases h

theorem NoAb.get : NoAb (MonadState.get : M St) := by
  intro s e h; cases h

theorem NoAb.set (t : St) : NoAb (MonadStateOf.set t : M PUnit) := by
  intro s e h; cases h

theorem NoAb.modify (f : St → St) : NoAb (modify f : M PUnit) := by
  intro s e h; cases h

theorem NoAb.oob {α : Type} : NoAb (throw Err.oob : M α) := by
  intro s e h; cases h; rfl

theorem NoAb.bind {α β : Type} {x : M α} {g : α → M β} (hx : NoAb x) (hg : ∀ a, NoAb (g a)) :
    NoAb (x >>= g) := by
  intro s e h
  rw [StateT.run_bind] at h
  cases h1 : x.run s with
  | error e1 => rw [h1] at h; cases h; exact hx s _ h1
  | ok q => rw [h1] at h; exact hg q.1 q.2 e h

theorem NoAb.ite {α : Type} {c : Prop} [Decidable c] {x y : M α} (hx : NoAb x) (hy : NoAb y) :
    NoAb (if c then x else y) := by
  split <;> assumption

theorem NoAb.dite {α : Type} {c : Prop} [Decidable c] {x : c → M α} {y : ¬ c → M α}
    (hx : ∀ h, NoAb (x h)) (hy : ∀ h, NoAb (y h)) : NoAb (if h : c then x h else y h) := by
  split
  · exact hx _
  · exact hy _

theorem NoAb.ld8 (a : ArrId) (j : Word) : NoAb (ld8 a j) := by
  intro s e h; rw [ld8_run] at h; split at h <;> cases h; rfl

theorem NoAb.ld64 (a : ArrId) (j : Word) : NoAb (ld64 a j) := by
  intro s e h; rw [ld64_run] at h; split at h <;> cases h; rfl

theorem NoAb.ldc (d : List UInt8) (j : Word) : NoAb (ldc d j) := by
  intro s e h; rw [ldc_run] at h; split at h <;> cases h; rfl

theorem NoAb.ld8x8 (b : BSrc) (j : Word) : NoAb (ld8x8 b j) := by
  intro s e h; rw [ld8x8_run] at h; split at h <;> cases h; rfl

theorem NoAb.st8 (a : ArrId) (j v : Word) : NoAb (st8 a j v) := by
  intro s e h; rw [st8_run] at h; split at h <;> cases h; rfl

theorem NoAb.st64 (a : ArrId) (j v : Word) : NoAb (st64 a j v) := by
  intro s e h; rw [st64_run] at h; split at h <;> cases h; rfl

macro "noab" : tactic => `(tactic| repeat (first
  | assumption
  | with_reducible exact NoAb.pure _ | with_reducible exact NoAb.get
  | with_reducible exact NoAb.set _ | with_reducible exact NoAb.modify _
  | with_reducible exact NoAb.oob
  | exact NoAb.ld8 _ _ | exact NoAb.ld64 _ _ | exact NoAb.ldc _ _ | exact NoAb.ld8x8 _ _
  | exact NoAb.st8 _ _ _ | exact NoAb.st64 _ _ _
  | with_reducible refine NoAb.bind ?_ fun _ => ?_
  | with_reducible refine NoAb.dite (fun _ => ?_) (fun _ => ?_)
  | with_reducible refine NoAb.ite ?_ ?_))

theorem noAb_evalE : ∀ e : Expr, NoAb (evalE e)
  | .const w => NoAb.pure w
  | .var x => by simp only [evalE]; noab
  | .bin op a b => by have := noAb_evalE a; have := noAb_evalE b; simp only [evalE]; noab
  | .ld8 a i => by have := noAb_evalE i; simp only [evalE]; noab
  | .ld64 a i => by have := noAb_evalE i; simp only [evalE]; noab
  | .len8 a => by simp only [evalE]; noab
  | .len64 a => by simp only [evalE]; noab
  | .cmpw c a b => by have := noAb_evalE a; have := noAb_evalE b; simp only [evalE]; noab
  | .ldc d i => by have := noAb_evalE i; simp only [evalE]; noab
  | .glob g => by simp only [evalE]; noab
  | .ld64t a t i => by have := noAb_evalE t; have := noAb_evalE i; simp only [evalE]; noab
  | .len64t a t => by have := noAb_evalE t; simp only [evalE]; noab
  | .ld8x8 s i => by have := noAb_evalE i; simp only [evalE]; noab

theorem noAb_evalC : ∀ c : Cond, NoAb (evalC c)
  | .cmp c a b => by have := noAb_evalE a; have := noAb_evalE b; simp only [evalC]; noab
  | .and p q => by have := noAb_evalC p; have := noAb_evalC q; simp only [evalC]; noab
  | .or p q => by have := noAb_evalC p; have := noAb_evalC q; simp only [evalC]; noab
  | .not p => by have := noAb_evalC p; simp only [evalC]; noab

theorem noAb_evalArgs : ∀ es : List Expr, NoAb (evalArgs es)
  | [] => NoAb.pure _
  | e :: es => by have := noAb_evalE e; have := noAb_evalArgs es; simp only [evalArgs]; noab

theorem noAb_warr : ∀ w : WArr, NoAb (warr w)
  | .plain a => NoAb.pure a
  | .tier a t => by have := noAb_evalE t; simp only [warr]; noab

macro "noabS" : tactic => `(tactic| repeat (first
  | exact noAb_evalE _ | exact noAb_evalC _ | exact noAb_evalArgs _ | exact noAb_warr _
  | assumption
  | with_reducible exact NoAb.pure _ | with_reducible exact NoAb.get
  | with_reducible exact NoAb.set _ | with_reducible exact NoAb.modify _
  | with_reducible exact NoAb.oob
  | exact NoAb.st8 _ _ _ | exact NoAb.st64 _ _ _
  | with_reducible refine NoAb.bind ?_ fun _ => ?_
  | with_reducible refine NoAb.dite (fun _ => ?_) (fun _ => ?_)
  | with_reducible refine NoAb.ite ?_ ?_))

/-! ## Error runs -/

/-- `k` fails on the copy `c` with a nonzero code only as on the original `o`. -/
def KRelE (k : Stmt → M Sig) (c o : Stmt) : Prop := ∀ (s : St) (e : Err),
  0 < s.mem.bytes.size → (k c).run s = .error e → e.code ≠ 0 → (k o).run (s.setIn preIn) = .error e

theorem run_bind_error {α β : Type} {x : M α} {g : α → M β} {s : St} {e : Err}
    (h : (x >>= g).run s = .error e) :
    x.run s = .error e ∨ ∃ a s', x.run s = .ok (a, s') ∧ (g a).run s' = .error e := by
  rw [StateT.run_bind] at h
  cases hx : x.run s with
  | error e' => rw [hx] at h; cases h; exact .inl rfl
  | ok q => rw [hx] at h; exact .inr ⟨q.1, q.2, rfl, h⟩

theorem run_bind_error_of {α β : Type} {x : M α} {g : α → M β} {s : St} {a : α} {s' : St} {e : Err}
    (hx : x.run s = .ok (a, s')) (hg : (g a).run s' = .error e) : (x >>= g).run s = .error e := by
  rw [StateT.run_bind, hx]; exact hg

theorem run_bind_error_left {α β : Type} {x : M α} {g : α → M β} {s : St} {e : Err}
    (hx : x.run s = .error e) : (x >>= g).run s = .error e := by
  rw [StateT.run_bind, hx]; rfl

/-- The first step of a `>>=` that never aborts: an error of nonzero code comes from the rest. -/
theorem bind_noAb {α β : Type} {x : M α} {g : α → M β} {s : St} {e : Err} (hx : NoAb x)
    (h : (x >>= g).run s = .error e) (hk : e.code ≠ 0) :
    ∃ a s', x.run s = .ok (a, s') ∧ (g a).run s' = .error e := by
  rcases run_bind_error h with h1 | h1
  · exact absurd (hx s e h1) hk
  · exact h1

theorem callFn_simE {k : Stmt → M Sig} {dc dd : FunDecl} (hk : KRelE k dc.body dd.body)
    (vs : List Word) (s : St) (e : Err) (h0 : 0 < s.mem.bytes.size)
    (h : (callFn k dc vs).run s = .error e) (hc : e.code ≠ 0) :
    (callFn k dd vs).run (s.setIn preIn) = .error e := by
  unfold callFn at h ⊢
  obtain ⟨s2, s3, h3, h4⟩ := bind_noAb NoAb.get h hc
  simp only [StateT.run_get] at h3
  obtain ⟨rfl, rfl⟩ := h3
  obtain ⟨u, s4, h5, h6⟩ := bind_noAb (NoAb.set _) h4 hc
  simp only [StateT.run_set] at h5
  obtain ⟨-, rfl⟩ := h5
  refine run_bind_error_of (s' := s.setIn preIn) (a := s.setIn preIn) rfl ?_
  refine run_bind_error_of (a := ()) (s' := { s with loc := Locals.init vs }.setIn preIn) rfl ?_
  rcases run_bind_error h6 with h7 | ⟨rr, s5, h7, h8⟩
  · exact run_bind_error_left (hk _ e h0 h7 hc)
  · have : NoAb ((fun r => do
        modify fun s' : St => { s' with loc := s.loc }
        Pure.pure r.retVal) rr : M (List Word)) := by noab
    exact absurd (this s5 e h8) hc

/-! ## Abort values that do not read the input -/

/-- Every `abort`'s value reads no byte of array `0` (so the copy and the original abort with the
same code). -/
def _root_.L.Stmt.abNoIn : Stmt → Bool
  | .abort e => e.noIn
  | .seq s t => s.abNoIn && t.abNoIn
  | .ite _ s t => s.abNoIn && t.abNoIn
  | .while _ s => s.abNoIn
  | _ => true

theorem abNoIn_preS (t : NTree) : ∀ s : Stmt, (preS t s).abNoIn = s.abNoIn
  | .seq s u => by simp only [preS, Stmt.abNoIn, abNoIn_preS t s, abNoIn_preS t u]
  | .ite c s u => by simp only [preS, Stmt.abNoIn, abNoIn_preS t s, abNoIn_preS t u]
  | .while c s => by simp only [preS, Stmt.abNoIn, abNoIn_preS t s]
  | .skip | .brk | .abort _ | .set .. | .gset .. | .st8 .. | .st64 .. | .ret _ | .call .. | .st64t ..
  | .copy64 .. | .copy8w .. | .scan8 .. => rfl

/-- Every function body of `p` aborts only with values that do not read the input. -/
def AbNoIn (p : Prog) : Prop := ∀ f fd, p.lookup f = some fd → fd.body.abNoIn = true

/-- The error runs of the copies and of the shared functions at fuel `n`. -/
def KSimE (p : Prog) (t : NTree) (S : FnName → Bool) (n : Nat) : Prop :=
  ∀ c o, Sim t S c o → c.abNoIn = true → KRelE (exec p n) c o

theorem lookupFn_err {p : Prog} {f : FnName} {s : St} {e : Err}
    (h : (lookupFn p f).run s = .error e) : e.code = 0 := by
  unfold lookupFn at h
  cases hp : p.lookup f with
  | none => rw [hp] at h; cases h; rfl
  | some fd => rw [hp] at h; cases h

theorem noAb_lookupFn (p : Prog) (f : FnName) : NoAb (lookupFn p f) :=
  fun _ _ h => lookupFn_err h

theorem invoke_simE_copy {p : Prog} {t : NTree} {S : FnName → Bool} (hP : PreSimProg p t S)
    (hA : AbNoIn p) (n : Nat) (ih : KSimE p t S n) (g : FnName) (hg : isCopied t g = true)
    (vs : List Word) (s : St) (e : Err) (h0 : 0 < s.mem.bytes.size)
    (h : (invoke p (exec p n) ("pre_" ++ g) vs).run s = .error e) (hc : e.code ≠ 0) :
    (invoke p (exec p n) g vs).run (s.setIn preIn) = .error e := by
  unfold invoke at h ⊢
  obtain ⟨fd', s2, h1, h2⟩ := bind_noAb (noAb_lookupFn _ _) h hc
  obtain ⟨hl', rfl⟩ := lookupFn_ok h1
  obtain ⟨fd, hl⟩ := Option.isSome_iff_exists.mp (hP.defined g hg)
  obtain ⟨hcp, hst, hcl⟩ := hP.copy g fd hg hl
  rw [hcp] at hl'; cases hl'
  have ha : (preFn t fd).body.abNoIn = true := by
    simp only [preFn]; rw [abNoIn_preS]; exact hA g fd hl
  exact run_bind_error_of (lookupFn_run hl _)
    (callFn_simE (ih _ _ (sim_preS _ hst hcl) ha) vs s e h0 h2 hc)

theorem invoke_simE_shared {p : Prog} {t : NTree} {S : FnName → Bool} (hP : PreSimProg p t S)
    (hA : AbNoIn p) (n : Nat) (ih : KSimE p t S n) (g : FnName) (hg : S g = true) (vs : List Word)
    (s : St) (e : Err) (h0 : 0 < s.mem.bytes.size)
    (h : (invoke p (exec p n) g vs).run s = .error e) (hc : e.code ≠ 0) :
    (invoke p (exec p n) g vs).run (s.setIn preIn) = .error e := by
  unfold invoke at h ⊢
  obtain ⟨fd, s2, h1, h2⟩ := bind_noAb (noAb_lookupFn _ _) h hc
  obtain ⟨hl, rfl⟩ := lookupFn_ok h1
  obtain ⟨-, hn, hcl⟩ := hP.shared g fd hg hl
  exact run_bind_error_of (lookupFn_run hl _)
    (callFn_simE (ih _ _ (sim_noIn _ hn hcl) (hA g fd hl)) vs s e h0 h2 hc)

/-- A statement whose step never aborts (no `abort`, call or compound statement inside). -/
theorem krelE_of_noAb {k : Stmt → M Sig} {c o : Stmt} (h : NoAb (k c)) : KRelE k c o :=
  fun s e _ he hc => absurd (h s e he) hc

theorem setLocs_noAb (xs : List Var) (rs : List Word) :
    NoAb (do setLocs xs rs; return Sig.normal : M Sig) := by
  simp only [setLocs]; noabS

theorem step_simE {p : Prog} {t : NTree} {S : FnName → Bool} (hP : PreSimProg p t S)
    (hA : AbNoIn p) (n : Nat) (ihn : KSimE p t S n) {c o : Stmt} (hs : Sim t S c o) :
    c.abNoIn = true → KRelE (step p (exec p n)) c o := by
  induction hs with
  | «skip» => exact fun _ => krelE_of_noAb (by simp only [step]; noabS)
  | brk => exact fun _ => krelE_of_noAb (by simp only [step]; noabS)
  | «abort» ex =>
    intro ha s e h0 h hc
    simp only [Stmt.abNoIn] at ha
    simp only [step] at h ⊢
    obtain ⟨v, s2, h1, h2⟩ := bind_noAb (noAb_evalE _) h hc
    obtain ⟨rfl, h1'⟩ := erel_noIn ex ha s v s2 h0 h1
    exact run_bind_error_of h1' h2
  | set x _ => exact fun _ => krelE_of_noAb (by simp only [step, setLoc]; noabS)
  | gset g _ => exact fun _ => krelE_of_noAb (by simp only [step, setG]; noabS)
  | st8 _ _ _ => exact fun _ => krelE_of_noAb (by simp only [step]; noabS)
  | st64 _ _ _ => exact fun _ => krelE_of_noAb (by simp only [step]; noabS)
  | st64t _ _ _ _ => exact fun _ => krelE_of_noAb (by simp only [step]; noabS)
  | copy64 _ _ _ _ _ => exact fun _ => krelE_of_noAb (by
      simp only [step]; noabS)
  | copy8w _ _ _ _ _ => exact fun _ => krelE_of_noAb (by
      simp only [step]; noabS)
  | scan8 _ _ _ _ _ => exact fun _ => krelE_of_noAb (by
      simp only [step, setLoc]; noabS)
  | ret _ => exact fun _ => krelE_of_noAb (by simp only [step]; noabS)
  | seq h1 h2 ih1 ih2 =>
    intro ha s e h0 h hc
    simp only [Stmt.abNoIn, Bool.and_eq_true] at ha
    simp only [step] at h ⊢
    rcases run_bind_error h with h3 | ⟨a, s2, h3, h4⟩
    · exact run_bind_error_left (ih1 ha.1 s e h0 h3 hc)
    · obtain ⟨h3', hK⟩ := step_sim hP n (ksim hP n) h1 s a s2 h0 h3
      refine run_bind_error_of h3' ?_
      cases a with
      | normal => exact ih2 ha.2 s2 e (hK.pos h0) h4 hc
      | brk => cases h4
      | ret v => cases h4
  | ite hcc h1 h2 ih1 ih2 =>
    intro ha s e h0 h hc
    simp only [Stmt.abNoIn, Bool.and_eq_true] at ha
    simp only [step] at h ⊢
    obtain ⟨b, s2, h3, h4⟩ := bind_noAb (noAb_evalC _) h hc
    obtain ⟨rfl, h3'⟩ := hcc s b s2 h0 h3
    refine run_bind_error_of h3' ?_
    cases b
    · exact ih2 ha.2 s e h0 h4 hc
    · exact ih1 ha.1 s e h0 h4 hc
  | «while» hcc hb ihb =>
    intro ha s e h0 h hc
    have ha' := ha
    simp only [Stmt.abNoIn] at ha'
    simp only [step] at h ⊢
    obtain ⟨b, s2, h3, h4⟩ := bind_noAb (noAb_evalC _) h hc
    obtain ⟨rfl, h3'⟩ := hcc s b s2 h0 h3
    refine run_bind_error_of h3' ?_
    cases b
    · cases h4
    · rcases run_bind_error h4 with h5 | ⟨a, s3, h5, h6⟩
      · exact run_bind_error_left (ihb ha' s e h0 h5 hc)
      · obtain ⟨h5', hK⟩ := step_sim hP n (ksim hP n) hb s a s3 h0 h5
        refine run_bind_error_of h5' ?_
        cases a with
        | normal => exact ihn _ _ (.while hcc hb) ha s3 e (hK.pos h0) h6 hc
        | brk => cases h6
        | ret v => cases h6
  | callC xs hg ha =>
    intro _ s e h0 h hc
    simp only [step] at h ⊢
    obtain ⟨vs, s2, h1, h2⟩ := bind_noAb (noAb_evalArgs _) h hc
    obtain ⟨rfl, h1'⟩ := ha s vs s2 h0 h1
    refine run_bind_error_of h1' ?_
    rcases run_bind_error h2 with h3 | ⟨rs, s3, h3, h4⟩
    · exact run_bind_error_left (invoke_simE_copy hP hA n ihn _ hg vs s e h0 h3 hc)
    · exact absurd (setLocs_noAb xs rs s3 e h4) hc
  | callS xs hg ha =>
    intro _ s e h0 h hc
    simp only [step] at h ⊢
    obtain ⟨vs, s2, h1, h2⟩ := bind_noAb (noAb_evalArgs _) h hc
    obtain ⟨rfl, h1'⟩ := ha s vs s2 h0 h1
    refine run_bind_error_of h1' ?_
    rcases run_bind_error h2 with h3 | ⟨rs, s3, h3, h4⟩
    · exact run_bind_error_left (invoke_simE_shared hP hA n ihn _ hg vs s e h0 h3 hc)
    · exact absurd (setLocs_noAb xs rs s3 e h4) hc

theorem ksimE {p : Prog} {t : NTree} {S : FnName → Bool} (hP : PreSimProg p t S) (hA : AbNoIn p) :
    ∀ n, KSimE p t S n
  | 0 => fun _ _ _ _ s e _ h hc => by cases h; exact absurd rfl hc
  | n + 1 => fun _ _ hs ha => step_simE hP hA n (ksimE hP hA n) hs ha

/-- **The simulation, for errors**: a run of the copy `pre_f` that fails with a nonzero code
fails the same way as `f` on the state whose input is the prelude's bytes. -/
theorem preSimE {p : Prog} {t : NTree} {S : FnName → Bool} (hP : PreSimProg p t S) (hA : AbNoIn p)
    (n : Nat) (f : FnName) (hf : isCopied t f = true) (vs : List Word) (s : St) (e : Err)
    (h0 : 0 < s.mem.bytes.size)
    (h : (invoke p (exec p n) ("pre_" ++ f) vs).run s = .error e) (hk : e.code ≠ 0) :
    (invoke p (exec p n) f vs).run (s.setIn preIn) = .error e :=
  invoke_simE_copy hP hA n (ksimE hP hA n) f hf vs s e h0 h hk

end L.Checker
