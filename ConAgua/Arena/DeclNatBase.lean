import ConAgua.L.ModelGen
import ConAgua.Arena.DeclHeader
import ConAgua.Arena.WhnfCoreApp
import ConAgua.Arena.WhnfDelta
import ConAgua.Arena.IndView
import ConAgua.Arena.SimLib

/-!
# The structural-`Nat` gate: shared pieces (lane `decls3`, helper `decls3-nat`)

`DeclArmsNat.lean`'s L functions call master's interners and the pin readers; this file gives
them, under the stage relation, in the form the gate's refinements chain.

* **`CallRef p f args pre op post`**: every returning run of `f(args)` (`callW`, lane `whnf`'s
  "a call as a function of the memory") from `pre` is a successful run of the twin's `op`, `post`
  relating the memories, the twin state after, the result words and the twin result. It is the
  `RefAM` shape (`CallRef.refAM`) with the L fuel and the locals quantified away, so a caller's
  word model calls its callees through `callW` (one generic `callW_spec`, no callee model), and
  its relational lemma applies the callees' `CallRef`s to the runs.
* The primitives: `pin_at`, `pin_word`, `iw_alloc`, the record builders, `e_view`, `env_find`,
  `const_e`, `intern_const`, `intern_fvar`, `intern_succ`, `mk_*`, `ci_to_cv`.
-/

set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The word model's bind: the callee's result words and memory into the continuation. -/
def ntBW {β : Type} (x : Option (List Word × Mem)) (k : List Word → Mem → Option β) : Option β :=
  match x with
  | none => none
  | some (r, m) => k r m

@[simp, grind =] theorem bW_none {β : Type} (k : List Word → Mem → Option β) : ntBW none k = none := rfl
@[simp, grind =] theorem bW_some {β : Type} (r : List Word) (m : Mem) (k : List Word → Mem → Option β) :
    ntBW (some (r, m)) k = k r m := rfl

/-- **A refinement of the twin's `op` by the call `f(args)`**, over the runs `callW` gives. -/
def CallRef {α : Type} (p : Prog) (f : FnName) (args : List Word) (pre : Mem → AState → Prop)
    (op : AM α) (post : Mem → Mem → AState → List Word → α → Prop) : Prop :=
  ∀ (n : Nat) (m : Mem) (a : AState) (r : List Word) (m' : Mem), pre m a →
    callW p n f args m = some (r, m') → ∃ x a', op.run a = .ok (x, a') ∧ post m m' a' r x

/-- `CallRef` is `RefAM`. -/
theorem CallRef.refAM {α : Type} [Inhabited α] {p : Prog} {f : FnName} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    (h : CallRef p f args pre op post) : RefAM p f args pre op post := by
  intro n s₀ a₀ hpre
  refine triple_post (callW_spec p n f args s₀) ?_
  rintro r s' ⟨hl, hc⟩
  obtain ⟨x, a', hrun, hp⟩ := h n s₀.mem a₀ r s'.mem hpre hc
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hp⟩

/-- A `CallRef` from triples at every fuel and state. -/
theorem CallRef.of_triple {α : Type} {p : Prog} {f : FnName} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    (h : ∀ (n : Nat) (s₀ : St) (a₀ : AState), pre s₀.mem a₀ →
      ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => LocEq s' s₀ ∧ ∃ x a', op.run a₀ = .ok (x, a') ∧ post s₀.mem s'.mem a' r x; ⊤⦄) :
    CallRef p f args pre op post := by
  intro n m a r m' hpre hc
  obtain ⟨s', rfl, -, hx⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (h n _ a hpre) hc
  exact hx

/-- A `CallRef` from its successor fuels (fuel `0` has no returning run). -/
theorem CallRef.of_succ {α : Type} {p : Prog} {f : FnName} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    (h : ∀ (k : Nat) (m : Mem) (a : AState) (r : List Word) (m' : Mem), pre m a →
      callW p (k + 1) f args m = some (r, m') → ∃ x a', op.run a = .ok (x, a') ∧ post m m' a' r x) :
    CallRef p f args pre op post := by
  intro n m a r m' hpre hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ k => exact h k m a r m' hpre hc

/-- A model equation from a returning call: the model of the spec triple at the call's memory. -/
theorem callW_model {p : Prog} {k : Nat} {f : FnName} {args : List Word} {m m' : Mem}
    {r : List Word} {M : Mem → Option (List Word × Mem)}
    (hspec : ∀ s₀ : St, ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) f args
      ⦃fun r s' => LocEq s' s₀ ∧ M s₀.mem = some (r, s'.mem); ⊤⦄)
    (hc : callW p (k + 1) f args m = some (r, m')) : M m = some (r, m') := by
  obtain ⟨s', rfl, -, hM⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (hspec _) hc
  exact hM

/-! ### `Sim` over `ntBW` models -/

/-- A `CallRef` at a state meeting its precondition is a `Sim` of the call. -/
theorem CallRef.sim {α : Type} {p : Prog} {f : FnName} {args : List Word} {pre : Mem → AState → Prop} {op : AM α}
    {post : Mem → Mem → AState → List Word → α → Prop} (h : CallRef p f args pre op post) {n : Nat}
    {m : Mem} {a : AState} (hp : pre m a) :
    Sim (callW p n f args m) op a (fun r x m' a' => post m m' a' r x) :=
  fun r m' e => h n m a r m' hp e

/-- **A `CallRef` from a `Sim` of the model** its spec states. -/
theorem CallRef.of_sim {α : Type} {p : Prog} {f : FnName} {args : List Word} {pre : Mem → AState → Prop} {op : AM α}
    {post : Mem → Mem → AState → List Word → α → Prop} {M : Nat → Mem → Option (List Word × Mem)}
    (hspec : ∀ k s₀, ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) f args
      ⦃fun r s' => LocEq s' s₀ ∧ M k s₀.mem = some (r, s'.mem); ⊤⦄)
    (h : ∀ k m a, pre m a → Sim (M k m) op a (fun r x m' a' => post m m' a' r x)) :
    CallRef p f args pre op post :=
  CallRef.of_succ fun k m a r m' hp hc => h k m a hp r m' (callW_model (hspec k) hc)

/-- `Sim.bindK` for an `ntBW` step. -/
theorem _root_.L.Arena.Sim.ntB {α δ γ : Type} {body : List Word → Mem → Option (γ × Mem)} {mo : Option (List Word × Mem)}
    {op : AM α} {g : α → AM δ} {a : AState} {Q : List Word → α → Mem → AState → Prop}
    {R : γ → δ → Mem → AState → Prop} (h1 : Sim mo op a Q)
    (h2 : ∀ r x m₁ a₁, Q r x m₁ a₁ → Sim (body r m₁) (g x) a₁ R) : Sim (ntBW mo body) (op >>= g) a R :=
  Sim.bindK (K := (ntBW · body)) rfl (fun _ _ => rfl) h1 h2

/-- The last `ntBW` step of a model, returning `f r` for the callee's `r`: the twin is the callee's. -/
theorem _root_.L.Arena.Sim.ntRet {α γ : Type} {f : List Word → γ} {mo : Option (List Word × Mem)} {op : AM α}
    {a : AState} {Q : List Word → α → Mem → AState → Prop} {R : γ → α → Mem → AState → Prop}
    (h1 : Sim mo op a Q) (h2 : ∀ r x m₁ a₁, op.run a = .ok (x, a₁) → Q r x m₁ a₁ → R (f r) x m₁ a₁) :
    Sim (ntBW mo fun r m => some (f r, m)) op a R := by
  intro r m' e
  cases hmo : mo with
  | none => rw [hmo] at e; cases e
  | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hmo, bW_some, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨x, a', h, hQ⟩ := h1 r₁ m₁ hmo
    exact ⟨x, a', h, h2 _ _ _ _ h hQ⟩

/-- A weaker postcondition. -/
theorem CallRef.mono {α : Type} {p : Prog} {f : FnName} {args : List Word}
    {pre pre' : Mem → AState → Prop} {op : AM α} {post post' : Mem → Mem → AState → List Word → α → Prop}
    (h : CallRef p f args pre op post) (hpre : ∀ m a, pre' m a → pre m a)
    (hpost : ∀ m m' a r x, post m m' a r x → post' m m' a r x) : CallRef p f args pre' op post' := by
  intro n m a r m' hp hc
  obtain ⟨x, a', hr, hq⟩ := h n m a r m' (hpre m a hp) hc
  exact ⟨x, a', hr, hpost _ _ _ _ _ hq⟩

/-! ## Twin-free callees: the pool and the records -/

/-- A call with no twin counterpart (the pool, a record, a slice): `post` on the memories. -/
def FRef (p : Prog) (f : FnName) (args : List Word) (pre : Mem → Prop)
    (post : Mem → Mem → List Word → Prop) : Prop :=
  ∀ (n : Nat) (m : Mem) (r : List Word) (m' : Mem), pre m →
    callW p n f args m = some (r, m') → post m m' r

/-- **The pool grew and the stage relation survives**, at every environment and twin state. -/
def StKeep (m m' : Mem) : Prop :=
  IWGrow m m' ∧ ∀ (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (a : AState),
    StageR dn vis fe m a → StageR dn vis fe m' a

theorem StKeep.refl (m : Mem) : StKeep m m := ⟨IWGrow.refl m, fun _ _ _ _ h => h⟩

theorem StKeep.trans {m₁ m₂ m₃ : Mem} (h₁ : StKeep m₁ m₂) (h₂ : StKeep m₂ m₃) : StKeep m₁ m₃ :=
  ⟨h₁.1.trans h₂.1, fun dn vis fe a h => h₂.2 dn vis fe a (h₁.2 dn vis fe a h)⟩

theorem StKeep.of_eq {m m' : Mem} (h : m' = m) : StKeep m m' := h ▸ StKeep.refl m

/-- The `StageR` of a twin-state keep. -/
theorem StKeep.stage {m m' : Mem} (h : StKeep m m') {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} (hS : StageR dn vis fe m a) : StageR dn vis fe m' a :=
  h.2 dn vis fe a hS

/-! ### `pin_at`, `pin_word` -/

theorem pinAt_ref {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (p : Prog)
    (hp : p.lookup "pin_at" = some pinAtL) (i : Word) :
    CallRef p "pin_at" [i] (StageR dn vis fe) (pinAt i.toNat) (KeepPost dn vis fe decW0N) := by
  refine CallRef.of_triple fun n s₀ a₀ hS => ?_
  refine triple_post (pinAt_refines p hp n s₀ a₀ hS.1.pins i) ?_
  rintro r s' ⟨hm, hl, hlt, hrun⟩
  refine ⟨hl, decI (r.headD 0), a₀, hrun, ?_⟩
  rw [hm]
  exact ⟨hS, IWGrow.refl _, hlt, rfl⟩

/-- The same at a named slot. -/
theorem pinSlot_ref {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (p : Prog)
    (hp : p.lookup "pin_at" = some pinAtL) (k : Word) (op : AM NIdx) (hop : op = pinAt k.toNat) :
    CallRef p "pin_at" [k] (StageR dn vis fe) op (KeepPost dn vis fe decW0N) := by
  subst hop; exact pinAt_ref p hp k

/-- The words `pin_word` returns, and that it leaves the memory. -/
theorem pinWord_model {m m' : Mem} {k : Word} {r : List Word} (h : pinWordW m k = some (r, m')) :
    m' = m ∧ pinW m 0 ≠ 0 ∧ r = [pinW m k.toNat] := by
  unfold pinWordW at h
  by_cases h0 : pinW m 0 = 0
  · simp [h0] at h
  · simp only [h0, if_false, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, h0, by simp [rdW, pinW]⟩

theorem pinWord_ref_aux {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {α : Type}
    (p : Prog) (hp : p.lookup "pin_word" = some pinWordL) (k : Word) (op : AM α)
    (dec : Mem → List Word → α → Prop)
    (hop : ∀ m a, StageR dn vis fe m a → pinW m 0 ≠ 0 →
      ∃ x, op.run a = .ok (x, a) ∧ dec m [pinW m k.toNat] x) :
    CallRef p "pin_word" [k] (StageR dn vis fe) op (KeepPost dn vis fe dec) := by
  refine CallRef.of_triple fun n s₀ a₀ hS => ?_
  refine triple_post (pinWord_specW p hp n s₀ k) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hmm, h0, rfl⟩ := pinWord_model hm
  obtain ⟨x, hrun, hd⟩ := hop _ _ hS h0
  rw [hmm]
  exact ⟨hl, x, a₀, hrun, hS, IWGrow.refl _, hd⟩

/-- The level-list decoder of a result word. -/
def decW0S (_m : Mem) (r : List Word) (e : LsIdx) : Prop := (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = e

theorem pinWord52_ref {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (p : Prog)
    (hp : p.lookup "pin_word" = some pinWordL) :
    CallRef p "pin_word" [52] (StageR dn vis fe) pinEmptyLevels (KeepPost dn vis fe decW0S) :=
  pinWord_ref_aux p hp 52 _ _ fun m a hS h0 => by
    have hF := hS.1.pins.full h0
    exact ⟨_, pinEmptyLevels_run hF, hF.lv_lt.1, rfl⟩

theorem pinWord53_ref {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (p : Prog)
    (hp : p.lookup "pin_word" = some pinWordL) :
    CallRef p "pin_word" [53] (StageR dn vis fe) pinZeroLevel (KeepPost dn vis fe decW0L) :=
  pinWord_ref_aux p hp 53 _ _ fun m a hS h0 => by
    have hF := hS.1.pins.full h0
    exact ⟨_, pinZeroLevel_run hF, hF.lv_lt.2.1, rfl⟩

/-! ### `iw_alloc` -/

/-- What a returning `iw_alloc(k)` model leaves. -/
theorem allocW_post {m m1 : Mem} {k q : Word} (hw : allocW m k = some (q, m1)) (hI : IWOK m) :
    q = rdW (m.arr64 CTL) 200 ∧ m1 = allocMem m k ∧ StKeep m m1 ∧
      iwTop m + k.toNat ≤ (m.arr64 IW).size ∧ iwTop m1 = iwTop m + k.toNat := by
  obtain ⟨hI1, hE1, hsz, hEs, hct⟩ := hI
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hw hsz
  have hq' : q.toNat = iwTop m := by rw [hq]; rfl
  rw [hq'] at hroom
  refine ⟨hq, hm1, ⟨?_, fun dn vis fe a hS => (allocW_stage hw hS).1⟩, hroom, ?_⟩
  · rw [hm1]
    exact allocMem_grow m k (by simp only [iwTop] at hroom ⊢; omega) hct
  · rw [hm1]
    simp only [iwTop, allocMem, rdW_set64]
    rw [if_pos ⟨trivial, trivial, hct⟩, UInt64.toNat_add]
    simp only [iwTop] at hroom
    omega

theorem iwAlloc_fref (p : Prog) (hp : p.lookup "iw_alloc" = some iwAlloc) (k : Word) :
    FRef p "iw_alloc" [k] (fun m => IWOK m)
      (fun m m' r => r.headD 0 = rdW (m.arr64 CTL) 200 ∧ m' = allocMem m k ∧ StKeep m m' ∧
        iwTop m + k.toNat ≤ (m.arr64 IW).size ∧ iwTop m' = iwTop m + k.toNat) := by
  intro n m r m' hI hc
  obtain ⟨s', rfl, hl, hw⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iwAlloc_specW p hp n _ k) hc
  exact allocW_post hw hI
theorem FRef.of_succ {p : Prog} {f : FnName} {args : List Word} {pre : Mem → Prop}
    {post : Mem → Mem → List Word → Prop}
    (h : ∀ (k : Nat) (m : Mem) (r : List Word) (m' : Mem), pre m →
      callW p (k + 1) f args m = some (r, m') → post m m' r) : FRef p f args pre post := by
  intro n m r m' hpre hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ k => exact h k m r m' hpre hc

/-! ### Records -/

/-- A writer of `IW` and `CTL[200]` that grew the pool and left it in bounds keeps the stage
relation. -/
theorem stkeep_of_frame {m m' : Mem} (hf : MemFrame [IW] [200] m m') (hg : IWGrow m m')
    (hI : IWOK m) (htop : iwTop m' ≤ (m'.arr64 IW).size) : StKeep m m' := by
  obtain ⟨hI1, hE1, hsz, hEs, hct⟩ := hI
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hf.2.1 129 (by simp)
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp [EREC, IW]) (by decide)
  refine ⟨hg, fun dn vis fe a hS => ⟨CheckR.frame_iw hf hS.1, htop, ?_, ?_, ?_, ?_⟩⟩
  · simp only [erTop, h129, hE]; exact hE1
  · rw [hf.2.2.1 IW]; exact hsz
  · rw [hE]; exact hEs
  · rw [hf.2.2.1 CTL]; exact hct

/-- What a record builder leaves: its words at the old top, the pool grown. -/
def RecPost (m m' : Mem) (r : List Word) (ws : List Word) : Prop :=
  r.headD 0 = rdW (m.arr64 CTL) 200 ∧ StKeep m m' ∧ iwTop m + ws.length ≤ (m.arr64 IW).size ∧
    iwTop m' = iwTop m + ws.length ∧ ∀ j < ws.length, (m'.arr64 IW)[iwTop m + j]? = ws[j]?

/-- `alloc k` then the words `ws` written at the old top. -/
theorem recPost_wr (m : Mem) (ws : List Word) (k : Word) (hk : k.toNat = ws.length) (hI : IWOK m)
    (hroom : iwTop m + ws.length ≤ (m.arr64 IW).size) :
    RecPost m (wrIW (allocMem m k) (rdW (m.arr64 CTL) 200) ws) [rdW (m.arr64 CTL) 200] ws := by
  obtain ⟨hI1, hE1, hsz, hEs, hct⟩ := hI
  obtain ⟨hget, hg, hf, htop⟩ := recMem_post m ws k hk hct hroom hsz
  have hit : iwTop (wrIW (allocMem m k) (rdW (m.arr64 CTL) 200) ws) = iwTop m + ws.length := by
    simp only [iwTop, htop, UInt64.toNat_add]
    simp only [iwTop] at hroom
    rw [Nat.mod_eq_of_lt (by omega), hk]
  refine ⟨rfl, stkeep_of_frame hf hg ⟨hI1, hE1, hsz, hEs, hct⟩ ?_, hroom, hit, fun j hj => hget j hj⟩
  rw [hit, hf.2.2.1 IW]; exact hroom

theorem rec2_fref (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "rec2" = some rec2) (a b : Word) :
    FRef p "rec2" [a, b] (fun m => IWOK m)
      (fun m m' r => RecPost m m' r [a, b]) := by
  intro n m r m' hI hc
  obtain ⟨s', rfl, hl, hm, hq, hroom⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (rec2_spec p ha hp n _ a b hI.2.2.1) hc
  change s'.mem = rec2Mem m a b at hm
  change r.headD 0 = _ at hq
  rw [hm, rec2Mem_eq]
  have := recPost_wr m [a, b] 2 rfl hI (by simpa [iwTop] using hroom)
  obtain ⟨-, h2, h3, h4, h5⟩ := this
  exact ⟨hq, h2, h3, h4, h5⟩

theorem rec3_fref (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "rec3" = some rec3) (a b c : Word) :
    FRef p "rec3" [a, b, c] (fun m => IWOK m)
      (fun m m' r => RecPost m m' r [a, b, c]) := by
  intro n m r m' hI hc
  obtain ⟨s', rfl, hl, hm, hq, hroom⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (rec3_spec p ha hp n _ a b c hI.2.2.1) hc
  change s'.mem = rec3Mem m a b c at hm
  change r.headD 0 = _ at hq
  rw [hm, rec3Mem_eq]
  have := recPost_wr m [a, b, c] 3 rfl hI (by simpa [iwTop] using hroom)
  obtain ⟨-, h2, h3, h4, h5⟩ := this
  exact ⟨hq, h2, h3, h4, h5⟩

/-- The model of `sl_new1(x)` (the allocation through `callW`). -/
l_model ntSlNew1_specW (p : Prog) (hp : p.lookup "sl_new1" = some slNew1)
  fns [hp ↦ slNew1W list]
  specs [callW_spec p n "iw_alloc"]
  grind [arena_grind] bind ntBW simp [ntBW]

theorem slNew1_fref (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "sl_new1" = some slNew1) (x : Word) :
    FRef p "sl_new1" [x] (fun m => IWOK m)
      (fun m m' r => RecPost m m' r [x] ∧ r = [r.headD 0, 1]) := by
  refine FRef.of_succ fun k m r m' hI hc => ?_
  obtain ⟨s', rfl, hl, hw⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ntSlNew1_specW p hp (k + 1) _ x) hc
  change slNew1W p (k + 1) m x = some (r, s'.mem) at hw
  rw [slNew1W.arm1] at hw
  cases h1 : callW p k "iw_alloc" [1] m with
  | none => rw [h1] at hw; simp at hw
  | some q =>
    obtain ⟨r1, m1⟩ := q
    rw [h1, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, hm⟩ := hw
    obtain ⟨hq, hm1, hk, hroom, ht⟩ := iwAlloc_fref p ha 1 k m r1 m1 hI h1
    have := recPost_wr m [x] 1 rfl hI (by simpa using hroom)
    have e : s'.mem = wrIW (allocMem m 1) (rdW (m.arr64 CTL) 200) [x] := by
      rw [← hm, hm1, ← hq]; rfl
    rw [e]
    obtain ⟨-, h2, h3, h4, h5⟩ := this
    exact ⟨⟨hq, h2, h3, h4, h5⟩, rfl⟩

/-! ## Master's interners under the stage relation -/

/-- An interned `const` handle word is below `2^32` (lane `whnf`'s `ceinternW_hw`). -/
theorem ceinternW_hw' (m : Mem) (a : AState) (hR : ConstR m a) (f x : Word) (hf : f.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) (w : Word) (m' : Mem) (hI : ceinternW m f x = some (w, m')) :
    w.toNat < 2 ^ 32 := by
  have hI₂ := hI
  exact consInternM_lt constCS_wf hR hI₂

theorem fvinternW_hw (m : Mem) (a : AState) (hR : FVarR m a) (u ty : Word) (w : Word) (m' : Mem)
    (hI : fvinternW m u ty = some (w, m')) : w.toNat < 2 ^ 32 := by
  have hI₂ := hI
  exact consInternM_lt fvarCS_wf hR hI₂

theorem lainternW_hw (m : Mem) (a : AState) (hR : LamR m a) (t b : Word) (w : Word) (m' : Mem)
    (hI : lainternW m t b = some (w, m')) : w.toNat < 2 ^ 32 := by
  exact consInternM_lt lamCS_wf hR hI

theorem leinternW_hw (m : Mem) (a : AState) (hR : LetR m a) (t v b : Word) (w : Word) (m' : Mem)
    (hI : leinternW m t v b = some (w, m')) : w.toNat < 2 ^ 32 := by
  exact consInternM_lt letCS_wf hR hI

theorem fainternW_hw' (m : Mem) (a : AState) (hR : ForallR m a) (t b : Word) (w : Word) (m' : Mem)
    (hI : fainternW m t b = some (w, m')) : w.toNat < 2 ^ 32 := by
  exact consInternM_lt forallCS_wf hR hI

theorem pjinternW_hw' (m : Mem) (a : AState) (hR : ProjR m a) (n u e : Word) (w : Word) (m' : Mem)
    (hI : pjinternW m n u e = some (w, m')) : w.toNat < 2 ^ 32 := by
  exact consInternM_lt projCS_wf hR hI

theorem mkLamW_hw (m : Mem) (a : AState) (hA : ArenaD m a) (t b r : Word) (m' : Mem)
    (hI : mkLamW m t b = some (r, m')) : r.toNat < 2 ^ 32 := by
  unfold mkLamW at hI
  split at hI
  · cases hI
  cases hI₁ : lainternW m t b with
  | none => simp [hI₁, mkK] at hI
  | some p =>
  obtain ⟨r₁, m₁⟩ := p
  simp only [hI₁, mkK_some] at hI
  split at hI
  · cases hI
  simp only [Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  exact lainternW_hw m a hA.1.lam t b _ m₁ hI₁

theorem mkLetW_hw (m : Mem) (a : AState) (hA : ArenaD m a) (t v b r : Word) (m' : Mem)
    (hI : mkLetW m t v b = some (r, m')) : r.toNat < 2 ^ 32 := by
  unfold mkLetW at hI
  split at hI
  · cases hI
  cases hI₁ : leinternW m t v b with
  | none => simp [hI₁, mkK] at hI
  | some p =>
  obtain ⟨r₁, m₁⟩ := p
  simp only [hI₁, mkK_some] at hI
  split at hI
  · cases hI
  simp only [Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  exact leinternW_hw m a hA.1.letE t v b _ m₁ hI₁

theorem mkForallW_hw' (m : Mem) (a : AState) (hA : ArenaD m a) (t b r : Word) (m' : Mem)
    (hI : mkForallW m t b = some (r, m')) : r.toNat < 2 ^ 32 := by
  unfold mkForallW at hI
  split at hI
  · cases hI
  cases hI₁ : fainternW m t b with
  | none => simp [hI₁, mkK] at hI
  | some p =>
  obtain ⟨r₁, m₁⟩ := p
  simp only [hI₁, mkK_some] at hI
  split at hI
  · cases hI
  simp only [Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  exact fainternW_hw' m a hA.1.forallE t b _ m₁ hI₁

theorem mkProjW_hw' (m : Mem) (a : AState) (hA : ArenaD m a) (n i e r : Word) (m' : Mem)
    (hI : mkProjW m n i e = some (r, m')) : r.toNat < 2 ^ 32 := by
  unfold mkProjW at hI
  split at hI
  · cases hI
  cases hI₁ : pjinternW m n i e with
  | none => simp [hI₁, mkK] at hI
  | some p =>
  obtain ⟨r₁, m₁⟩ := p
  simp only [hI₁, mkK_some] at hI
  split at hI
  · cases hI
  simp only [Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  exact pjinternW_hw' m a hA.1.proj n i e _ m₁ hI₁

theorem sinternW_hw (m : Mem) (a : AState) (hR : SuccR m a) (u : Word) (w : Word) (m' : Mem)
    (hI : sinternW m u = some (w, m')) : w.toNat < 2 ^ 32 := by
  have hI₂ := hI
  exact consInternM_lt succCS_wf hR hI₂

/-- `intern_succ` under the stage relation. -/
theorem internSuccN_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {r : Word} (hS : StageR dn vis fe m a) (u : Word) (hu : u.toNat < 2 ^ 32)
    (hI : sinternW m u = some (r, m')) :
    ∃ a', (internLNode (.succ (decI u))).run a = .ok (decI r, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  have hR := hS.1.arena.1
  obtain ⟨hok, hX, hres⟩ := sintern_correct m a hR.succ u hu _ _ hI
  have hfr := sinternW_frame m u _ _ hI
  exact stage_of_level hS (internLNode_succ_run _ a) hok
    (hR.lift_succ _ _ _ _ ⟨hX, sintern_hp m a hR.succ u hu hR.succHp (lvlHPW_ok m a hR u hu) _ _ hI⟩
      hfr (AM.st_proto succLens _ _ _ _ _ _ a (internLNode_succ_run _ a) hok))
    hres hfr (by simp [SREC, SSLOT, SHP]) (by simp [succSch]) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩)
    (hS.1.mode.frame hfr (by decide) (by decide))

/-- The lookups of master's interners, the environment and the pin readers that the gate's
proofs call (the real functions, not the stubs of `masterFns`). -/
structure MasterProg (p : Prog) : Prop where
  lPinAt : p.lookup "pin_at" = some pinAtL
  lPinWord : p.lookup "pin_word" = some pinWordL
  lEnvIx : p.lookup "env_ix" = some envIxL
  lEnvRowGet : p.lookup "env_row_get" = some envRowGetL
  lEnvFind : p.lookup "env_find" = some envFindL
  lConstFind : p.lookup "const_find" = some constFind
  lConstPush : p.lookup "const_push" = some constPush
  lInternConst : p.lookup "intern_const" = some internConst
  lDerB : p.lookup "der_b" = some derB
  lAppFind : p.lookup "app_find" = some appFind
  lAppPush : p.lookup "app_push" = some appPush
  lInternApp : p.lookup "intern_app" = some internApp
  lMkApp : p.lookup "mk_app" = some mkApp
  lFvarFind : p.lookup "fvar_find" = some fvarFind
  lFvarPush : p.lookup "fvar_push" = some fvarPush
  lInternFVar : p.lookup "intern_fvar" = some internFVar
  lLamFind : p.lookup "lam_find" = some lamFind
  lLamPush : p.lookup "lam_push" = some lamPush
  lInternLam : p.lookup "intern_lam" = some internLamL
  lMkLam : p.lookup "mk_lam" = some mkLam
  lForallFind : p.lookup "forall_find" = some forallFind
  lForallPush : p.lookup "forall_push" = some forallPush
  lInternForall : p.lookup "intern_forall" = some internForallL
  lMkForall : p.lookup "mk_forall" = some mkForall
  lLetFind : p.lookup "letE_find" = some letFind
  lLetPush : p.lookup "letE_push" = some letPush
  lInternLet : p.lookup "intern_letE" = some internLet
  lMkLet : p.lookup "mk_let" = some mkLet
  lProjFind : p.lookup "proj_find" = some projFind
  lProjPush : p.lookup "proj_push" = some projPush
  lInternProj : p.lookup "intern_proj" = some internProj
  lMkProj : p.lookup "mk_proj" = some mkProj
  lSuccFind : p.lookup "succ_find" = some succFind
  lSuccPush : p.lookup "succ_push" = some succPush
  lInternSucc : p.lookup "intern_succ" = some internSucc
  lZeroFind : p.lookup "zero_find" = some zeroFind
  lZeroPush : p.lookup "zero_push" = some zeroPush
  lInternZero : p.lookup "intern_zero" = some internZero
  lSortFind : p.lookup "sort_find" = some sortFind
  lSortPush : p.lookup "sort_push" = some sortPush
  lInternSort : p.lookup "intern_sort" = some internSort
  lConstE : p.lookup "const_e" = some constEL

section interners
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

theorem internConst_ref (hM : MasterProg p) (f x : Word) (hf : H f) (hx : H x) :
    CallRef p "intern_const" [f, x] (StageR dn vis fe)
      (internE (.const (decI f) (decI x))) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_triple fun n s₀ a₀ hS => ?_
  refine triple_post (internConst_spec p hM.lConstFind hM.lConstPush hM.lInternConst n s₀ f x) ?_
  rintro r s' ⟨hl, hI⟩
  obtain ⟨a', hrun, hS', hg⟩ := internConst_stage hS f x hf hx hI
  exact ⟨hl, decE (r.headD 0), a', hrun, hS', hg, ceinternW_hw' _ _ hS.1.arena.1.const f x hf hx _ _ hI, rfl⟩

theorem internFVar_ref (hM : MasterProg p) (u ty : Word) (hty : H ty) :
    CallRef p "intern_fvar" [u, ty] (StageR dn vis fe)
      (internE (.fvar u.toNat (decE ty))) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_triple fun n s₀ a₀ hS => ?_
  refine triple_post (internFVar_spec p hM.lFvarFind hM.lFvarPush hM.lInternFVar n s₀ u ty) ?_
  rintro r s' ⟨hl, hI⟩
  obtain ⟨a', hrun, hS', hg⟩ := internFVar_stage hS u ty hty hI
  exact ⟨hl, decE (r.headD 0), a', hrun, hS', hg, fvinternW_hw _ _ hS.1.arena.1.fvar u ty _ _ hI, rfl⟩

theorem mkApp_ref (hM : MasterProg p) (f x : Word) :
    CallRef p "mk_app" [f, x] (StageR dn vis fe)
      (internE (.app (decE f) (decE x))) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_triple fun n s₀ a₀ hS => ?_
  refine triple_post (mkApp_spec p hM.lDerB hM.lAppFind hM.lAppPush hM.lInternApp hM.lMkApp n s₀ f x) ?_
  rintro r s' ⟨hl, hI⟩
  obtain ⟨a', hrun, hS', hg⟩ := mkApp_stage hS f x hI
  exact ⟨hl, decE (r.headD 0), a', hrun, hS', hg, mkAppW_hw _ _ hS.1.arena f x _ _ hI, rfl⟩

theorem mkLam_ref (hM : MasterProg p) (t b : Word) :
    CallRef p "mk_lam" [t, b] (StageR dn vis fe)
      (internE (.lam (decE t) (decE b))) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_triple fun n s₀ a₀ hS => ?_
  refine triple_post (mkLam_spec p hM.lDerB hM.lLamFind hM.lLamPush hM.lInternLam hM.lMkLam n s₀ t b) ?_
  rintro r s' ⟨hl, hI⟩
  obtain ⟨a', hrun, hS', hg⟩ := mkLam_stage hS t b hI
  exact ⟨hl, decE (r.headD 0), a', hrun, hS', hg, mkLamW_hw _ _ hS.1.arena t b _ _ hI, rfl⟩

theorem mkForall_ref (hM : MasterProg p) (t b : Word) :
    CallRef p "mk_forall" [t, b] (StageR dn vis fe)
      (internE (.forallE (decE t) (decE b))) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_triple fun n s₀ a₀ hS => ?_
  refine triple_post (mkForall_spec p hM.lDerB hM.lForallFind hM.lForallPush hM.lInternForall hM.lMkForall n s₀ t b) ?_
  rintro r s' ⟨hl, hI⟩
  obtain ⟨a', hrun, hS', hg⟩ := mkForall_stage hS t b hI
  exact ⟨hl, decE (r.headD 0), a', hrun, hS', hg, mkForallW_hw' _ _ hS.1.arena t b _ _ hI, rfl⟩

theorem mkLet_ref (hM : MasterProg p) (t v b : Word) :
    CallRef p "mk_let" [t, v, b] (StageR dn vis fe)
      (internE (.letE (decE t) (decE v) (decE b))) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_triple fun n s₀ a₀ hS => ?_
  refine triple_post (mkLet_spec p hM.lDerB hM.lLetFind hM.lLetPush hM.lInternLet hM.lMkLet n s₀ t v b) ?_
  rintro r s' ⟨hl, hI⟩
  obtain ⟨a', hrun, hS', hg⟩ := mkLet_stage hS t v b hI
  exact ⟨hl, decE (r.headD 0), a', hrun, hS', hg, mkLetW_hw _ _ hS.1.arena t v b _ _ hI, rfl⟩

theorem mkProj_ref (hM : MasterProg p) (n i e : Word) :
    CallRef p "mk_proj" [n, i, e] (StageR dn vis fe)
      (internE (.proj (decI n) i.toNat (decE e))) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_triple fun k s₀ a₀ hS => ?_
  refine triple_post (mkProj_spec p hM.lDerB hM.lProjFind hM.lProjPush hM.lInternProj hM.lMkProj k s₀ n i e) ?_
  rintro r s' ⟨hl, hI⟩
  obtain ⟨a', hrun, hS', hg⟩ := mkProj_stage hS n i e hI
  exact ⟨hl, decE (r.headD 0), a', hrun, hS', hg, mkProjW_hw' _ _ hS.1.arena n i e _ _ hI, rfl⟩

theorem internSucc_ref (hM : MasterProg p) (u : Word) (hu : H u) :
    CallRef p "intern_succ" [u] (StageR dn vis fe)
      (internLNode (.succ (decI u))) (KeepPost dn vis fe decW0L) := by
  refine CallRef.of_triple fun n s₀ a₀ hS => ?_
  refine triple_post (internSucc_spec p hM.lSuccFind hM.lSuccPush hM.lInternSucc n s₀ u) ?_
  rintro r s' ⟨hl, hI⟩
  obtain ⟨a', hrun, hS', hg⟩ := internSuccN_stage hS u hu hI
  exact ⟨hl, decI (r.headD 0), a', hrun, hS', hg, sinternW_hw _ _ hS.1.arena.1.succ u _ _ hI, rfl⟩

end interners

/-! ## `const_e`, `e_view`, `sl_contains` -/

/-- The model of `const_e(n)`. -/
def constEW (p : Prog) (n : Nat) (m : Mem) (nm : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "pin_word" [52] m) fun r1 m1 =>
  ntBW (callW p n "intern_const" [nm, r1.headD 0] m1) fun r2 m2 => some ([r2.headD 0], m2)

theorem constE_specW (p : Prog) (hp : p.lookup "const_e" = some constEL) (n : Nat) (s₀ : St)
    (nm : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "const_e" [nm]
    ⦃fun r s' => LocEq s' s₀ ∧ constEW p n s₀.mem nm = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, constEL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_word", callW_spec p n "intern_const"] <;>
    finish [constEW, ntBW]

section prims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

theorem constE_ref (hM : MasterProg p) (nm : Word) :
    CallRef p "const_e" [nm] (fun m a => StageR dn vis fe m a ∧ H nm) (constE (decI nm))
      (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hnm⟩ hc => ?_
  have hw := callW_model (M := fun mm => constEW p k mm nm) (constE_specW p hM.lConstE k · nm) hc
  unfold constEW at hw
  cases h1 : callW p k "pin_word" [52] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1l, hx1⟩ := pinWord52_ref (dn := dn) (vis := vis) (fe := fe) p
    hM.lPinWord k m a r1 m1 hS h1
  cases h2 : callW p k "intern_const" [nm, r1.headD 0] m1 with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ := internConst_ref (dn := dn) (vis := vis) (fe := fe) hM nm
    (r1.headD 0) hnm hx1l k m1 a1 r2 m2 hS1 h2
  refine ⟨x2, a2, ?_, hS2, hg1.trans hg2, hx2l, hx2⟩
  simp only [constE, emptyLevels, StateT.run_bind, hrun1, exc_ok_bind', ← hx1, hrun2]

theorem eView_ref (h : Word) (hE : p.lookup "e_view" = some eView) :
    CallRef p "e_view" [h] (StageR dn vis fe) (view (decE h))
      (KeepPost dn vis fe (fun _ r v => ViewR r v)) := by
  refine CallRef.of_triple fun n s₀ a₀ hS => ?_
  refine triple_post (eView_refines p hE n s₀ a₀ hS.1.arena.1 h) ?_
  rintro r s' ⟨rfl, hok, hst, hv⟩
  have hrun := AM.run_of_ok _ _ hok
  rw [hst] at hrun
  exact ⟨rfl, _, a₀, hrun, hS, IWGrow.refl _, hv⟩

end prims

/-! ## `sl_contains` -/

theorem decHL_bnd {k : IdxKind} (m : Mem) (o l : Word) {xs : List (Idx k)}
    (h : decHL m o.toNat l.toNat = some xs) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    o.toNat + l.toNat < 2 ^ 64 := by
  by_cases hl : l.toNat = 0
  · have := o.toNat_lt; omega
  · have := hslice?_bound (iwA m) l.toNat o.toNat xs h (by omega)
    simp only [iwA] at this
    omega

theorem containsDecI {k : IdxKind} (ws : List Word) (x : Word) (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) :
    (ws.map (fun w => (decI w : Idx k))).contains (decI x) = ws.contains x := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.contains_cons]
    have hw : w.toNat < 2 ^ 32 := hws w (by simp)
    have hb : ((decI x : Idx k) == decI w) = (x == w) := by
      by_cases h : x = w
      · subst h; rw [beq_self_eq_true, beq_self_eq_true]
      · have : (decI x : Idx k) ≠ decI w := fun e => h (by
          rw [(decI_eq_iff x hx _).mp e]; exact decI_word_self w hw)
        rw [beq_false_of_ne this, beq_false_of_ne h]
    rw [hb, ih (fun y hy => hws y (by simp [hy]))]

section slc
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

theorem slContains_ref {k : IdxKind} (hp : p.lookup "sl_contains" = some slContains) (o l x : Word)
    (xs : List (Idx k)) (hx : H x) :
    CallRef p "sl_contains" [o, l, x]
      (fun m a => StageR dn vis fe m a ∧ decHL m o.toNat l.toNat = some xs)
      (pure (xs.contains (decI x)) : AM Bool) (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_triple fun n s₀ a₀ ⟨hS, hd⟩ => ?_
  refine triple_post (slContains_spec p hp n s₀ o l x) ?_
  rintro r s' ⟨hl, hm, hcw⟩
  obtain ⟨ws, hws, rfl, hlt⟩ := slR_of_decHL s₀.mem l.toNat o.toNat xs hd
    (decHL_bnd _ o l hd hS.2.2.2.1)
  rw [UInt64.ofNat_toNat, UInt64.ofNat_toNat] at hws
  have hr := containsW_ok n _ _ _ _ _ _ hws hcw
  rw [containsDecI ws x hlt hx]
  refine ⟨hl, _, a₀, rfl, hm ▸ hS, hm ▸ IWGrow.refl _, ?_⟩
  by_cases hc : ws.contains x = true
  · simp only [hc, if_true] at hr ⊢
    simp only [decW0B, hr]; decide
  · simp only [hc, if_false] at hr ⊢
    simp only [decW0B, hr]; decide

end slc

/-! ## `env_find` -/

theorem ntRowPW_eq (m : Mem) (w : Word) (hw : w.toNat < 2 ^ 32) (ht : tagW w ≤ 2) :
    rowPW m w = rowP m w := by
  have h1 := tagW_toNat w
  have h2 := ixW_toNat w hw
  have ht' : rowTag w ≤ 2 := by rw [← h1]; exact UInt64.le_iff_toNat_le.mp ht
  have hix : rowIx w < 2 ^ 30 := by
    simp only [rowIx]; have : w.toNat % 2 ^ 27 < 2 ^ 27 := Nat.mod_lt _ (by decide)
    have : w.toNat / 2 ^ 27 % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  have h3 : (ixW w + 1).toNat = rowIx w + 1 := by
    rw [UInt64.toNat_add, h2]; simp; omega
  simp only [rowPW, rowP, ht', if_true, rdW, h3]
  simp [selArr_rowSelW w ht']

/-- The result of `env_find`: the miss flag, or the hit flag and a record pointer that decodes. -/
def decFd (dn : NIdx → Option ConLeche.Name) (m : Mem) (r : List Word) :
    Option IConstantInfo → Prop
  | none => r.headD 0 = 0
  | some ci => r.headD 0 = 1 ∧ decCI (erecP m) dn (r.tail.headD 0).toNat = some ci

theorem EnvR.hit_some {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}
    (h : EnvR dn m vis fe) (w : Word) (hw : w.toNat < 2 ^ 32) (ht : rowTag w ≤ 2)
    (hc : rowC m w ≠ 0) : ∃ ci, decCI (erecP m) dn (rowP m w).toNat = some ci := by
  have hk := h.keys (decI w) (by rwa [decI_word_self w hw])
  have hv := h.vals (decI w) (by rwa [decI_word_self w hw]) (by rwa [decI_word_self w hw])
  rw [decI_word_self w hw] at hk hv
  simp only [rowW, hc, if_false, Option.map_some] at hk
  cases e : fe.idx[(decI w : NIdx)]? with
  | none => simp [e] at hk
  | some r =>
    obtain ⟨c, ci⟩ := r
    simp only [e, Option.map_some] at hv
    exact ⟨ci, hv.symm⟩

theorem envFind_call {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}
    (hM : MasterProg p) (w : Word) (hw : H w) {n : Nat} {m m' : Mem} {r : List Word}
    (hE : EnvR dn m vis fe) (h : callW p n "env_find" [w, vis] m = some (r, m')) :
    m' = m ∧ decFd dn m r (fe.find? (decI w)) := by
  obtain ⟨s', rfl, -, hmod⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_specW p hM.lEnvIx hM.lEnvRowGet hM.lEnvFind n _ w vis) h
  change envFindW m w vis = some (r, s'.mem) at hmod
  unfold envFindW at hmod
  by_cases ht : 2 < tagW w
  · simp [ht] at hmod
  rw [if_neg ht] at hmod
  have ht2 : tagW w ≤ 2 := by
    have : ¬ (2 : Word).toNat < (tagW w).toNat := fun e => ht (UInt64.lt_iff_toNat_lt.mpr e)
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have htag : rowTag w ≤ 2 := by rw [← tagW_toNat]; exact UInt64.le_iff_toNat_le.mp ht2
  rw [EnvR.find?_eq hE w hw htag, ← rowCW_eq m w hw ht2]
  by_cases hc : rowCW m w = 0
  · rw [if_pos hc] at hmod; simp only [Option.some.injEq, Prod.mk.injEq] at hmod
    obtain ⟨rfl, hm⟩ := hmod
    rw [← hm, if_pos hc]
    exact ⟨rfl, rfl⟩
  rw [if_neg hc] at hmod
  have hc' : (rowCW m w).toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by simpa using e))
  by_cases hv : rowCW m w - 1 < vis
  · rw [if_pos hv] at hmod; simp only [Option.some.injEq, Prod.mk.injEq] at hmod
    obtain ⟨rfl, hm⟩ := hmod
    have hv' : (rowCW m w).toNat - 1 < vis.toNat := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _
        (UInt64.le_iff_toNat_le.mpr (by simp; omega))] at hv
      simpa using hv
    have hcC : rowC m w ≠ 0 := by rw [← rowCW_eq m w hw ht2]; exact hc
    obtain ⟨ci, hci⟩ := EnvR.hit_some hE w hw htag hcC
    rw [← hm, if_neg hc, if_pos hv', ← ntRowPW_eq m w hw ht2]
    rw [← ntRowPW_eq m w hw ht2] at hci
    refine ⟨rfl, ?_⟩
    simp [decFd, hci]
  · rw [if_neg hv] at hmod; simp only [Option.some.injEq, Prod.mk.injEq] at hmod
    obtain ⟨rfl, hm⟩ := hmod
    have hv' : ¬ (rowCW m w).toNat - 1 < vis.toNat := by
      intro e; apply hv; rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _
        (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
      simpa using e
    rw [← hm, if_neg hc, if_neg hv']
    exact ⟨rfl, rfl⟩

/-! ## The named pin readers are `pin_at` at their slots -/

@[simp] theorem natPredName_eq : natPredName = pinAt 14 := rfl
@[simp] theorem natAddName_eq : natAddName = pinAt 15 := rfl
@[simp] theorem natSubName_eq : natSubName = pinAt 16 := rfl
@[simp] theorem natMulName_eq : natMulName = pinAt 17 := rfl
@[simp] theorem natPowName_eq : natPowName = pinAt 18 := rfl
@[simp] theorem natBeqName_eq : natBeqName = pinAt 19 := rfl
@[simp] theorem natBleName_eq : natBleName = pinAt 20 := rfl
@[simp] theorem natDivName_eq : natDivName = pinAt 21 := rfl
@[simp] theorem natModName_eq : natModName = pinAt 22 := rfl
@[simp] theorem natGcdName_eq : natGcdName = pinAt 23 := rfl
@[simp] theorem natLandName_eq : natLandName = pinAt 24 := rfl
@[simp] theorem natLorName_eq : natLorName = pinAt 25 := rfl
@[simp] theorem natXorName_eq : natXorName = pinAt 26 := rfl
@[simp] theorem natShiftLeftName_eq : natShiftLeftName = pinAt 27 := rfl
@[simp] theorem natShiftRightName_eq : natShiftRightName = pinAt 28 := rfl
@[simp] theorem boolName_eq : boolName = pinAt 29 := rfl
@[simp] theorem boolTrueName_eq : boolTrueName = pinAt 30 := rfl
@[simp] theorem boolFalseName_eq : boolFalseName = pinAt 31 := rfl
@[simp] theorem pinNat_eq : pinNat = pinAt 1 := rfl
@[simp] theorem pinNatZero_eq : pinNatZero = pinAt 2 := rfl
@[simp] theorem pinNatSucc_eq : pinNatSucc = pinAt 3 := rfl
@[simp] theorem pinEq_eq : pinEq = pinAt 0 := rfl

/-- A `CallRef` from a `RefAM`. -/
theorem CallRef.of_refAM {α : Type} [Inhabited α] {p : Prog} {f : FnName} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    (h : RefAM p f args pre op post) : CallRef p f args pre op post := by
  intro n m a r m' hpre hc
  obtain ⟨s', rfl, -, hq⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (h n _ a hpre) hc
  exact ⟨AM.res op a, AM.st op a, AM.run_of_ok op a hq.1, hq.2⟩

end L.Ind
