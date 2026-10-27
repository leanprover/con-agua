import ConAgua.Arena.IndStubs
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.IndCopy2

/-!
# A word model simulates a twin run (lane `indproofs2`, helper `rec`)

The relational half of the phase-8 template (`IndSumSpec/StructElimLevel.lean`) as a few combinators, so that a
relational lemma is a chain of `RSim.bind` steps instead of a hand-written case split ending in a
step-by-step rewrite of the twin's run.

`RSim o op a Q`: whenever the word model `o` returns `b`, the twin's `op` run from `a` succeeds
with some `x`, `a'`, and `Q b a' x`. A model is a chain of continuations `K (callee …)` with
`K none = none`; `RSim.bind` composes a callee's `RSim` with its continuation's, `RSim.lstep` takes an
L-only step (a pure model the twin computes inline), `RSim.pure` ends the chain.

`fuelW n o`: `none` at fuel `0`, `o` above. A callee whose spec holds at fuel `n + 1` only gets a
spec at every fuel through it (`invoke_exec_zero`: a call at fuel `0` never returns).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Result words -/

theorem getD_zero (r : List Word) : r.getD 0 0 = r.headD 0 := by cases r <;> rfl
theorem getD_one (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  cases r with | nil => rfl | cons a t => cases t <;> rfl
theorem getD_two (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  rw [show r.getD 2 0 = r.tail.getD 1 0 by cases r <;> rfl, getD_one]
theorem getD_three (r : List Word) : r.getD 3 0 = r.tail.tail.tail.headD 0 := by
  rw [show r.getD 3 0 = r.tail.getD 2 0 by cases r <;> rfl, getD_two]
theorem getD_four (r : List Word) : r.getD 4 0 = r.tail.tail.tail.tail.headD 0 := by
  rw [show r.getD 4 0 = r.tail.getD 3 0 by cases r <;> rfl, getD_three]

/-! ## Arguments read directly (grind's offset matching of `Locals.init_cons_succ` stops early) -/

theorem loc_init4 (x0 x1 x2 x3 x4 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: r) 4 = x4 := rfl
theorem loc_init5 (x0 x1 x2 x3 x4 x5 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: r) 5 = x5 := rfl
theorem loc_init6 (x0 x1 x2 x3 x4 x5 x6 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: r) 6 = x6 := rfl
theorem loc_init7 (x0 x1 x2 x3 x4 x5 x6 x7 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: r) 7 = x7 := rfl
theorem loc_init8 (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: r) 8 = x8 := rfl
theorem loc_init9 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: r) 9 = x9 := rfl
theorem loc_init10 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: r) 10 = x10 := rfl
theorem loc_init11 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: r) 11 = x11 := rfl

/-- The cursor and the count of a non-empty slice, one step on. -/
theorem slice_step {o l : Word} (hl : l ≠ 0) (hb : o.toNat + l.toNat < 2 ^ 64) :
    (o + 1).toNat = o.toNat + 1 ∧ (l - 1).toNat = l.toNat - 1 ∧ l.toNat ≠ 0 := by
  have hl0 : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  refine ⟨?_, ?_, hl0⟩
  · rw [UInt64.toNat_add]; simp; omega
  · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp

/-! ## Fuel `0` -/

/-- A call at fuel `0` never returns. -/
theorem invoke_exec_zero (p : Prog) (f : FnName) (args : List Word) (P : St → Prop) :
    ⦃P⦄ invoke p (exec p 0) f args ⦃fun _ _ => False; ⊤⦄ := by
  refine M.triple_of_run fun s r s' _ h => ?_
  have he : (invoke p (exec p 0) f args).run s = .error (match p.lookup f with
      | some _ => .outOfFuel | none => .noFun f) := by
    cases hl : p.lookup f with
    | none => simp only [invoke, lookupFn, hl]; rfl
    | some fd => simp only [invoke, lookupFn, hl]; rfl
  rw [he] at h; cases h

/-- `none` at fuel `0`. -/
def fuelW {β : Type} : Nat → Option β → Option β
  | 0, _ => none
  | _ + 1, o => o

@[simp] theorem fuelW_zero {β : Type} (o : Option β) : fuelW 0 o = none := rfl
@[simp] theorem fuelW_succ {β : Type} (n : Nat) (o : Option β) : fuelW (n + 1) o = o := rfl

/-! ## The simulation -/

/-- **The word model's result `o` simulates the twin's `op` from `a`**, with post `Q`. -/
def RSim {β α : Type} (o : Option β) (op : AM α) (a : AState) (Q : β → AState → α → Prop) : Prop :=
  ∀ b, o = some b → ∃ x a', op.run a = .ok (x, a') ∧ Q b a' x

namespace RSim
variable {β γ α δ : Type}

theorem none {op : AM α} {a : AState} {Q : β → AState → α → Prop} : RSim none op a Q := by
  intro b h; cases h

/-- End of the chain: a pure twin result. -/
theorem pure {o : Option β} {x : α} {a : AState} {Q : β → AState → α → Prop}
    (h : ∀ b, o = some b → Q b a x) : RSim o (Pure.pure x : AM α) a Q :=
  fun b hb => ⟨x, a, rfl, h b hb⟩

/-- End of the chain at a model result `some b`. -/
theorem pure_some {b : β} {x : α} {a : AState} {Q : β → AState → α → Prop}
    (h : Q b a x) : RSim (some b) (Pure.pure x : AM α) a Q :=
  RSim.pure fun _ hb => by cases hb; exact h

/-- **A callee step**: the callee's simulation, then its continuation's. -/
theorem bind {K : Option β → Option γ} (hK : K Option.none = Option.none) {o : Option β}
    {op : AM α} {f : α → AM δ} {a : AState} {Q1 : β → AState → α → Prop}
    {Q : γ → AState → δ → Prop} (h1 : RSim o op a Q1)
    (h2 : ∀ b x a1, o = some b → Q1 b a1 x → RSim (K (some b)) (f x) a1 Q) :
    RSim (K o) (op >>= f) a Q := by
  intro c hc
  cases ho : o with
  | none => rw [ho, hK] at hc; cases hc
  | some b =>
    rw [ho] at hc
    obtain ⟨x, a1, hr1, hq1⟩ := h1 b ho
    obtain ⟨y, a2, hr2, hq2⟩ := h2 b x a1 ho hq1 c hc
    refine ⟨y, a2, ?_, hq2⟩
    show (op >>= f) a = _
    have hr1' : op a = .ok (x, a1) := hr1
    show (do let (x, s) ← op a; f x s) = _
    rw [hr1']
    exact hr2

/-- **A callee step at the twin's tail**: the twin ends with the callee, the model post-processes
its result. -/
theorem bindPure {K : Option β → Option γ} (hK : K Option.none = Option.none) {o : Option β}
    {op : AM α} {a : AState} {Q1 : β → AState → α → Prop} {Q : γ → AState → α → Prop}
    (h1 : RSim o op a Q1) (h2 : ∀ b x a1, o = some b → Q1 b a1 x → RSim (K (some b)) (Pure.pure x : AM α) a1 Q) :
    RSim (K o) op a Q := by
  have h := RSim.bind (f := fun x => (Pure.pure x : AM α)) hK h1 h2
  rwa [bind_pure] at h

/-- **A twin-only step**: a twin computation the model does not run (a read of the state). -/
theorem tstep {o : Option β} {op : AM α} {f : α → AM δ} {a a' : AState} {x : α}
    {Q : β → AState → δ → Prop} (hr : op.run a = .ok (x, a')) (h : RSim o (f x) a' Q) :
    RSim o (op >>= f) a Q := by
  intro b hb
  obtain ⟨y, a2, hr2, hq⟩ := h b hb
  refine ⟨y, a2, ?_, hq⟩
  have hr1' : op a = .ok (x, a') := hr
  show (do let (x, s) ← op a; f x s) = _
  rw [hr1']
  exact hr2

/-- **An L-only step**: the model computes something (a pure word model) the twin does not run. -/
theorem lstep {K : Option β → Option γ} (hK : K Option.none = Option.none) {o : Option β}
    {op : AM δ} {a : AState} {Q : γ → AState → δ → Prop}
    (h : ∀ b, o = some b → RSim (K (some b)) op a Q) : RSim (K o) op a Q := by
  cases ho : o with
  | none => rw [hK]; exact RSim.none
  | some b => exact h b ho

/-- Rewrite the model. -/
theorem of_eq {o o' : Option β} {op : AM α} {a : AState} {Q : β → AState → α → Prop}
    (he : o = o') (h : RSim o' op a Q) : RSim o op a Q := he ▸ h

/-- Weaken the post. -/
theorem mono {o : Option β} {op : AM α} {a : AState} {Q Q' : β → AState → α → Prop}
    (h : RSim o op a Q) (hq : ∀ b a' x, o = some b → Q b a' x → Q' b a' x) : RSim o op a Q' := by
  intro b hb
  obtain ⟨x, a', hr, hq'⟩ := h b hb
  exact ⟨x, a', hr, hq b a' x hb hq'⟩

/-- A twin that throws is never simulated, unless the model fails. -/
theorem of_none {o : Option β} {op : AM α} {a : AState} {Q : β → AState → α → Prop}
    (h : o = Option.none) : RSim o op a Q := by rw [h]; exact RSim.none

/-- The usual way to conclude: a `RSim` of a successful model run gives the twin run. -/
theorem run {o : Option β} {op : AM α} {a : AState} {Q : β → AState → α → Prop} {b : β}
    (h : RSim o op a Q) (hb : o = some b) : ∃ x a', op.run a = .ok (x, a') ∧ Q b a' x := h b hb

/-- The census theorem's post from a `RSim` of the model a triple gives. -/
theorem am {o : Option β} {op : AM α} [Inhabited α] {a : AState} {Q : β → AState → α → Prop}
    {b : β} (h : RSim o op a Q) (hb : o = some b) : AM.ok op a ∧ Q b (AM.st op a) (AM.res op a) := by
  obtain ⟨x, a', hr, hq⟩ := h b hb
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok op a a' x hr
  exact ⟨hok, by rw [hst, hres]; exact hq⟩

end RSim

/-- A stub's `RelAM` as a `RSim`. -/
theorem RelAM.sim {α : Type} {f : FnName} {args : List Word} {pre : Mem → AState → Prop} {op : AM α}
    {post : Mem → Mem → AState → List Word → α → Prop} (h : RelAM f args pre op post)
    {m : Mem} {a : AState} (hp : pre m a) :
    RSim (stubM f m args) op a (fun b a' x => post m b.2 a' b.1 x) := by
  intro b hb
  obtain ⟨r, m'⟩ := b
  exact h m m' a r hb hp

/-! ## The usual post -/

/-- The usual post as a `RSim` post on `(r, m')`: the stage relation, growth from `m`, the result
decoded by `dec`. -/
def KP {α : Type} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem)
    (dec : Mem → List Word → α → Prop) (b : List Word × Mem) (a' : AState) (x : α) : Prop :=
  StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ dec b.2 b.1 x

/-! ## Words read at a decoded record -/

theorem ofNat_add_toNat (w : Word) (k : Nat) (h : w.toNat + k < 2 ^ 64) :
    (w + UInt64.ofNat k).toNat = w.toNat + k := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega : k < 2 ^ 64)]
  exact Nat.mod_eq_of_lt h

/-- A number at `IW[w + k]`, read at the word address. -/
theorem iwN_rdW_at {m : Mem} {w : Word} {k v : Nat} (h : iwN m (w.toNat + k) = some v)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    rdW (m.arr64 IW) (w + UInt64.ofNat k) = UInt64.ofNat v ∧ v < 2 ^ 64 := by
  have hlt : w.toNat + k < (m.arr64 IW).size := by
    simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, -⟩ := h
    exact (Array.getElem?_eq_some_iff.mp hx).1
  have := iwN_rdW h (by omega)
  have he : UInt64.ofNat (w.toNat + k) = w + UInt64.ofNat k := by
    apply UInt64.toNat_inj.mp
    rw [ofNat_add_toNat w k (by omega)]; simp; omega
  rw [he] at this; exact this

/-- A handle at `IW[w + k]`, read at the word address. -/
theorem iwH_rdW_at {m : Mem} {kk : IdxKind} {w : Word} {k : Nat} {x : Idx kk}
    (h : iwH m (w.toNat + k) = some x) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    ∃ v, rdW (m.arr64 IW) (w + UInt64.ofNat k) = v ∧ v.toNat < 2 ^ 32 ∧ decI v = x := by
  have hlt : w.toNat + k < (m.arr64 IW).size := by
    simp only [iwH, hd?, iwA] at h
    cases hw : (m.arr64 IW)[w.toNat + k]? with
    | none => simp [hw] at h
    | some _ => exact (Array.getElem?_eq_some_iff.mp hw).1
  have := iwH_rdW h (by omega)
  have he : UInt64.ofNat (w.toNat + k) = w + UInt64.ofNat k := by
    apply UInt64.toNat_inj.mp
    rw [ofNat_add_toNat w k (by omega)]; simp; omega
  rw [he] at this; exact this

/-! ## Records without a size precondition -/

/-- The model of `recN(ws)`: an allocation of `|ws|` words, then the words. -/
def recW (m : Mem) (k : Word) (ws : List Word) : Option (List Word × Mem) :=
  match allocW m k with
  | none => none
  | some (q, m1) => some ([q], wrIW m1 q ws)

section recs
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (n : Nat)
include ha

theorem rec2_specW (hp : p.lookup "rec2" = some rec2) (s₀ : St) (a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec2" [a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ recW s₀.mem 2 [a, b] = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, rec2]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [recW, wrIW]

theorem rec3_specW (hp : p.lookup "rec3" = some rec3) (s₀ : St) (a b c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec3" [a, b, c]
    ⦃fun r s' => LocEq s' s₀ ∧ recW s₀.mem 3 [a, b, c] = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, rec3]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [recW, wrIW, UInt64.add_assoc]

theorem rec4_specW (hp : p.lookup "rec4" = some rec4) (s₀ : St) (a b c d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec4" [a, b, c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ recW s₀.mem 4 [a, b, c, d] = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, rec4]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [recW, wrIW, UInt64.add_assoc]

theorem rec5_specW (hp : p.lookup "rec5" = some rec5) (s₀ : St) (a b c d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec5" [a, b, c, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ recW s₀.mem 5 [a, b, c, d, e] = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, rec5]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [recW, wrIW, UInt64.add_assoc]

end recs

/-- **What a record leaves**: the pointer is the old top, the words are there, the pool only
grew, only `IW` and `CTL[200]` changed, the new top is `q + |ws|`. -/
theorem recW_post {m m' : Mem} {k : Word} {ws r : List Word} (h : recW m k ws = some (r, m'))
    (hc : 200 < (m.arr64 CTL).size) (hsz : (m.arr64 IW).size < 2 ^ 64) (hk : k.toNat = ws.length) :
    r = [rdW (m.arr64 CTL) 200] ∧
    (∀ j < ws.length, (m'.arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? = ws[j]?) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ iwTop m' = iwTop m + ws.length ∧
    iwTop m + ws.length ≤ (m.arr64 IW).size := by
  simp only [recW] at h
  cases hal : allocW m k with
  | none => rw [hal] at h; cases h
  | some qm =>
    obtain ⟨q, m1⟩ := qm
    rw [hal] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hq, rfl, hroom⟩ := allocW_facts hal hsz
    subst hq
    rw [hk] at hroom
    obtain ⟨hget, hg, hf, htop⟩ := recMem_post m ws k hk hc hroom hsz
    refine ⟨rfl, hget, hg, hf, ?_, by simpa [iwTop] using hroom⟩
    simp only [iwTop, htop]; rw [UInt64.toNat_add, hk]; omega

end L.Ind
