import ConAgua.Arena.WhnfDeltaRefine3
import ConAgua.Arena.PinsNatOp
import ConAgua.Arena.CoreAgree

/-!
# `nat_op_result` under `CoreS` (the first of `WhnfDelta`'s two assumed facts)

Lane `nat2`/`pinsenv` proved `natOpResultL_refines`: `nat_op_result` in the concrete program
`natArmProg` refines `natOpResult` under `ArenaR`. `NatOpResultOK p` (`WhnfDeltaRefine3.lean`)
wants it in any program `p` that agrees with `natArmProg'` on `natFns`, under `CoreS`:

* **The program**: `invoke_agreeOn` (`CoreAgree.lean`) twice, `p` → `natArmProg'` → `natArmProg`,
  with `natArmProg'_closed` and `natArmProg_closed` (both `decide +kernel` on the text) as the
  call-closure witnesses.
* **The memory**: `nat_op_result`'s write set (`natA`, `natC`: the pool, the `lit` and `const`
  tables and their counts) is below every other tier of `CoreS` and avoids the derived-range
  arrays, the walk memos and the stack.
* **The twin state**: `natOpResult` reads pins and interns at most one leaf (a `lit`, or a `const`
  for `Nat.beq`/`Nat.ble`): `LeafOp`. A leaf step keeps the caches, the pins and the level store
  (`cpl`), and carries `DerR` (at any memory) over: a new `lit`/`const` node has both ranges `0`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## Leaf steps of the twin -/

/-- **A leaf step**: the caches, pins and level store kept, `DerR` carried over at any memory. -/
def LeafStep (a a' : AState) : Prop := cpl a' = cpl a ∧ ∀ m, DerR m a → DerR m a'

theorem LeafStep.refl (a : AState) : LeafStep a a := ⟨rfl, fun _ h => h⟩

theorem LeafStep.trans {a₁ a₂ a₃ : AState} (h₁ : LeafStep a₁ a₂) (h₂ : LeafStep a₂ a₃) :
    LeafStep a₁ a₃ := ⟨h₂.1.trans h₁.1, fun m h => h₂.2 m (h₁.2 m h)⟩

/-- Every successful run of `op` is a leaf step. -/
@[irreducible] def LeafOp {α : Type} (op : AM α) : Prop :=
  ∀ a r a', op.run a = .ok (r, a') → LeafStep a a'

theorem LeafOp.pure {α : Type} (x : α) : LeafOp (Pure.pure x : AM α) := by
  unfold LeafOp; intro a r a' h; cases h; exact LeafStep.refl _

theorem LeafOp.bind {α γ : Type} {x : AM α} {f : α → AM γ} (hx : LeafOp x)
    (hf : ∀ v, LeafOp (f v)) : LeafOp (x >>= f) := by
  unfold LeafOp at *; intro a r a' h
  simp only [StateT.run_bind] at h
  cases h1 : x.run a with
  | error e => rw [h1] at h; cases h
  | ok q =>
    obtain ⟨v, a₁⟩ := q
    rw [h1] at h
    exact (hx a v a₁ h1).trans (hf v a₁ r a' h)

theorem LeafOp.ite {α : Type} {c : Prop} [Decidable c] {x y : AM α} (hx : LeafOp x)
    (hy : LeafOp y) : LeafOp (if c then x else y) := by
  by_cases h : c
  · simp only [h, ite_true]; exact hx
  · simp only [h, ite_false]; exact hy

theorem LeafOp.of_keeps {α : Type} {op : AM α} (h : Keeps id op) : LeafOp op := by
  unfold LeafOp; intro a r a' hr
  have : a' = a := Keeps.run h hr
  subst this; exact LeafStep.refl _

theorem leafOp_pinAt (i : Nat) : LeafOp (pinAt i) := by
  apply LeafOp.of_keeps
  unfold Keeps; intro a r a' h
  simp only [pinAt, StateT.run_bind, StateT.run_get, pure_bind] at h
  split at h
  · cases h; rfl
  · simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h

theorem leafOp_pinEmptyLevels : LeafOp pinEmptyLevels := by
  apply LeafOp.of_keeps
  unfold Keeps; intro a r a' h
  simp only [pinEmptyLevels, StateT.run_bind, StateT.run_get, pure_bind] at h
  split at h
  · cases h; rfl
  · simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h

/-- Interning a `lit` node is a leaf step. -/
theorem leafOp_internLit (l : ConLeche.Literal) : LeafOp (internE (.lit l)) := by
  unfold LeafOp; intro a r a' h
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ h
  have hk : cpl a' = cpl a := Keeps.run (keeps_cpl_internNodeE _) (by simpa [internE] using h)
  refine ⟨hk, fun m hD => ?_⟩
  have hcs := AM.proto_cases litLens _ _ _ _ _ _ a (internE_lit_run _ a) hok
  rw [← hst]
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD
  · exact ⟨hD.bvar, hD.fvar, hD.sort, hD.const,
      ⟨derT_push hD.lit.1 _ _ _ ⟨bvar_derLit _ _, fvar_derLit _ _, lp_derLit _ _⟩, hD.lit.2⟩, hD.app, hD.lam,
      hD.forallE, hD.letE, hD.proj⟩
  · exact ⟨hD.bvar, hD.fvar, hD.sort, hD.const,
      ⟨hD.lit.1, derT_push hD.lit.2 _ _ _ ⟨bvar_derLit _ _, fvar_derLit _ _, lp_derLit _ _⟩⟩, hD.app, hD.lam,
      hD.forallE, hD.letE, hD.proj⟩

/-- Interning a `const` node is a leaf step. -/
theorem leafOp_internConst (n : NIdx) (us : LsIdx) : LeafOp (internE (.const n us)) := by
  unfold LeafOp; intro a r a' h
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ h
  have hk : cpl a' = cpl a := Keeps.run (keeps_cpl_internNodeE _) (by simpa [internE] using h)
  refine ⟨hk, fun m hD => ?_⟩
  have hcs := AM.proto_cases constLens _ _ _ _ _ _ a (internE_const_run _ _ a) hok
  rw [← hst]
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD
  · exact ⟨hD.bvar, hD.fvar, hD.sort,
      ⟨derT_push hD.const.1 _ _ _ ⟨bvar_derConst _ _ _, fvar_derConst _ _ _⟩, hD.const.2⟩, hD.lit,
      hD.app, hD.lam, hD.forallE, hD.letE, hD.proj⟩
  · exact ⟨hD.bvar, hD.fvar, hD.sort,
      ⟨hD.const.1, derT_push hD.const.2 _ _ _ ⟨bvar_derConst _ _ _, fvar_derConst _ _ _⟩⟩, hD.lit,
      hD.app, hD.lam, hD.forallE, hD.letE, hD.proj⟩

/-- **`natOpResult` is a leaf step**: fifteen pin reads, then at most one leaf interned. -/
theorem leafOp_natOpResult (c : NIdx) (x y : Nat) : LeafOp (natOpResult c x y) := by
  have hl : ∀ v : Nat, LeafOp (do let r ← internE (.lit (.natVal v)); Pure.pure (some r) : AM (Option EIdx)) :=
    fun v => LeafOp.bind (leafOp_internLit _) (fun _ => LeafOp.pure _)
  have hc : ∀ n : NIdx, LeafOp (do let r ← constE n; Pure.pure (some r) : AM (Option EIdx)) :=
    fun n => LeafOp.bind (LeafOp.bind leafOp_pinEmptyLevels (fun _ => leafOp_internConst _ _))
      (fun _ => LeafOp.pure _)
  simp only [natOpResult, natPredName, natAddName, natSubName, natMulName, natPowName,
    natBeqName, natBleName, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatPred, pinNatAdd, pinNatSub,
    pinNatMul, pinNatPow, pinNatBeq, pinNatBle, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight]
  repeat' first
    | exact hl _
    | exact hc _
    | exact LeafOp.pure _
    | (apply LeafOp.bind (leafOp_pinAt _); intro _)
    | apply LeafOp.ite

/-! ## The program -/

/-- The functions of `natArmProg`. -/
def natArmFns : List FnName := natArmProg.map (·.1)

theorem natArmProg_closed : closedA natArmProg natA natC natArmFns = true := by decide +kernel

theorem lookup_append_of_mem {β : Type} (l₁ l₂ : List (String × β)) (f : String)
    (h : f ∈ l₁.map (·.1)) : (l₁ ++ l₂).lookup f = l₁.lookup f := by
  induction l₁ with
  | nil => simp at h
  | cons x xs ih =>
    obtain ⟨k, v⟩ := x
    by_cases hk : f = k
    · subst hk; simp [List.lookup]
    · have : f ∈ xs.map (·.1) := by simp at h ⊢; rcases h with h | h; exact absurd h hk; exact h
      have hb : (f == k) = false := by simpa using hk
      simp only [List.cons_append, List.lookup, hb]; exact ih this

theorem natArmProg'_agree : ∀ f ∈ natArmFns, natArmProg'.lookup f = natArmProg.lookup f :=
  fun f hf => lookup_append_of_mem natArmProg _ f hf

theorem natC_lt : ∀ x ∈ natC, x.toNat < 20 := by
  intro x hx; simp only [natC, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide

/-- **`nat_op_result` in a program agreeing with `natArmProg'`** runs as in `natArmProg`. -/
theorem invoke_natOpResult {p : Prog} (hp : ∀ f ∈ natFns, p.lookup f = natArmProg'.lookup f)
    (n : Nat) (vs : List Word) :
    invoke p (exec p n) "nat_op_result" vs = invoke natArmProg (exec natArmProg n) "nat_op_result" vs :=
  (invoke_agreeOn natArmProg'_closed hp n (by decide) vs).trans
    (invoke_agreeOn natArmProg_closed natArmProg'_agree n (by decide) vs)

/-! ## The arms keep the pool below its old top (`PoolGrew`)

Every arm's refinement is generic in the relation (`NatArms.lean`), so it holds at
`ArenaR m a ∧ PoolGrew m₀ m` (`ArenaP m₀`): the arithmetic only appends (`Grows`), and `intern_lit`
and `intern_const` do not write the pool at all (their write sets, from the text). -/

/-- `ArenaR` and "the pool only grew since `m₀`". -/
def ArenaP (m₀ : Mem) (m : Mem) (a : AState) : Prop := ArenaR m a ∧ PoolGrew m₀ m

theorem arenaP_pool (m₀ : Mem) : ∀ m a, ArenaP m₀ m a → PoolOK m := fun _ _ h => h.1.lit.1
theorem arenaP_grow (m₀ : Mem) : ∀ m m' a, ArenaP m₀ m a → Grows m m' → ArenaP m₀ m' a :=
  fun m m' a h hg => ⟨ArenaR.grow m m' hg a h.1, h.2.trans (PoolGrew.of_grows hg)⟩

/-- `intern_lit`'s functions in `natArmProg`: the `lit` table only. -/
def natLitFns : List FnName := ["intern_lit", "lit_hash", "limbs_eq", "lit_match", "lit_find", "lit_push"]
theorem natLitFns_closed : closedA natArmProg [REC, SLOT] [2, 3] natLitFns = true := by decide +kernel

/-- `nat_beq_lit`/`nat_ble_lit` and their callees: the `const` table only. -/
def natCmpFns : List FnName :=
  ["nat_beq_lit", "nat_ble_lit", "nat_cmp", "intern_const", "const_find", "const_push"]
theorem natCmpFns_closed : closedA natArmProg [CREC, CSLOT, CLP] [18, 19] natCmpFns = true := by
  decide +kernel

theorem internLit_armsP (m₀ : Mem) : InternSpec natArmProg (ArenaP m₀) := by
  intro a₀ n s₀ o l ⟨hA, hP⟩ hq hn
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hD, hres⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (internLit_arms a₀ n s₀ o l hA hq hn)
  obtain ⟨hfr, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (invoke_memFrame natLitFns_closed n (f := "intern_lit") (by decide) [o, l] s₀)
  subst hs
  exact ⟨hloc, hok, ⟨hD, hP.trans (PoolGrew.of_frame hfr (by decide) (by decide))⟩, hres⟩

theorem cmpArmP {g : FnName} {arm : Nat → Nat → AM (Option EIdx)} (hg : g ∈ natCmpFns)
    (h : CmpArmR ArenaR g arm) (m₀ : Mem) : CmpArmR (ArenaP m₀) g arm := by
  intro n s₀ a₀ ⟨hA, hP⟩ oa la ob lb t f us ha hb hna hnb ht hf hu hT hF hE
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hD, hres⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (h n s₀ a₀ hA oa la ob lb t f us ha hb hna hnb ht hf hu hT hF hE)
  obtain ⟨hfr, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (invoke_memFrame natCmpFns_closed n hg [oa, la, ob, lb, t, f, us] s₀)
  subst hs
  exact ⟨hloc, hok, ⟨hD, hP.trans (PoolGrew.of_frame hfr (by decide) (by decide))⟩, hres⟩

/-- **The sixteen arms under `ArenaP m₀`.** -/
theorem natArmsR_pool (m₀ : Mem) : NatArmsR (ArenaP m₀) where
  pred := fun n s₀ a₀ hR oa la ha =>
    natPredLit_refines natArmProg (ArenaP m₀) (arenaP_pool m₀) (arenaP_grow m₀) (internLit_armsP m₀)
      rfl rfl rfl rfl rfl n s₀ a₀ hR oa la ha
  pow := fun n s₀ a₀ hR oa la ob lb ha hnb =>
    natPowLit_refines natArmProg (ArenaP m₀) (arenaP_pool m₀) (arenaP_grow m₀) (internLit_armsP m₀)
      rfl rfl rfl rfl rfl n s₀ a₀ hR oa la ob lb ha hnb
  add := fun n s₀ a₀ hR oa la ob lb ha hb _ _ =>
    natAddLit_refines natArmProg rfl rfl rfl rfl rfl (ArenaP m₀) (arenaP_pool m₀) (arenaP_grow m₀)
      (internLit_armsP m₀) n s₀ a₀ hR oa la ob lb ha hb
  sub := fun n s₀ a₀ hR oa la ob lb ha hb hna hnb =>
    topLit_refines natArmProg (ArenaP m₀) (arenaP_pool m₀) (arenaP_grow m₀) (internLit_armsP m₀)
      "nat_sub_lit" "nat_sub" _ rfl natSub_top n s₀ a₀ hR oa la ob lb ha hb hna hnb
  mul := fun n s₀ a₀ hR oa la ob lb ha hb hna hnb =>
    topLit_refines natArmProg (ArenaP m₀) (arenaP_pool m₀) (arenaP_grow m₀) (internLit_armsP m₀)
      "nat_mul_lit" "nat_mul" _ rfl natMul_top n s₀ a₀ hR oa la ob lb ha hb hna hnb
  div := fun n s₀ a₀ hR oa la ob lb ha hb _ hnb =>
    natDivLit_refines natArmProg (ArenaP m₀) (arenaP_pool m₀) (arenaP_grow m₀) (internLit_armsP m₀)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl n s₀ a₀ hR oa la ob lb ha hb hnb
  mod := fun n s₀ a₀ hR oa la ob lb ha hb _ hnb =>
    natModLit_refines natArmProg (ArenaP m₀) (arenaP_pool m₀) (arenaP_grow m₀) (internLit_armsP m₀)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl n s₀ a₀ hR oa la ob lb ha hb hnb
  gcd := fun n s₀ a₀ hR oa la ob lb ha hb hna hnb =>
    natGcdLit_refines natArmProg (ArenaP m₀) (arenaP_pool m₀) (arenaP_grow m₀) (internLit_armsP m₀)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl n s₀ a₀ hR oa la ob lb ha hb hna hnb
  land := fun n s₀ a₀ hR oa la ob lb ha hb hna hnb =>
    topLit_refines natArmProg (ArenaP m₀) (arenaP_pool m₀) (arenaP_grow m₀) (internLit_armsP m₀)
      "nat_land_lit" "nat_land" _ rfl natLand_top n s₀ a₀ hR oa la ob lb ha hb hna hnb
  lor := fun n s₀ a₀ hR oa la ob lb ha hb hna hnb =>
    topLit_refines natArmProg (ArenaP m₀) (arenaP_pool m₀) (arenaP_grow m₀) (internLit_armsP m₀)
      "nat_lor_lit" "nat_lor" _ rfl natLor_top n s₀ a₀ hR oa la ob lb ha hb hna hnb
  xor := fun n s₀ a₀ hR oa la ob lb ha hb hna hnb =>
    topLit_refines natArmProg (ArenaP m₀) (arenaP_pool m₀) (arenaP_grow m₀) (internLit_armsP m₀)
      "nat_xor_lit" "nat_xor" _ rfl natXor_top n s₀ a₀ hR oa la ob lb ha hb hna hnb
  shl := fun n s₀ a₀ hR oa la ob lb ha hb hna hnb =>
    topLit_refines natArmProg (ArenaP m₀) (arenaP_pool m₀) (arenaP_grow m₀) (internLit_armsP m₀)
      "nat_shl_lit" "nat_shl" _ rfl natShl_top n s₀ a₀ hR oa la ob lb ha hb hna hnb
  shr := fun n s₀ a₀ hR oa la ob lb ha hb hna hnb =>
    topLit_refines natArmProg (ArenaP m₀) (arenaP_pool m₀) (arenaP_grow m₀) (internLit_armsP m₀)
      "nat_shr_lit" "nat_shr" _ rfl natShr_top n s₀ a₀ hR oa la ob lb ha hb hna hnb
  beq := cmpArmP (by decide) natBeqLit_refinesA m₀
  ble := cmpArmP (by decide) natBleLit_refinesA m₀

/-! ## The relation -/

/-- **`CoreS` across `nat_op_result`**: the arena relation from the refinement, the derived ranges
and every upper tier by the frame and the leaf step. -/
theorem CoreS.of_natOp {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (hR : ArenaR m' a')
    (hL : LeafStep a a') (hf : MemFrame natA natC m m') (hP : PoolGrew m m') :
    CoreS dn m' a' vis fe M eb ∧ StackKept m m' := by
  obtain ⟨hcpl, hder⟩ := hL
  simp only [cpl, Prod.mk.injEq] at hcpl
  obtain ⟨hc, hp, hl⟩ := hcpl
  have hD : DerR m' a := DerR.frameM natA natC m m' hf (by decide) a hS.arena.2
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by decide) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by decide)
  refine ⟨⟨⟨hR, hder m' hD⟩, ?_, ?_, hS.env.frame (by decide) (.of_lt natC_lt (by decide)) hf, ?_, ?_, ?_,
    hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn, hS.memos.frame hf (by decide) (by decide),
    hf.2.2.1 145 ▸ hS.bstk⟩, by simp only [spTop, h136], by rw [hspn],
    fun i _ => by simp only [spW, hspn], BKept.of_frame hf (by decide) (by decide), hP⟩
  · rw [hc]; exact hS.core.frame (by decide) (.of_lt natC_lt (by decide)) hf
  · rw [hp]; exact hS.pins.congr (hf.1 PINS (by decide) (by decide))
  · intro h l e; rw [hc] at e; have := hS.readL h l e; simp only [EStore.ls] at this ⊢; rw [hl]; exact this
  · intro h l e; rw [hc] at e; have := hS.readLs h l e; rw [hl]; exact this
  · rw [hl]; exact hS.nwf

/-- **`nat_op_result` refines `natOpResult` under `CoreS`** in every program that agrees with
`natArmProg'` on `natFns` (the first assumed fact of `WhnfDeltaRefine4.lean`). -/
theorem natOpResultOK_of_agree {p : Prog} (hp : ∀ f ∈ natFns, p.lookup f = natArmProg'.lookup f) :
    NatOpResultOK p := by
  intro n s₀ a₀ dn vis fe MM eb c oa la ob lb hS hc ha hb hna hnb
  unfold CoreSpec
  simp only [invoke_natOpResult hp]
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, ⟨hR, hPG⟩, hres⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (natOpResultL_refinesR (ArenaP s₀.mem) (natArmsR_pool s₀.mem) n s₀ a₀ ⟨hS.arena.1, PoolGrew.refl _⟩
      ⟨fun _ => hS.pins⟩ c oa la ob lb hc ha hb hna hnb)
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (invoke_memFrame natArmProg_closed n (by decide) _ s₀)
  subst hs
  have hrun' := AM.run_of_ok _ _ hok
  have hL : LeafStep a₀ (AM.st (natOpResult (decI c) (pv (s.mem.arr64 POOL) oa.toNat la.toNat)
      (pv (s.mem.arr64 POOL) ob.toNat lb.toNat)) a₀) := by
    have h := leafOp_natOpResult (decI c) (pv (s.mem.arr64 POOL) oa.toNat la.toNat)
      (pv (s.mem.arr64 POOL) ob.toNat lb.toNat)
    unfold LeafOp at h; exact h _ _ _ hrun'
  obtain ⟨hS', hSt⟩ := hS.of_natOp hR hL hf hPG
  exact ⟨hloc, hok, ⟨MM, hS', KeptAll.refl _ _, hSt⟩, hres, trivial⟩

end L.Arena
