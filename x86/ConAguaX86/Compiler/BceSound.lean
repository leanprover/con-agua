module

public import ConAguaX86.Compiler.SimExpr

@[expose] public section

/-!
# Bounds-check elimination: what the facts mean

`Facts.Holds fa σ`: every fact of `fa` (`Bce.lean`) is true in the L state `σ`. This file proves
that the analysis's steps within one state are sound (an access that evaluated passed its check,
a condition's value, a bound of an expression), that the facts survive a change of the locals
they do not mention when the arrays keep their sizes (`Holds.frame`), and what the code generator
needs at an access (`safeIdx_sound`). `BcePost.lean` carries the facts through the statements.
-/

namespace L.Compiler

open L

/-- The arrays of `σ'` have the sizes of those of `σ`. -/
def SameSizes (σ σ' : St) : Prop :=
  (∀ a, (σ'.mem.arr8 a).size = (σ.mem.arr8 a).size) ∧ ∀ s, (σ'.mem.arr64 s).size = (σ.mem.arr64 s).size

theorem SameSizes.refl (σ : St) : SameSizes σ σ := ⟨fun _ => rfl, fun _ => rfl⟩

theorem SameSizes.trans {σ σ' σ'' : St} (h : SameSizes σ σ') (h' : SameSizes σ' σ'') : SameSizes σ σ'' :=
  ⟨fun a => (h'.1 a).trans (h.1 a), fun s => (h'.2 s).trans (h.2 s)⟩

theorem SameSizes.of_mem {σ σ' : St} (h : σ'.mem = σ.mem) : SameSizes σ σ' := by
  unfold SameSizes; rw [h]; exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- The length of key `k`'s array, in its elements, in `σ`. -/
def AKey.len (σ : St) : AKey → Nat
  | .b a => (σ.mem.arr8 a).size
  | .w s => (σ.mem.arr64 s).size
  | .t a tv =>
    match evalP σ tv with
    | .ok v => (σ.mem.arr64 (tierA a v)).size
    | .error _ => 0
  | .h s => 2 * (σ.mem.arr64 s).size
  | .u a tv =>
    match evalP σ tv with
    | .ok v => 2 * (σ.mem.arr64 (tierA a v)).size
    | .error _ => 0

/-- The facts `fa` hold in `σ`. -/
structure Facts.Holds (fa : Facts) (σ : St) : Prop where
  lt : ∀ f ∈ fa.lt, Expr.pure f.2 = true ∧ AKey.pure f.1 = true ∧
    ∀ v, evalP σ f.2 = .ok v → v.toNat < f.1.len σ
  hi : ∀ f ∈ fa.hi, (σ.loc f.1).toNat < f.2

/-- The facts at a point hold in `σ` (`none`: the point is not reached). -/
def FHolds : Option Facts → St → Prop
  | none, _ => False
  | some fa, σ => fa.Holds σ

@[simp] theorem fholds_some {fa : Facts} {σ : St} : FHolds (some fa) σ ↔ fa.Holds σ := Iff.rfl
@[simp] theorem fholds_none {σ : St} : FHolds none σ ↔ False := Iff.rfl

theorem holds_empty (σ : St) : Facts.Holds {} σ := ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩

/-! ## Equality tests -/

theorem Expr.beqP_eq : ∀ {a b : Expr}, Expr.beqP a b = true → a = b
  | .const x, .const y, h => by
    simp only [Expr.beqP, beq_iff_eq] at h; rw [UInt64.toNat_inj.mp h]
  | .var x, .var y, h => by simp only [Expr.beqP, beq_iff_eq] at h; rw [h]
  | .bin o a b, .bin o' a' b', h => by
    simp only [Expr.beqP, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, Expr.beqP_eq h.1.2, Expr.beqP_eq h.2]
  | .const _, .var _, h | .const _, .bin .., h | .var _, .const _, h | .var _, .bin .., h
  | .bin .., .const _, h | .bin .., .var _, h => by simp [Expr.beqP] at h
  | .ld8 .., _, h | .ld64 .., _, h | .len8 _, _, h | .len64 _, _, h | .cmpw .., _, h | .ldc .., _, h
  | .glob _, _, h | .ld64t .., _, h | .len64t .., _, h | .ld8x8 .., _, h | .ld32t .., _, h
  | .ld32h .., _, h => by simp [Expr.beqP] at h
  | .const _, .ld8 .., h | .const _, .ld64 .., h | .const _, .len8 _, h | .const _, .len64 _, h
  | .const _, .cmpw .., h | .const _, .ldc .., h | .const _, .glob _, h | .const _, .ld64t .., h
  | .const _, .len64t .., h | .const _, .ld8x8 .., h | .const _, .ld32t .., h | .const _, .ld32h .., h
  | .var _, .ld8 .., h | .var _, .ld64 .., h | .var _, .len8 _, h | .var _, .len64 _, h
  | .var _, .cmpw .., h | .var _, .ldc .., h | .var _, .glob _, h | .var _, .ld64t .., h
  | .var _, .len64t .., h | .var _, .ld8x8 .., h | .var _, .ld32t .., h | .var _, .ld32h .., h
  | .bin .., .ld8 .., h | .bin .., .ld64 .., h | .bin .., .len8 _, h | .bin .., .len64 _, h
  | .bin .., .cmpw .., h | .bin .., .ldc .., h | .bin .., .glob _, h | .bin .., .ld64t .., h
  | .bin .., .len64t .., h | .bin .., .ld8x8 .., h | .bin .., .ld32t .., h | .bin .., .ld32h .., h => by
    simp [Expr.beqP] at h

theorem tieredArray_eq {s s' : TieredArray} (h1 : s.arr = s'.arr) (h2 : s.hi = s'.hi) : s = s' := by
  cases s; cases s'; simp_all

theorem AKey.beq_eq {k k' : AKey} (h : AKey.beq k k' = true) : k = k' := by
  cases k <;> cases k' <;> simp only [AKey.beq, Bool.and_eq_true, beq_iff_eq, reduceCtorEq] at h <;>
    first
    | (rw [h])
    | (rw [tieredArray_eq h.1 h.2])
    | (rw [h.1, Expr.beqP_eq h.2])

/-! ## Pure expressions -/

theorem pure_ok {σ : St} : ∀ {e : Expr}, Expr.pure e = true → ∃ v, evalP σ e = .ok v
  | .const w, _ => ⟨w, rfl⟩
  | .var x, _ => ⟨σ.loc x, rfl⟩
  | .bin op a b, h => by
    simp only [Expr.pure, Bool.and_eq_true] at h
    obtain ⟨va, ha⟩ := pure_ok (σ := σ) h.1
    obtain ⟨vb, hb⟩ := pure_ok (σ := σ) h.2
    exact ⟨op.eval va vb, by simp [evalP, ha, hb]; rfl⟩
  | .ld8 .., h | .ld64 .., h | .len8 _, h | .len64 _, h | .cmpw .., h | .ldc .., h | .glob _, h
  | .ld64t .., h | .len64t .., h | .ld8x8 .., h | .ld32t .., h | .ld32h .., h => by simp [Expr.pure] at h

/-- A pure expression reads only the locals it mentions. -/
theorem pure_frame {σ σ' : St} : ∀ {e : Expr}, Expr.pure e = true →
    (∀ y, Expr.readsV y e = true → σ'.loc y = σ.loc y) → evalP σ' e = evalP σ e
  | .const _, _, _ => rfl
  | .var x, _, h => by simp only [evalP]; rw [h x (by simp [Expr.readsV])]
  | .bin op a b, hp, h => by
    simp only [Expr.pure, Bool.and_eq_true] at hp
    simp only [evalP]
    rw [pure_frame hp.1 (fun y hy => h y (by simp [Expr.readsV, hy])),
      pure_frame hp.2 (fun y hy => h y (by simp [Expr.readsV, hy]))]
  | .ld8 .., h, _ | .ld64 .., h, _ | .len8 _, h, _ | .len64 _, h, _ | .cmpw .., h, _ | .ldc .., h, _
  | .glob _, h, _ | .ld64t .., h, _ | .len64t .., h, _ | .ld8x8 .., h, _ | .ld32t .., h, _
  | .ld32h .., h, _ => by simp [Expr.pure] at h

theorem AKey.len_frame {σ σ' : St} {k : AKey} (hp : AKey.pure k = true)
    (h : ∀ y, AKey.readsV y k = true → σ'.loc y = σ.loc y) (hs : SameSizes σ σ') :
    k.len σ' = k.len σ := by
  cases k with
  | b a => exact hs.1 a
  | w s => exact hs.2 s
  | h s => simp only [AKey.len, hs.2 s]
  | t a tv =>
    simp only [AKey.len]
    rw [pure_frame hp h]
    cases evalP σ tv <;> simp [hs.2]
  | u a tv =>
    simp only [AKey.len]
    rw [pure_frame hp h]
    cases evalP σ tv <;> simp [hs.2]

/-! ## The facts across a change of state -/

/-- The facts hold in `σ'` if they do in `σ`, the locals they mention are unchanged and the arrays
keep their sizes. -/
theorem Facts.Holds.frame {fa : Facts} {σ σ' : St} (h : fa.Holds σ)
    (hlt : ∀ f ∈ fa.lt, ∀ y, (AKey.readsV y f.1 || Expr.readsV y f.2) = true → σ'.loc y = σ.loc y)
    (hhi : ∀ f ∈ fa.hi, σ'.loc f.1 = σ.loc f.1) (hs : SameSizes σ σ') : fa.Holds σ' := by
  refine ⟨fun f hf => ?_, fun f hf => by rw [hhi f hf]; exact h.hi f hf⟩
  obtain ⟨hpe, hpk, hv⟩ := h.lt f hf
  refine ⟨hpe, hpk, fun v he => ?_⟩
  rw [AKey.len_frame hpk (fun y hy => hlt f hf y (by simp [hy])) hs]
  rw [pure_frame hpe (fun y hy => hlt f hf y (by simp [hy]))] at he
  exact hv v he

theorem Facts.Holds.addLt {fa : Facts} {σ : St} (h : fa.Holds σ) {k : AKey} {e : Expr}
    (hk : Expr.pure e = true → AKey.pure k = true → ∀ v, evalP σ e = .ok v → v.toNat < k.len σ) :
    (fa.addLt k e).Holds σ := by
  unfold Facts.addLt
  split
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    refine ⟨fun f hf => ?_, h.hi⟩
    have hf' := List.mem_of_mem_take hf
    rcases List.mem_cons.mp hf' with rfl | hm
    · exact ⟨hc.1.1, hc.1.2, hk hc.1.1 hc.1.2⟩
    · exact h.lt f hm
  · exact h

/-- Accesses that passed their check. -/
def LoadsOk (σ : St) (l : List (AKey × Expr)) : Prop :=
  ∀ f ∈ l, ∀ v, evalP σ f.2 = .ok v → v.toNat < f.1.len σ

theorem LoadsOk.append {σ : St} {l l' : List (AKey × Expr)} (h : LoadsOk σ l) (h' : LoadsOk σ l') :
    LoadsOk σ (l ++ l') := fun f hf => by
  rcases List.mem_append.mp hf with hf | hf
  · exact h f hf
  · exact h' f hf

theorem LoadsOk.nil (σ : St) : LoadsOk σ [] := fun _ h => by simp at h

theorem Facts.Holds.addLoads {σ : St} : ∀ {fa : Facts} {l : List (AKey × Expr)}, fa.Holds σ → LoadsOk σ l →
    (fa.addLoads l).Holds σ
  | _, [], h, _ => h
  | _, (k, e) :: l, h, hl => by
    simp only [Facts.addLoads]
    exact Facts.Holds.addLoads (h.addLt fun _ _ v hv => hl (k, e) List.mem_cons_self v hv)
      fun f hf => hl f (List.mem_cons_of_mem _ hf)

/-! ## Accesses -/

theorem keyT_len {σ : St} {a : ArrId} {t : Expr} {k : AKey} {u : Word} (hk : keyT a t = some k)
    (ht : evalP σ t = .ok u) : k.len σ = (σ.mem.arr64 (tierA a u)).size := by
  unfold keyT at hk
  split at hk
  · cases hk; simp only [evalP] at ht; cases ht; rfl
  · split at hk
    · cases hk; simp only [AKey.len, ht]
    · cases hk

theorem keyT_pure {a : ArrId} {t : Expr} {k : AKey} (hk : keyT a t = some k) : AKey.pure k = true := by
  unfold keyT at hk
  split at hk
  · cases hk; rfl
  · split at hk
    · cases hk; simpa [AKey.pure]
    · cases hk

theorem key32_len {σ : St} {a : ArrId} {t : Expr} {k : AKey} {u : Word} (hk : key32 a t = some k)
    (ht : evalP σ t = .ok u) : k.len σ = 2 * (σ.mem.arr64 (tierA a u)).size := by
  unfold key32 at hk
  split at hk
  · cases hk; simp only [evalP] at ht; cases ht; rfl
  · split at hk
    · cases hk; simp only [AKey.len, ht]
    · cases hk

theorem bind_ok {α β : Type} {x : Except Err α} {f : α → Except Err β} {v : β}
    (h : (x >>= f) = .ok v) : ∃ a, x = .ok a ∧ f a = .ok v := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem loadsOk_cons {σ : St} {k : AKey} {i : Expr} {l : List (AKey × Expr)} {j : Word} {n : Nat}
    (hi : evalP σ i = .ok j) (hj : j.toNat < n) (hk : k.len σ = n) (hl : LoadsOk σ l) :
    LoadsOk σ ((k, i) :: l) := fun f hf v hv => by
  rcases List.mem_cons.mp hf with rfl | hm
  · rw [hi] at hv; cases hv; rw [hk]; exact hj
  · exact hl f hm v hv

theorem loadsOk_opt {σ : St} {ok : Option AKey} {i : Expr} {j : Word} {n : Nat}
    (hi : evalP σ i = .ok j) (hj : j.toNat < n) (hk : ∀ k, ok = some k → k.len σ = n) :
    LoadsOk σ (optLoad ok i) := by
  cases ok with
  | none => exact LoadsOk.nil σ
  | some k => exact loadsOk_cons hi hj (hk k rfl) (LoadsOk.nil σ)

/-- Every access of an expression that evaluated passed its check. -/
theorem loads_sound {σ : St} : ∀ {e : Expr} {v : Word}, evalP σ e = .ok v → LoadsOk σ (Expr.loads e)
  | .const _, _, _ | .var _, _, _ | .len8 _, _, _ | .len64 _, _, _ | .glob _, _, _ => LoadsOk.nil σ
  | .bin op a b, v, h | .cmpw op a b, v, h => by
    obtain ⟨va, ha, h⟩ := bind_ok h
    obtain ⟨vb, hb, -⟩ := bind_ok h
    exact (loads_sound ha).append (loads_sound hb)
  | .ld8 a i, v, h => by
    obtain ⟨j, hj, h⟩ := bind_ok h
    split at h
    · exact loadsOk_cons hj (by assumption) rfl (loads_sound hj)
    · cases h
  | .ld64 a i, v, h => by
    obtain ⟨j, hj, h⟩ := bind_ok h
    split at h
    · exact loadsOk_cons hj (by assumption) rfl (loads_sound hj)
    · cases h
  | .ldc _ i, v, h => by
    obtain ⟨j, hj, -⟩ := bind_ok h
    show LoadsOk σ (Expr.loads i); exact loads_sound hj
  | .ld8x8 _ i, v, h => by
    obtain ⟨j, hj, -⟩ := bind_ok h
    show LoadsOk σ (Expr.loads i); exact loads_sound hj
  | .len64t _ t, v, h => by
    obtain ⟨u, hu, -⟩ := bind_ok h
    show LoadsOk σ (Expr.loads t); exact loads_sound hu
  | .ld64t a t i, v, h => by
    obtain ⟨u, hu, h⟩ := bind_ok h
    obtain ⟨j, hj, h⟩ := bind_ok h
    simp only [Expr.loads]
    split at h
    · exact ((loadsOk_opt hj (by assumption) fun k hk => keyT_len hk hu).append (loads_sound hu)).append
        (loads_sound hj)
    · cases h
  | .ld32h a t i _, v, h => by
    obtain ⟨u, hu, h⟩ := bind_ok h
    obtain ⟨j, hj, h⟩ := bind_ok h
    simp only [Expr.loads]
    split at h
    · exact ((loadsOk_opt hj (by assumption) fun k hk => keyT_len hk hu).append (loads_sound hu)).append
        (loads_sound hj)
    · cases h
  | .ld32t a t i, v, h => by
    obtain ⟨u, hu, h⟩ := bind_ok h
    obtain ⟨j, hj, h⟩ := bind_ok h
    simp only [Expr.loads]
    split at h
    · rename_i hjs
      have hd : (j / 2).toNat = j.toNat / 2 := by simp [UInt64.toNat_div]
      have hj2 : j.toNat < 2 * (σ.mem.arr64 (tierA a u)).size := by omega
      exact ((loadsOk_opt hj hj2 fun k hk => key32_len hk hu).append (loads_sound hu)).append
        (loads_sound hj)
    · cases h

theorem evalCP_bind {σ : St} {c : Cond} {b : Bool} {f : Bool → Except Err Bool}
    (h : (evalCP σ c >>= f) = .ok b) : ∃ a, evalCP σ c = .ok a ∧ f a = .ok b := bind_ok h

theorem loadsAny_sound {σ : St} : ∀ {c : Cond} {b : Bool}, evalCP σ c = .ok b → LoadsOk σ (Cond.loadsAny c)
  | .cmp _ a b, _, h => by
    obtain ⟨va, ha, h⟩ := bind_ok h
    obtain ⟨vb, hb, -⟩ := bind_ok h
    exact (loads_sound ha).append (loads_sound hb)
  | .and p _, _, h | .or p _, _, h | .not p, _, h => by
    obtain ⟨a, ha, -⟩ := evalCP_bind h
    show LoadsOk σ (Cond.loadsAny p); exact loadsAny_sound ha

theorem condLoads_sound {σ : St} : ∀ {c : Cond} {pol : Bool}, evalCP σ c = .ok pol →
    LoadsOk σ (Cond.loads c pol)
  | .cmp _ a b, _, h => by
    obtain ⟨va, ha, h⟩ := bind_ok h
    obtain ⟨vb, hb, -⟩ := bind_ok h
    exact (loads_sound ha).append (loads_sound hb)
  | .and p q, true, h => by
    obtain ⟨a, ha, h⟩ := evalCP_bind h
    cases a
    · cases h
    · exact (condLoads_sound ha).append (condLoads_sound h)
  | .and p _, false, h => by
    obtain ⟨a, ha, -⟩ := evalCP_bind h
    show LoadsOk σ (Cond.loadsAny p); exact loadsAny_sound ha
  | .or p _, true, h => by
    obtain ⟨a, ha, -⟩ := evalCP_bind h
    show LoadsOk σ (Cond.loadsAny p); exact loadsAny_sound ha
  | .or p q, false, h => by
    obtain ⟨a, ha, h⟩ := evalCP_bind h
    cases a
    · exact (condLoads_sound ha).append (condLoads_sound h)
    · cases h
  | .not p, pol, h => by
    obtain ⟨a, ha, h⟩ := evalCP_bind h
    simp only [Cond.loads]
    have : a = !pol := by cases a <;> cases pol <;> simp_all [pure, Except.pure]
    subst this
    exact condLoads_sound ha

theorem lenKey_sound {σ : St} {b : Expr} {k : AKey} {y : Word} (hk : lenKey b = some k)
    (hb : evalP σ b = .ok y) : y.toNat ≤ k.len σ := by
  cases b <;> simp only [lenKey, reduceCtorEq] at hk
  · cases hk; simp only [evalP] at hb; cases hb
    simp only [Mem.len8, AKey.len]; exact Nat.mod_le _ _
  · cases hk; simp only [evalP] at hb; cases hb
    simp only [Mem.len64, AKey.len]; exact Nat.mod_le _ _
  · rename_i a t
    obtain ⟨u, hu, hb⟩ := bind_ok hb
    cases hb
    rw [keyT_len hk hu]
    simp only [Mem.len64]; exact Nat.mod_le _ _

theorem Facts.Holds.cmpF {fa : Facts} {σ : St} (h : fa.Holds σ) {op : Cmp} {a b : Expr} {pol : Bool}
    (hc : evalCP σ (.cmp op a b) = .ok pol) : (fa.cmpF op a b pol).Holds σ := by
  obtain ⟨va, ha, hc⟩ := bind_ok hc
  obtain ⟨vb, hb, hc⟩ := bind_ok hc
  have hpol : op.eval va vb = pol := by cases hc; rfl
  unfold Facts.cmpF
  split
  · split
    · rename_i k hk
      refine h.addLt fun _ _ v hv => ?_
      rw [ha] at hv; cases hv
      have := lenKey_sound hk hb
      simp only [Cmp.eval, decide_eq_true_eq, UInt64.lt_iff_toNat_lt] at hpol
      omega
    · exact h
  · split
    · rename_i k hk
      refine h.addLt fun _ _ v hv => ?_
      rw [hb] at hv; cases hv
      have := lenKey_sound hk ha
      simp only [Cmp.eval, decide_eq_false_iff_not, UInt64.le_iff_toNat_le] at hpol
      omega
    · exact h
  · exact h

theorem Facts.Holds.cond {σ : St} : ∀ {c : Cond} {fa : Facts} {pol : Bool}, fa.Holds σ →
    evalCP σ c = .ok pol → (fa.cond c pol).Holds σ
  | .cmp op a b, _, _, h, hc => h.cmpF hc
  | .and p q, fa, pol, h, hc => by
    simp only [Facts.cond]
    cases pol
    · exact h
    · obtain ⟨a, ha, hc⟩ := evalCP_bind hc
      cases a
      · cases hc
      · exact (h.cond ha).cond hc
  | .or p q, fa, pol, h, hc => by
    simp only [Facts.cond]
    cases pol
    · obtain ⟨a, ha, hc⟩ := evalCP_bind hc
      cases a
      · exact (h.cond ha).cond hc
      · cases hc
    · exact h
  | .not p, fa, pol, h, hc => by
    simp only [Facts.cond]
    obtain ⟨a, ha, hc⟩ := evalCP_bind hc
    have : a = !pol := by cases a <;> cases pol <;> simp_all [pure, Except.pure]
    subst this
    exact h.cond ha

theorem Facts.Holds.condAll {fa : Facts} {σ : St} (h : fa.Holds σ) {c : Cond} {pol : Bool}
    (hc : evalCP σ c = .ok pol) : (fa.condAll c pol).Holds σ :=
  (h.addLoads (condLoads_sound hc)).cond hc

/-! ## Bounds of values -/

theorem hiLookup_mem : ∀ {l : List (Var × Nat)} {x : Var} {n : Nat}, l.lookup x = some n → (x, n) ∈ l
  | [], _, _, h => by simp at h
  | (y, m) :: l, x, n, h => by
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hxy; cases h; simp only [beq_iff_eq] at hxy; subst hxy; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hiLookup_mem h)

theorem hiE_sound {σ : St} {hi : List (Var × Nat)} (hh : ∀ f ∈ hi, (σ.loc f.1).toNat < f.2) :
    ∀ {e : Expr} {n : Nat} {v : Word}, hiE hi e = some n → evalP σ e = .ok v → v.toNat < n
  | .const k, n, v, h, he => by
    simp only [hiE, Option.some.injEq] at h; cases he; omega
  | .var x, n, v, h, he => by
    simp only [hiE] at h; cases he; exact hh _ (hiLookup_mem h)
  | .bin op a b, n, v, h, he => by
    obtain ⟨va, ha, he⟩ := bind_ok he
    obtain ⟨vb, hb, he⟩ := bind_ok he
    cases he
    have hva := va.toNat_lt
    have hvb := vb.toNat_lt
    cases op
    case add =>
      simp only [hiE] at h
      split at h
      · rename_i x y hx hy
        split at h
        · cases h
          have h1 := hiE_sound hh hx ha
          have h2 := hiE_sound hh hy hb
          simp only [BinOp.eval, UInt64.toNat_add]
          omega
        · cases h
      · cases h
    case and =>
      simp only [hiE] at h
      simp only [BinOp.eval, UInt64.toNat_and]
      split at h
      · rename_i x hx
        have h1 := hiE_sound hh hx ha
        have := Nat.and_le_left (n := va.toNat) (m := vb.toNat)
        split at h
        · rename_i y hy
          cases h
          have h2 := hiE_sound hh hy hb
          have := Nat.and_le_right (n := va.toNat) (m := vb.toNat)
          omega
        · cases h; omega
      · have h2 := hiE_sound hh h hb
        have := Nat.and_le_right (n := va.toNat) (m := vb.toNat)
        omega
    case shr =>
      cases b with
      | const sh =>
        simp only [hiE, Option.some.injEq] at h
        subst h
        cases hb
        simp only [BinOp.eval, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
        have hb' : va.toNat ≤ (hiE hi a).getD (2 ^ 64) - 1 := by
          cases hx : hiE hi a with
          | none => simp; omega
          | some x => have := hiE_sound hh hx ha; simp; omega
        have := Nat.div_le_div_right (c := 2 ^ (vb.toNat % 64)) hb'
        omega
      | _ => simp [hiE] at h
    all_goals simp [hiE] at h

/-! ## Assignments and kills -/

theorem Facts.mem_kill_lt {fa : Facts} {x : Var} {f : AKey × Expr} (h : f ∈ (fa.kill x).lt) :
    f ∈ fa.lt ∧ AKey.readsV x f.1 = false ∧ Expr.readsV x f.2 = false := by
  simp only [Facts.kill, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem Facts.mem_kill_hi {fa : Facts} {x : Var} {f : Var × Nat} (h : f ∈ (fa.kill x).hi) :
    f ∈ fa.hi ∧ f.1 ≠ x := by
  simp only [Facts.kill, List.mem_filter, bne_iff_ne, ne_eq] at h
  exact h

/-- `killAll` is one filter. -/
theorem Facts.killAll_eq : ∀ (fa : Facts) (xs : List Var), fa.killAll xs =
    { lt := fa.lt.filter fun f => xs.all fun x => !AKey.readsV x f.1 && !Expr.readsV x f.2
      hi := fa.hi.filter fun f => xs.all fun x => f.1 != x }
  | fa, [] => by
    cases fa; simp only [Facts.killAll, List.all_nil, Facts.mk.injEq]
    exact ⟨(List.filter_eq_self.mpr fun _ _ => rfl).symm, (List.filter_eq_self.mpr fun _ _ => rfl).symm⟩
  | fa, x :: xs => by
    simp only [Facts.killAll, Facts.killAll_eq _ xs, Facts.kill, List.filter_filter, List.all_cons]
    congr 1 <;> (congr 1; funext f; rw [Bool.and_comm])

theorem Facts.killAll_idem (fa : Facts) (xs : List Var) : (fa.killAll xs).killAll xs = fa.killAll xs := by
  simp only [Facts.killAll_eq, List.filter_filter, Bool.and_self]

theorem headF_idem (fa : Option Facts) (s : Stmt) : headF (headF fa s) s = headF fa s := by
  cases fa <;> simp [headF, Facts.killAll_idem]

/-- The facts that do not mention the locals `xs` hold in `σ'` if they did in `σ`, `σ'` has the
locals of `σ` outside `xs`, and the arrays keep their sizes. -/
theorem Facts.Holds.killAll {fa : Facts} {σ σ' : St} (h : fa.Holds σ) (xs : List Var)
    (hl : ∀ y, y ∉ xs → σ'.loc y = σ.loc y) (hs : SameSizes σ σ') : (fa.killAll xs).Holds σ' := by
  rw [Facts.killAll_eq]
  have h' : (fa.killAll xs).Holds σ := by
    rw [Facts.killAll_eq]
    exact ⟨fun f hf => h.lt f (List.mem_filter.mp hf).1, fun f hf => h.hi f (List.mem_filter.mp hf).1⟩
  rw [Facts.killAll_eq] at h'
  refine h'.frame (fun f hf y hy => hl y fun hm => ?_) (fun f hf => hl _ fun hm => ?_) hs
  · have := (List.mem_filter.mp hf).2
    simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at this
    have := this y hm
    simp_all
  · have := (List.mem_filter.mp hf).2
    simp only [List.all_eq_true, bne_iff_ne, ne_eq] at this
    exact this _ hm rfl

theorem Facts.Holds.kill {fa : Facts} {σ σ' : St} (h : fa.Holds σ) (x : Var)
    (hl : ∀ y, y ≠ x → σ'.loc y = σ.loc y) (hs : SameSizes σ σ') : (fa.kill x).Holds σ' := by
  have := h.killAll [x] (fun y hy => hl y (by simpa using hy)) hs
  simpa [Facts.killAll] using this

theorem Facts.Holds.set {fa : Facts} {σ : St} (h : fa.Holds σ) {x : Var} {e : Expr} {v : Word}
    (he : evalP σ e = .ok v) : (fa.set x e).Holds (σ.setLoc x v) := by
  have h1 := (h.addLoads (loads_sound he)).kill x (σ' := σ.setLoc x v)
    (fun y hy => by simp [St.setLoc, hy]) (SameSizes.of_mem rfl)
  unfold Facts.set
  split
  · rename_i n hn
    refine ⟨h1.lt, fun f hf => ?_⟩
    rcases List.mem_cons.mp hf with rfl | hm
    · simp only [St.setLoc, ite_true]; exact hiE_sound h.hi hn he
    · exact h1.hi f hm
  · exact h1

/-! ## Joins -/

theorem fholds_join {a b : Option Facts} {σ : St} (h : FHolds a σ ∨ FHolds b σ) : FHolds (joinF a b) σ := by
  cases a with
  | none => simpa [joinF] using h
  | some f =>
    cases b with
    | none => simpa [joinF] using h
    | some g =>
      simp only [joinF, fholds_some]
      rcases h with h | h
      · refine ⟨fun x hx => h.lt x (List.mem_filter.mp hx).1, fun x hx => ?_⟩
        obtain ⟨⟨y, n⟩, hy, hxy⟩ := List.mem_filterMap.mp hx
        obtain ⟨m, -, rfl⟩ := Option.map_eq_some_iff.mp hxy
        have := h.hi _ hy
        simp only at this ⊢; omega
      · refine ⟨fun x hx => ?_, fun x hx => ?_⟩
        · obtain ⟨y, hy, hxy⟩ := List.any_eq_true.mp (List.mem_filter.mp hx).2
          simp only [Bool.and_eq_true] at hxy
          have : x = y := Prod.ext (AKey.beq_eq hxy.1) (Expr.beqP_eq hxy.2)
          subst this; exact h.lt x hy
        · obtain ⟨⟨y, n⟩, hy, hxy⟩ := List.mem_filterMap.mp hx
          obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hxy
          have := h.hi _ (hiLookup_mem hm)
          simp only at this ⊢; omega

/-! ## At an access -/

/-- An expression reads only the memory and the locals in it. -/
theorem evalP_congr {σ σ' : St} (hm : σ'.mem = σ.mem) :
    ∀ {e : Expr}, (∀ y, Expr.readsV y e = true → σ'.loc y = σ.loc y) → evalP σ' e = evalP σ e
  | .const _, _ => rfl
  | .var x, h => by simp only [evalP]; rw [h x (by simp [Expr.readsV])]
  | .glob _, _ | .len8 _, _ | .len64 _, _ => by simp only [evalP, hm]
  | .bin _ a b, h | .cmpw _ a b, h => by
    simp only [evalP]
    rw [evalP_congr hm (e := a) (fun y hy => h y (by simp [Expr.readsV, hy])),
      evalP_congr hm (e := b) (fun y hy => h y (by simp [Expr.readsV, hy]))]
  | .ld8 _ i, h | .ld64 _ i, h | .ldc _ i, h | .ld8x8 _ i, h => by
    simp only [evalP, hm]
    rw [evalP_congr hm (e := i) (fun y hy => h y (by simp [Expr.readsV, hy]))]
  | .len64t _ t, h => by
    simp only [evalP, hm]
    rw [evalP_congr hm (e := t) (fun y hy => h y (by simp [Expr.readsV, hy]))]
  | .ld64t _ t i, h | .ld32t _ t i, h | .ld32h _ t i _, h => by
    simp only [evalP, hm]
    rw [evalP_congr hm (e := t) (fun y hy => h y (by simp [Expr.readsV, hy])),
      evalP_congr hm (e := i) (fun y hy => h y (by simp [Expr.readsV, hy]))]

/-- **The facts at an expression**: they hold in a state `σ0` with `σ`'s memory that agrees with
`σ` on the locals `e` reads. (`σ` may be a ghost state of the expression code's proof, whose
locals in clobbered registers changed, `Inv.ghost`; `σ0` is the statement's state.) -/
def FactsFor (ctx : Ctx) (σ : St) (e : Expr) : Prop :=
  ∃ σ0 : St, FHolds ctx.fa σ0 ∧ σ0.mem = σ.mem ∧ ∀ y, Expr.readsV y e = true → σ0.loc y = σ.loc y

theorem FactsFor.of {ctx : Ctx} {σ : St} (h : FHolds ctx.fa σ) (e : Expr) : FactsFor ctx σ e :=
  ⟨σ, h, rfl, fun _ _ => rfl⟩

theorem FactsFor.sub {ctx : Ctx} {σ : St} {e : Expr} (h : FactsFor ctx σ e) {e' : Expr}
    (hs : ∀ y, Expr.readsV y e' = true → Expr.readsV y e = true) : FactsFor ctx σ e' :=
  let ⟨σ0, h1, h2, h3⟩ := h
  ⟨σ0, h1, h2, fun y hy => h3 y (hs y hy)⟩

/-- The facts at `e` for a context with the same facts. -/
theorem FactsFor.ctx {ctx ctx' : Ctx} {σ : St} {e : Expr} (h : FactsFor ctx σ e) (hf : ctx'.fa = ctx.fa) :
    FactsFor ctx' σ e := by
  unfold FactsFor; rw [hf]; exact h

/-- **What an unchecked access uses**: where `safeIdx` holds and the facts do, the index is below
the length `L` of the accessed array, given that `L` is at least the minimum length `mn` and the
key's length. -/
theorem safeIdx_sound {fa : Option Facts} {k : Option AKey} {i : Expr} {mn : Nat} {σ : St}
    (h : safeIdx fa k i mn = true) (hf : FHolds fa σ) {L : Nat} (hmn : mn ≤ L)
    (hk : ∀ key, k = some key → key.len σ ≤ L) {j : Word} (hj : evalP σ i = .ok j) : j.toNat < L := by
  cases fa with
  | none => exact absurd hf id
  | some fa =>
    simp only [safeIdx, Bool.or_eq_true] at h
    rcases h with h | h
    · split at h
      · rename_i n hn
        have := hiE_sound hf.hi hn hj
        simp only [decide_eq_true_eq] at h
        omega
      · cases h
    · split at h
      · rename_i key
        obtain ⟨f, hf', hm⟩ := List.any_eq_true.mp h
        simp only [Bool.and_eq_true] at hm
        have h1 := AKey.beq_eq hm.1
        have h2 := Expr.beqP_eq hm.2
        have := (hf.lt f hf').2.2 j (by rw [h2]; exact hj)
        rw [h1] at this
        exact Nat.lt_of_lt_of_le this (hk key rfl)
      · cases h

/-- **The check of an access dropped by the code generator** (`Ctx.ck` false) is not needed: the
index `i` (a part of `e`) is below the array's length `L`, which is at least the minimum `mn` and
the key's length in the states that agree with `σ` on `e`. -/
theorem ck_sound {ctx : Ctx} {σ : St} {e i : Expr} (hfa : FactsFor ctx σ e)
    (hsub : ∀ y, Expr.readsV y i = true → Expr.readsV y e = true)
    {k : Option AKey} {mn L : Nat} (hck : ctx.ck k i mn = false) (hmn : mn ≤ L)
    (hk : ∀ σ0 : St, σ0.mem = σ.mem → (∀ y, Expr.readsV y e = true → σ0.loc y = σ.loc y) →
      ∀ key, k = some key → key.len σ0 ≤ L)
    {j : Word} (hj : evalP σ i = .ok j) : j.toNat < L := by
  obtain ⟨σ0, h1, h2, h3⟩ := hfa
  have hs : safeIdx ctx.fa k i mn = true := by simpa [Ctx.ck] using hck
  exact safeIdx_sound hs h1 hmn (hk σ0 h2 h3)
    (by rw [evalP_congr h2 (fun y hy => h3 y (hsub y hy))]; exact hj)

end L.Compiler
