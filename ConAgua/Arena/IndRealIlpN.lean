import ConAgua.Arena.IndRealNames

/-!
# `name_rec_i` discharged (lane `indproofs4`, helper `indproofs4-ilp`)

The recipe of `IndRealNames.lean`'s `name_rec` (`nrF`, `nrF_ok`) for `name_rec_i(n, i)`: the
digit count (`dec_len`), `rec_` and the decimal digits of `i` written at the pool top (most
significant first, the loop running from the end, `x / 10` as `mulhi(x, ⌈2^67/10⌉) >> 3`), then
master's `intern_nstr`. The written words are `strWords s!"rec_{i}"` (`strWords_recI`).
-/

set_option linter.deprecated false
set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Decimal digits -/

/-- `x / 10` the way `dec_len` and `name_rec_i` compute it. -/
def div10W (x : Word) : Word := UInt64.ofNat (x.toNat * 14757395258967641293 / 2 ^ 64) >>> 3

theorem div10W_toNat (x : Word) : (div10W x).toNat = x.toNat / 10 := by
  have hx := x.toNat_lt
  have h1 : x.toNat * 14757395258967641293 / 2 ^ 64 < 2 ^ 64 := by omega
  simp only [div10W, UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h1]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
  omega

/-- The number of decimal digits of `n`. -/
def decLenN (n : Nat) : Nat := if n < 10 then 1 else decLenN (n / 10) + 1

theorem decLenN_le (n : Nat) : decLenN n ≤ n / 2 + 1 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold decLenN
    split
    · omega
    · have := ih (n / 10) (by omega); omega

theorem decLenN_pos (n : Nat) : 1 ≤ decLenN n := by
  unfold decLenN; split <;> omega

/-- The last `d` decimal digits of `x` as character words, most significant first. -/
def digsR : Nat → Nat → List Word
  | 0, _ => []
  | d + 1, x => digsR d (x / 10) ++ [(48 + x % 10 : Nat).toUInt64]

theorem strWords_append (s t : String) : strWords (s ++ t) = strWords s ++ strWords t := by
  simp [strWords, String.toByteArray_append]

theorem strWords_digit (d : Nat) (h : d < 10) :
    strWords (String.singleton (Nat.digitChar d)) = [(48 + d : Nat).toUInt64] := by
  have : ∀ e : Fin 10, strWords (String.singleton (Nat.digitChar e)) = [(48 + e : Nat).toUInt64] := by
    decide
  exact this ⟨d, h⟩

theorem strWords_repr (n : Nat) : strWords n.repr = digsR (decLenN n) n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · rw [Nat.repr_of_lt h, strWords_digit n h]
      unfold decLenN; rw [if_pos h]
      simp [digsR, Nat.mod_eq_of_lt h]
    · rw [Nat.repr_of_ge (by omega), strWords_append, ih (n / 10) (by omega),
        strWords_digit _ (Nat.mod_lt _ (by omega))]
      conv => rhs; unfold decLenN
      rw [if_neg h]; rfl

theorem strWords_recI (i : Nat) :
    strWords s!"rec_{i}" = [114, 101, 99, 95] ++ digsR (decLenN i) i := by
  have : s!"rec_{i}" = "rec_" ++ i.repr := by simp; rfl
  rw [this, strWords_append, strWords_repr]
  rfl

/-! ## `dec_len` -/

/-- `dec_len`'s loop (named, for its spec). -/
-- con-ron: none — `decLen`'s own loop (`rfl`), a named block for the proof
def dlLoop : Stmt := lblk (x, k) {
  while 9 < x {
    x := mulhi(x, 14757395258967641293) >> 3;
    k += 1
  }
}

theorem decLen_eq : L.Stubs.decLen = lfn (x) locals (k) {
  k := 1;
  ⟪dlLoop⟫;
  return k
} := rfl

/-- The model of `dec_len`'s loop at the loop's fuel. -/
def dlW : Nat → Word → Word → Option Word
  | 0, _, _ => none
  | f + 1, x, k => if 9 < x then dlW f (div10W x) (k + 1) else some k

theorem dlW_stop (f : Nat) (x k : Word) (h : ¬ 9 < x) : dlW (f + 1) x k = some k := by
  simp only [dlW, if_neg h]
theorem dlW_step (f : Nat) (x k : Word) (h : 9 < x) : dlW (f + 1) x k = dlW f (div10W x) (k + 1) := by
  simp only [dlW, if_pos h]

theorem dlLoop_spec (p : Prog) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p f dlLoop
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧
      dlW f (s₀.loc 0) (s₀.loc 1) = some (s'.loc 1); ⊤⦄ := by
  induction f generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ f ih =>
    rw [exec, step_while (w := dlLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih] <;>
      finish [dlW_stop, dlW_step, div10W]

theorem decLen_specW (p : Prog) (hp : p.lookup "dec_len" = some L.Stubs.decLen) (n : Nat)
    (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "dec_len" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ dlW (n + 1) x 1 = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp, decLen_eq]
  simp only [callFn]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      fun s => Triple.step_exec (dlLoop_spec p (n + 1) s)] <;>
    finish

theorem dlW_ok : ∀ (f : Nat) (x k r : Word), dlW f x k = some r →
    k.toNat + decLenN x.toNat < 2 ^ 64 → r.toNat = k.toNat + decLenN x.toNat - 1 := by
  intro f
  induction f with
  | zero => intro x k r h; simp [dlW] at h
  | succ f ih =>
    intro x k r h hb
    by_cases hx : 9 < x
    · rw [dlW_step f x k hx] at h
      have hx' : 10 ≤ x.toNat := by have := UInt64.lt_iff_toNat_lt.mp hx; simp at this; omega
      have hd : decLenN x.toNat = decLenN (x.toNat / 10) + 1 := by
        conv => lhs; unfold decLenN
        rw [if_neg (by omega)]
      have hk : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have := ih _ _ _ h (by rw [hk, div10W_toNat]; omega)
      rw [hk, div10W_toNat] at this; omega
    · rw [dlW_stop f x k hx] at h; cases h
      have hx' : x.toNat < 10 := by
        have := mt UInt64.lt_iff_toNat_lt.mpr hx; simp at this; omega
      unfold decLenN; rw [if_pos hx']; omega

/-! ## `name_rec_i`'s digit loop and body -/

/-- `name_rec_i`'s digit loop (named, for its spec). -/
-- con-ron: none — `nameRecIL`'s own loop (`rfl`), a named block for the proof
def digLoop : Stmt := lblk (n, i, k, o, j, x, q, s) {
  while o + 4 < j {
    j -= 1;
    q := mulhi(x, 14757395258967641293) >> 3;
    POOL.u64[j] := 48 + (x - q * 10);
    x := q
  }
}

theorem nameRecI_eq : L.Stubs.nameRecIL = lfn (n, i) locals (k, o, j, x, q, s) {
  k := call dec_len(i);
  o := call pool_room(k + 4);
  POOL.u64[o] := 114;
  POOL.u64[o + 1] := 101;
  POOL.u64[o + 2] := 99;
  POOL.u64[o + 3] := 95;
  j := o + 4 + k;
  x := i;
  ⟪digLoop⟫;
  s := call intern_nstr(n, o, k + 4);
  if s >= 4294967296 { abort };
  return s
} := rfl

/-- The model of the digit loop at the loop's fuel: the pool words below `j` down to `o + 4`. -/
def digW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | f + 1, m, o, j, x =>
    if o + 4 < j then digW f (m.set64 POOL (j - 1) (48 + (x - div10W x * 10))) o (j - 1) (div10W x)
    else some m

theorem digW_stop (f : Nat) (m : Mem) (o j x : Word) (h : ¬ o + 4 < j) : digW (f + 1) m o j x = some m := by
  simp only [digW, if_neg h]
theorem digW_step (f : Nat) (m : Mem) (o j x : Word) (h : o + 4 < j) : digW (f + 1) m o j x =
    digW f (m.set64 POOL (j - 1) (48 + (x - div10W x * 10))) o (j - 1) (div10W x) := by
  simp only [digW, if_pos h]

theorem digLoop_spec (p : Prog) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p f digLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
      digW f s₀.mem (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) = some s'.mem; ⊤⦄ := by
  induction f generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ f ih =>
    rw [exec, step_while (w := digLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, st64, ih] <;>
      finish [digW_stop, digW_step, div10W]

/-- The four bytes `rec_` at `o`. -/
def recIBytes (m : Mem) (o : Word) : Mem :=
  (((m.set64 POOL o 114).set64 POOL (o + 1) 101).set64 POOL (o + 2) 99).set64 POOL (o + 3) 95

/-- `name_rec_i`'s body over its callees' runs. -/
def nriW (p : Prog) (n : Nat) (m : Mem) (x i : Word) : Option (Word × Mem) :=
  match callW p n "dec_len" [i] m with
  | none => none
  | some (r₁, m₁) =>
    match callW p n "pool_room" [r₁.headD 0 + 4] m₁ with
    | none => none
    | some (r₂, m₂) =>
      match digW (n + 1) (recIBytes m₂ (r₂.headD 0)) (r₂.headD 0) (r₂.headD 0 + 4 + r₁.headD 0) i with
      | none => none
      | some m₃ =>
        match callW p n "intern_nstr" [x, r₂.headD 0, r₁.headD 0 + 4] m₃ with
        | none => none
        | some (r₄, m₄) => if 4294967296 ≤ r₄.headD 0 then none else some (r₄.headD 0, m₄)

theorem nameRecI_specW (p : Prog) (hp : p.lookup "name_rec_i" = some L.Stubs.nameRecIL) (n : Nat)
    (s₀ : St) (x i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "name_rec_i" [x, i]
    ⦃fun r s' => LocEq s' s₀ ∧ nriW p n s₀.mem x i = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp, nameRecI_eq]
  simp only [callFn]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "dec_len", callW_spec p n "pool_room", callW_spec p n "intern_nstr",
      fun s => Triple.step_exec (digLoop_spec p (n + 1) s)] <;>
    finish [nriW, recIBytes]

/-! ## The program and the model -/

/-- `name_rec_i` and its callees. -/
def nriProg : Prog :=
  [("name_rec_i", L.Stubs.nameRecIL), ("dec_len", L.Stubs.decLen), ("pool_room", L.Stubs.poolRoom),
   ("intern_nstr", internNStr), ("lit_hash", litHash), ("limbs_eq", limbsEq),
   ("nstr_match", nsMatch), ("nstr_find", nsFind), ("nstr_push", nsPush)]

def nriFns : List FnName := nriProg.map (·.1)

/-- `name_rec_i` writes the pool (and its top) and the `str` table. -/
theorem nriProg_closed : closedA nriProg [POOL, NSREC, NSSLOT] [0, 36, 37] nriFns = true := by
  decide +kernel

abbrev NriF (p : Prog) : Prop := ProgHas p nriProg

/-- **The model of `name_rec_i`.** -/
noncomputable def nriF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF nriProg "name_rec_i" m args

theorem nriF_spec (p : Prog) (hp : NriF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "name_rec_i" args
    ⦃fun r s' => LocEq s' s₀ ∧ nriF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec nriProg_closed (hp.agree nriFns) (by decide) n s₀ args

/-! ## The words written -/

theorem sliceL_snoc (p : Array Word) (o l : Nat) :
    sliceL p o (l + 1) = sliceL p o l ++ [p[o + l]?.getD 0] := by
  simp only [sliceL, List.ofFn_succ_last, Fin.val_last, Fin.val_castSucc]

theorem sliceL_add (p : Array Word) (o a : Nat) : ∀ b, sliceL p o (a + b) = sliceL p o a ++ sliceL p (o + a) b
  | 0 => by simp [sliceL]
  | b + 1 => by
    rw [← Nat.add_assoc, sliceL_snoc, sliceL_add p o a b, sliceL_snoc, List.append_assoc, Nat.add_assoc]

theorem sliceL_congr {p p' : Array Word} {o l : Nat} (h : ∀ t < l, p[o + t]? = p'[o + t]?) :
    sliceL p o l = sliceL p' o l := by
  simp only [sliceL]; congr 1; funext t; rw [h t t.2]

theorem getElem?_set64_pool (m : Mem) (q x : Word) (t : Nat) (hq : q.toNat < (m.arr64 POOL).size) :
    ((m.set64 POOL q x).arr64 POOL)[t]? = if q.toNat = t then some x else (m.arr64 POOL)[t]? := by
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h : q.toNat = t
  · subst h; simp [hq]
  · simp [h]

/-- **The digit loop**: from `j` down to `o + 4`, the last `j - o - 4` digits of `x`; nothing
else in the pool changes, the growth from `m₀` is kept. -/
theorem digW_ok (m₀ : Mem) : ∀ (f : Nat) (m m' : Mem) (o j x : Word), digW f m o j x = some m' →
    o.toNat + 4 < 2 ^ 64 → o.toNat + 4 ≤ j.toNat → j.toNat ≤ (m.arr64 POOL).size →
    Grows m₀ m → m₀.top.toNat ≤ o.toNat →
    Grows m₀ m' ∧ m'.top = m.top ∧ (m'.arr64 POOL).size = (m.arr64 POOL).size ∧
      (∀ t, (t < o.toNat + 4 ∨ j.toNat ≤ t) → (m'.arr64 POOL)[t]? = (m.arr64 POOL)[t]?) ∧
      sliceL (m'.arr64 POOL) (o.toNat + 4) (j.toNat - (o.toNat + 4)) =
        digsR (j.toNat - (o.toNat + 4)) x.toNat := by
  intro f
  induction f with
  | zero => intro m m' o j x h; simp [digW] at h
  | succ f ih =>
    intro m m' o j x h ho hj hjs hg ht
    have ho4 : (o + 4).toNat = o.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
    by_cases hc : o + 4 < j
    · rw [digW_step f m o j x hc] at h
      have hc' : o.toNat + 4 < j.toNat := by rw [← ho4]; exact UInt64.lt_iff_toNat_lt.mp hc
      have hj1 : (j - 1).toNat = j.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
      have hq : (j - 1).toNat < (m.arr64 POOL).size := by omega
      have hsz : ((m.set64 POOL (j - 1) (48 + (x - div10W x * 10))).arr64 POOL).size = (m.arr64 POOL).size :=
        Mem.size_arr64_set64 _ _ _ _
      have hg1 := grows_set_above hg (q := j - 1) (x := 48 + (x - div10W x * 10)) (by omega)
      obtain ⟨hg', htop, hsz', hkeep, hsl⟩ := ih _ m' o (j - 1) (div10W x) h ho (by omega)
        (by rw [hsz]; omega) hg1 ht
      have htop1 : (m.set64 POOL (j - 1) (48 + (x - div10W x * 10))).top = m.top := by
        simp only [top_rdW, Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ POOL by decide)]
      refine ⟨hg', by rw [htop, htop1], by rw [hsz', hsz], fun t ht' => ?_, ?_⟩
      · rw [hkeep t (by omega), getElem?_set64_pool _ _ _ _ hq, if_neg (by omega)]
      · have hd : j.toNat - (o.toNat + 4) = (j.toNat - 1 - (o.toNat + 4)) + 1 := by omega
        rw [hd, sliceL_snoc, digsR, ← hj1, hsl, div10W_toNat]
        congr 2
        have e : o.toNat + 4 + ((j - 1).toNat - (o.toNat + 4)) = (j - 1).toNat := by omega
        rw [e, hkeep _ (.inr (Nat.le_refl _)), getElem?_set64_pool _ _ _ _ hq, if_pos rfl]
        simp only [Option.getD_some]
        apply UInt64.toNat_inj.mp
        have hx := x.toNat_lt
        have hd10 := div10W_toNat x
        have hm : (div10W x * 10).toNat = x.toNat / 10 * 10 := by
          rw [UInt64.toNat_mul, hd10]; simp; omega
        have hs : (x - div10W x * 10).toNat = x.toNat % 10 := by
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hm]; omega), hm]; omega
        rw [UInt64.toNat_add, hs]; simp
    · rw [digW_stop f m o j x hc] at h; cases h
      have hc' : ¬ o.toNat + 4 < j.toNat := fun h' => hc (by rw [UInt64.lt_iff_toNat_lt, ho4]; exact h')
      have h0 : j.toNat - (o.toNat + 4) = 0 := by omega
      exact ⟨hg, rfl, rfl, fun _ _ => rfl, by rw [h0]; simp [sliceL, digsR]⟩

/-- **The bytes `rec_` after the reserved room** grow the pool. -/
theorem recIBytes_ok (m : Mem) (hpool : PoolOK m) (R : Word) (hR : 4 ≤ R.toNat)
    (hno : m.top.toNat + R.toNat < 2 ^ 64) (hs : m.top.toNat + R.toNat ≤ (m.arr64 POOL).size) :
    Grows m (recIBytes (m.set64 CTL 0 (m.top + R)) m.top) ∧
      (recIBytes (m.set64 CTL 0 (m.top + R)) m.top).top = m.top + R ∧
      ((recIBytes (m.set64 CTL 0 (m.top + R)) m.top).arr64 POOL).size = (m.arr64 POOL).size ∧
      sliceL ((recIBytes (m.set64 CTL 0 (m.top + R)) m.top).arr64 POOL) m.top.toNat 4 =
        [114, 101, 99, 95] := by
  have hc := hpool.2.1
  have e1 : (m.top + 1).toNat = m.top.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (m.top + 2).toNat = m.top.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : (m.top + 3).toNat = m.top.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have eR : (m.top + R).toNat = m.top.toNat + R.toNat := by rw [UInt64.toNat_add]; omega
  have g0 := grows_top m (m.top + R) hc (by omega) (by omega)
  have g1 := grows_set_above g0 (q := m.top) (x := 114) (Nat.le_refl _)
  have g2 := grows_set_above g1 (q := m.top + 1) (x := 101) (by omega)
  have g3 := grows_set_above g2 (q := m.top + 2) (x := 99) (by omega)
  have g4 := grows_set_above g3 (q := m.top + 3) (x := 95) (by omega)
  have htop : (recIBytes (m.set64 CTL 0 (m.top + R)) m.top).top = m.top + R := by
    simp only [recIBytes, top_rdW, Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ POOL by decide)]
    exact Mem.top_set64 _ _ hc
  have hsz : ((recIBytes (m.set64 CTL 0 (m.top + R)) m.top).arr64 POOL).size = (m.arr64 POOL).size := by
    simp only [recIBytes, size_set64]
  refine ⟨g4, htop, hsz, ?_⟩
  simp only [sliceL, recIBytes, Mem.arr64_set64_ne _ _ _ _ _ (show POOL ≠ CTL by decide),
    Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, e1, e2, e3,
    List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, Array.getElem?_setIfInBounds,
    Array.size_setIfInBounds]
  simp (config := { decide := true }) [show m.top.toNat < (m.arr64 POOL).size by omega,
    show m.top.toNat + 1 < (m.arr64 POOL).size by omega, show m.top.toNat + 2 < (m.arr64 POOL).size by omega,
    show m.top.toNat + 3 < (m.arr64 POOL).size by omega]

theorem callW_dl {n : Nat} {m m' : Mem} {i : Word} {r : List Word}
    (h : callW nriProg n "dec_len" [i] m = some (r, m')) :
    m' = m ∧ (r.headD 0).toNat = decLenN i.toNat := by
  cases n with
  | zero => exact (callW_zero_false h).elim
  | succ n =>
    obtain ⟨s', hs', -, hm, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (decLen_specW nriProg rfl n _ i) h
    refine ⟨hs'.symm.trans hm, ?_⟩
    have := dlW_ok _ _ _ _ hW (by have := decLenN_le i.toNat; have := i.toNat_lt; simp; omega)
    rw [show (1 : Word).toNat = 1 from rfl] at this; have := decLenN_pos i.toNat; omega

/-- **`name_rec_i`'s model refines `internNNode (.str n s!"rec_{i}")`** (replaces
`IndStubs.nameRecI_spec`). -/
theorem nriF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (x i : Word) (hx : H x) :
    RelW nriF [x, i] (StageR dn vis fe) (internNNode (.str (decI x) s!"rec_{i.toNat}"))
      (KeepPost dn vis fe decW0N) := by
  intro m m' a r hc hS
  obtain ⟨n', hc'⟩ := callF_run hc
  cases n' with
  | zero => exact (callW_zero_false hc').elim
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (nameRecI_specW nriProg rfl n _ x i) hc'
  simp only at hs' hW
  rw [hs'] at hW
  unfold nriW at hW
  cases h1 : callW nriProg n "dec_len" [i] m with
  | none => rw [h1] at hW; cases hW
  | some q1 =>
  obtain ⟨r₁, m₁⟩ := q1
  rw [h1] at hW
  simp only at hW
  obtain ⟨rfl, hk⟩ := callW_dl h1
  generalize r₁.headD 0 = k at hW hk
  cases h2 : callW nriProg n "pool_room" [k + 4] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q2 =>
  obtain ⟨r₂, m₂⟩ := q2
  rw [h2] at hW
  simp only at hW
  obtain ⟨ho, hm₂, hno, hroom⟩ := prW_some (callW_pr rfl h2)
  rw [ho, hm₂] at hW
  have hpool : PoolOK m₁ := hS.1.arena.1.lit.1
  have hk4 : (k + 4).toNat = k.toNat + 4 := by
    have := decLenN_le i.toNat; have := i.toNat_lt; rw [UInt64.toNat_add]; simp; omega
  obtain ⟨hg, htop, hsz, hb⟩ := recIBytes_ok m₁ hpool (k + 4) (by omega) hno hroom
  generalize hm₃ : recIBytes (m₁.set64 CTL 0 (m₁.top + (k + 4))) m₁.top = m₃ at hW hg htop hsz hb
  have hj : (m₁.top + 4 + k).toNat = m₁.top.toNat + 4 + k.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_add]; simp; omega
  cases h3 : digW (n + 1) m₃ m₁.top (m₁.top + 4 + k) i with
  | none => rw [h3] at hW; cases hW
  | some m₄ =>
  rw [h3] at hW
  simp only at hW
  obtain ⟨hg4, htop4, hsz4, hkeep4, hsl4⟩ := digW_ok m₁ (n + 1) m₃ m₄ m₁.top (m₁.top + 4 + k) i h3
    (by omega) (by omega) (by rw [hsz]; omega) hg (Nat.le_refl _)
  rw [hj, show m₁.top.toNat + 4 + k.toNat - (m₁.top.toNat + 4) = k.toNat by omega, hk] at hsl4
  have hslice : sliceL (m₄.arr64 POOL) m₁.top.toNat (k + 4).toNat = strWords s!"rec_{i.toNat}" := by
    rw [hk4, Nat.add_comm k.toNat 4, sliceL_add, strWords_recI, hk, hsl4, ← hb]
    congr 1
    exact sliceL_congr fun t ht => hkeep4 _ (.inl (by omega))
  have hsl : SliceOK m₄ m₁.top (k + 4) := by
    have eR : (m₁.top + (k + 4)).toNat = m₁.top.toNat + (k + 4).toNat := by
      rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt hno
    simp only [SliceOK, htop4, htop, eR]; omega
  cases h4 : callW nriProg n "intern_nstr" [x, m₁.top, k + 4] m₄ with
  | none => rw [h4] at hW; cases hW
  | some q4 =>
  obtain ⟨r₄, m₅⟩ := q4
  rw [h4] at hW
  simp only at hW
  obtain ⟨c, hW⟩ := of_ite_none hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have hR₄ : ArenaR m₄ a := ArenaR.grow m₁ m₄ hg4 a hS.1.arena.1
  have hps : (m₁.arr64 POOL).size < 2 ^ 63 := hpool.2.2.1
  obtain ⟨s₅, hs₅, -, hok, hR₅, hres⟩ := triple_of_callW
    (internNStr_refinesA nriProg rfl rfl rfl rfl rfl rfl a n ⟨m₄, Locals.init []⟩ x m₁.top (k + 4) hR₄
      hx hsl s!"rec_{i.toNat}" hslice) h4
  obtain ⟨s₅', hs₅', -, hI⟩ := triple_of_callW (s₀ := ⟨m₄, Locals.init []⟩)
    (internNStr_spec nriProg rfl rfl rfl rfl rfl rfl n _ x m₁.top (k + 4) (by simp only; omega)
      (by simp only; rw [hk4]; omega)) h4
  simp only at hs₅ hR₅ hs₅' hI
  rw [hs₅] at hR₅
  rw [hs₅'] at hI
  have hfr : MemFrame [POOL, NSREC, NSSLOT] [0, 36, 37] m₁ m₅ :=
    ((grows_frame m₁ m₄ hg4).mono (by simp) (by simp)).trans
      ((consInternM_frame nstrCS_wf hI).mono (by simp [nstrCS]) (by simp [nstrCS]))
  obtain ⟨a', hrun, hS', hg', -, -⟩ := stage_of_name hS
    (internNNode_str_run (decI x) s!"rec_{i.toNat}" a) hok hR₅
    hres hfr (by simp [POOL, NSREC, NSSLOT]) (by simp) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)
  rw [hr] at hrun c
  refine ⟨decI (r.headD 0), a', hrun, hS', hg', ?_, rfl⟩
  have := mt UInt64.le_iff_toNat_le.mpr c
  have e : (4294967296 : Word).toNat = 4294967296 := rfl
  rw [e] at this; omega

end L.Ind
