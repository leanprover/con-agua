module

public import ConAgua.Arena.SlotGrow
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# The growth block's model and spec (lane slotgrow)

The models of the loops of `growB` (`SlotGrow.lean`), each a function of the memory and the loop's
variables that returns `none` where the L code aborts, and the spec of the block as spliced into a
push (`growBlkG S o`): it keeps the push's own variables (below `o`) and leaves the memory
`growM S.sa S.ca H m`, where `H m t i` is the hash the schema's `hash` block computes for node
`i` of tier `t` (`HashOK`).

The table relation's side (the growth re-registers every node, so every node is found again) is
`StoreLib.lean`'s `storeR_growIf`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The growth exponent of slot array `sa`: its last word. -/
def gexpW (sa : ArrId) (m : Mem) : Word := rdW (m.arr64 sa) (m.len64 sa - 1)

/-- The slot count of a tier of the table with slot array `sa`. -/
def gnW (sa : ArrId) (m : Mem) : Word := SN0 <<< gexpW sa m

/-- The probe loop: from slot `j` of tier `t` after `d` steps, the first free slot (`none`: the
abort after `n` steps). -/
def gprobeW (sl : Array Word) (t n j d : Word) : Option Word :=
  if rdW sl (j * 2 + t) = 0 then some j
  else if n ≤ d then none
  else gprobeW sl t n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by
    have := ‹¬ n ≤ d›; simp only [UInt64.le_iff_toNat_le] at this; omega
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  omega

/-- The node loop: register nodes `i, …, c - 1` of tier `t` (slot base `b`) among `n` slots,
`H` the hash of a node. -/
def gnodesW (sa : ArrId) (H : Mem → Word → Word → Word) (n t b c i : Word) (m : Mem) :
    Option Mem :=
  if i < c then
    match gprobeW (m.arr64 sa) t n (homeW (H m t i) n) 0 with
    | none => none
    | some j => gnodesW sa H n t b c (i + 1) (m.set64 sa (j * 2 + t) (b + i + 1))
  else some m
termination_by c.toNat - i.toNat
decreasing_by
  have : i.toNat < c.toNat := UInt64.lt_iff_toNat_lt.mp ‹i < c›
  have := c.toNat_lt
  have : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  omega

/-- The tier loop: register the nodes of tiers `t, …, 1`. -/
def gtiersW (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (n t : Word) (m : Mem) :
    Option Mem :=
  if t < 2 then
    match gnodesW sa H n t (rdW (m.arr64 CTL) SCB * t) (rdW (m.arr64 CTL) (ca + t)) 0 m with
    | none => none
    | some m' => gtiersW sa ca H n (t + 1) m'
  else some m
termination_by 2 - t.toNat
decreasing_by
  have : t.toNat < 2 := UInt64.lt_iff_toNat_lt.mp ‹t < 2›
  have : (t + 1).toNat = t.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  omega

/-- Eight zero words of `sa` from `k`. -/
def zero8 (sa : ArrId) (k : Word) (m : Mem) : Mem :=
  (((((((m.set64 sa k 0).set64 sa (k + 1) 0).set64 sa (k + 2) 0).set64 sa (k + 3) 0).set64 sa
    (k + 4) 0).set64 sa (k + 5) 0).set64 sa (k + 6) 0).set64 sa (k + 7) 0

/-- The zero loop: the words `[k, n)` of `sa`, eight at a time. (Where `k + 8` would wrap, the
L code's stores are out of bounds: the model stops.) -/
def gzeroW (sa : ArrId) (n k : Word) (m : Mem) : Mem :=
  if k < n ∧ k.toNat + 8 < 2 ^ 64 then gzeroW sa n (k + 8) (zero8 sa k m) else m
termination_by n.toNat - k.toNat
decreasing_by
  have : k.toNat < n.toNat := UInt64.lt_iff_toNat_lt.mp ‹k < n ∧ _›.1
  have : (k + 8).toNat = k.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  omega

/-- **The growth**: the memory after `growB`, `none` where it aborts. -/
def growM (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (m : Mem) : Option Mem :=
  if (m.len64 sa - 1) >>> 1 < gnW sa m * 2 then none
  else gtiersW sa ca H (gnW sa m * 2) 0
    (gzeroW sa (gnW sa m * 2) 0 (m.set64 sa (m.len64 sa - 1) (gexpW sa m + 1)))

/-- **A push's tail**: from the memory `m` after the push's writes, grow if node count `c + 1`
passes half the slot count of the memory `m₀` before them (the push reads the exponent first). -/
def growIf (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (m₀ m : Mem) (c : Word) :
    Option Mem :=
  if gnW sa m₀ < (c + 1) * 2 then growM sa ca H m else some m

theorem growIf_grow (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (m₀ m : Mem) (c : Word)
    (h : gnW sa m₀ < (c + 1) * 2) : growIf sa ca H m₀ m c = growM sa ca H m := by
  simp [growIf, h]

theorem growIf_keep (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (m₀ m : Mem) (c : Word)
    (h : ¬ gnW sa m₀ < (c + 1) * 2) : growIf sa ca H m₀ m c = some m := by
  simp [growIf, h]

/-! ### The frame of the growth -/

/-- From `m` to `m'` only array `sa` changes, and no size. -/
def GFr (sa : ArrId) (m m' : Mem) : Prop :=
  (∀ b, b ≠ sa → m'.arr64 b = m.arr64 b) ∧ (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧
    m'.words.size = m.words.size

theorem GFr.refl (sa : ArrId) (m : Mem) : GFr sa m m := ⟨fun _ _ => rfl, fun _ => rfl, rfl⟩

theorem GFr.trans {sa : ArrId} {m₁ m₂ m₃ : Mem} (h₁ : GFr sa m₁ m₂) (h₂ : GFr sa m₂ m₃) :
    GFr sa m₁ m₃ :=
  ⟨fun b hb => (h₂.1 b hb).trans (h₁.1 b hb), fun b => (h₂.2.1 b).trans (h₁.2.1 b),
    h₂.2.2.trans h₁.2.2⟩

theorem GFr.set64 (sa : ArrId) (m : Mem) (i v : Word) : GFr sa m (m.set64 sa i v) := by
  refine ⟨fun b hb => Mem.arr64_set64_ne _ _ _ _ _ hb, fun b => ?_, Mem.words_size_set64 _ _ _ _⟩
  by_cases h : b = sa
  · subst h; exact Mem.size_arr64_set64 _ _ _ _
  · rw [Mem.arr64_set64_ne _ _ _ _ _ h]

theorem GFr.zero8 (sa : ArrId) (k : Word) (m : Mem) : GFr sa m (zero8 sa k m) := by
  unfold L.Arena.zero8
  exact ((((((GFr.set64 _ _ _ _).trans (GFr.set64 _ _ _ _)).trans (GFr.set64 _ _ _ _)).trans
    (GFr.set64 _ _ _ _)).trans (GFr.set64 _ _ _ _)).trans (GFr.set64 _ _ _ _)).trans
    (GFr.set64 _ _ _ _) |>.trans (GFr.set64 _ _ _ _)

theorem gzeroW_fr (sa : ArrId) (n k : Word) (m : Mem) : GFr sa m (gzeroW sa n k m) := by
  fun_induction gzeroW sa n k m with
  | case1 k m _ ih => exact (GFr.zero8 sa k m).trans ih
  | case2 => exact GFr.refl _ _

theorem gnodesW_fr (sa : ArrId) (H : Mem → Word → Word → Word) (n t b c i : Word) (m m' : Mem)
    (h : gnodesW sa H n t b c i m = some m') : GFr sa m m' := by
  fun_induction gnodesW sa H n t b c i m generalizing m' with
  | case1 => simp_all
  | case2 i m _ j _ ih => exact (GFr.set64 _ _ _ _).trans (ih _ h)
  | case3 => simp_all; subst h; exact GFr.refl _ _

theorem gtiersW_fr (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (n t : Word)
    (m m' : Mem) (h : gtiersW sa ca H n t m = some m') : GFr sa m m' := by
  fun_induction gtiersW sa ca H n t m generalizing m' with
  | case1 => simp_all
  | case2 t m _ m₁ hm ih => exact (gnodesW_fr _ _ _ _ _ _ _ _ _ hm).trans (ih _ h)
  | case3 => simp_all; subst h; exact GFr.refl _ _

/-- `growIf_grow` with the test as the push computes it (the exponent read before its writes). -/
theorem growIf_grow' (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (m₀ m : Mem) (c : Word)
    (h : SN0 <<< rdW (m₀.arr64 sa) (m₀.len64 sa - 1) < (c + 1) * 2) :
    growIf sa ca H m₀ m c = growM sa ca H m :=
  growIf_grow sa ca H m₀ m c h

theorem growIf_keep' (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (m₀ m : Mem) (c : Word)
    (h : ¬ SN0 <<< rdW (m₀.arr64 sa) (m₀.len64 sa - 1) < (c + 1) * 2) :
    growIf sa ca H m₀ m c = some m :=
  growIf_keep sa ca H m₀ m c h

/-- **The growth writes only the slot array** (and keeps every size). -/
theorem growIf_frame (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (m₀ m m' : Mem)
    (c : Word) (h : growIf sa ca H m₀ m c = some m') :
    (∀ b, b ≠ sa → m'.arr64 b = m.arr64 b) ∧ (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧
      m'.words.size = m.words.size := by
  change GFr sa m m'
  unfold growIf at h
  split at h
  · unfold growM at h
    split at h
    · simp at h
    · exact ((GFr.set64 _ _ _ _).trans (gzeroW_fr _ _ _ _)).trans (gtiersW_fr _ _ _ _ _ _ _ h)
  · simp at h; subst h; exact GFr.refl _ _

/-- **The growth commutes with a write to another array** that the hash does not read (a push's
column write before its growth). -/
theorem growIf_set64 (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (m₀ m : Mem) (c : Word)
    (A : ArrId) (k x : Word) (hA : A ≠ sa) (hAc : A ≠ CTL)
    (hH : ∀ (m : Mem) (t i : Word), H (m.set64 A k x) t i = H m t i) :
    growIf sa ca H m₀ (m.set64 A k x) c = (growIf sa ca H m₀ m c).map (fun m' => m'.set64 A k x) := by
  sorry

/-- The schema's `hash` block, spliced at `o`, sets `h` (`o + 5`) to `H m t i` (`t` at `o + 2`,
`i` at `o + 3`) and changes nothing else. -/
def HashOK (p : Prog) (S : GrowSch) (o : Nat) (H : Mem → Word → Word → Word) : Prop :=
  ∀ (k : Stmt → M Sig) (s₀ : St),
    ⦃fun s => s = s₀⦄
    step p k (shiftS o S.hash)
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧
      LocEq s' (s₀.setLoc (o + 5) (H s₀.mem (s₀.loc (o + 2)) (s₀.loc (o + 3)))); ⊤⦄

/-- The variables below `o` are kept. -/
def KeepLo (o : Nat) (s s' : St) : Prop := ∀ x, x < o → s'.loc x = s.loc x

theorem KeepLo.loc {o : Nat} {s s' : St} (h : KeepLo o s s') (x : Var) (hx : x < o) :
    s'.loc x = s.loc x := h x hx

grind_pattern [lang_grind] KeepLo.loc => KeepLo o s s', s'.loc x

/-! ### The loops of the growth block, spliced at `o`

`n, k, t, i, c, h, j, b, d` are the locals `o + 0 … o + 8`. -/

/-- Every local but `x` and `y` is kept. -/
def Keep2 (x y : Var) (s s' : St) : Prop := ∀ z, z ≠ x → z ≠ y → s'.loc z = s.loc z

theorem Keep2.loc {x y : Var} {s s' : St} (h : Keep2 x y s s') (z : Var) (hx : z ≠ x) (hy : z ≠ y) :
    s'.loc z = s.loc z := h z hx hy

grind_pattern [lang_grind] Keep2.loc => Keep2 x y s s', s'.loc z

theorem gprobeW_free (sl : Array Word) (t n j d : Word) (k : Nat) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : sl[k] = 0) : gprobeW sl t n j d = some j := by
  rw [gprobeW, rdW_eq sl _ k hk hks]; simp [hv]

theorem gprobeW_next (sl : Array Word) (t n j d : Word) (k : Nat) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : sl[k] ≠ 0) (hd : ¬ n ≤ d) :
    gprobeW sl t n j d = gprobeW sl t n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1) := by
  rw [gprobeW, rdW_eq sl _ k hk hks]; simp [hv, hd]

grind_pattern [arena_grind] gprobeW_free => gprobeW sl t n j d, sl[k]
grind_pattern [arena_grind] gprobeW_next => gprobeW sl t n j d, sl[k]

theorem probeLoop_spec (p : Prog) (S : GrowSch) (o : Nat) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (shiftS o (probeLoopB S))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ Keep2 (o + 6) (o + 8) s₀ s' ∧
      gprobeW (s₀.mem.arr64 S.sa) (s₀.loc (o + 2)) (s₀.loc o) (s₀.loc (o + 6)) (s₀.loc (o + 8)) =
        some (s'.loc (o + 6)); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := shiftS o (probeLoopB S)) rfl]
  simp only [shiftS, shiftC, shiftE]
  simp only [Nat.add_comm _ o, Nat.add_zero]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, setLoc, ld64, ih] <;> finish [Keep2]

theorem probeLoop_step_spec (p : Prog) (S : GrowSch) (o : Nat) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (shiftS o (probeLoopB S))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ Keep2 (o + 6) (o + 8) s₀ s' ∧
      gprobeW (s₀.mem.arr64 S.sa) (s₀.loc (o + 2)) (s₀.loc o) (s₀.loc (o + 6)) (s₀.loc (o + 8)) =
        some (s'.loc (o + 6)); ⊤⦄ :=
  Triple.step_exec (probeLoop_spec p S o (n + 1) s₀)

section nodes
variable (sa : ArrId) (H : Mem → Word → Word → Word) (n t b c i : Word) (m : Mem)

theorem gnodesW_done (h : ¬ i < c) : gnodesW sa H n t b c i m = some m := by
  rw [gnodesW]; simp [h]

theorem gnodesW_step (sl : Array Word) (j₀ d : Word) (hi : i < c) (hsl : sl = m.arr64 sa)
    (hj₀ : j₀ = UInt64.ofNat (((H m t i * golden) ^^^ ((H m t i * golden) >>> 32)).toNat * n.toNat / 2 ^ 64)) (hd : d = 0) (hs : (gprobeW sl t n j₀ d).isSome) :
    gnodesW sa H n t b c i m = gnodesW sa H n t b c (i + 1)
      (m.set64 sa ((gprobeW sl t n j₀ d).getD 0 * 2 + t) (b + i + 1)) := by
  subst hsl hd
  have e0 : homeW (H m t i) n = j₀ := by rw [hj₀]; rfl
  rw [gnodesW, e0]; simp only [hi, ↓reduceIte]
  cases e : gprobeW (m.arr64 sa) t n j₀ 0 <;> simp_all

end nodes

grind_pattern [arena_grind] gnodesW_done => gnodesW sa H n t b c i m
grind_pattern [arena_grind] gnodesW_step => gnodesW sa H n t b c i m, gprobeW sl t n j₀ d

theorem nodeLoop_spec (p : Prog) (S : GrowSch) (o : Nat) (H : Mem → Word → Word → Word)
    (hH : HashOK p S o H) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (shiftS o (nodeLoopB S))
    ⦃fun r s' => r = .normal ∧ KeepLo o s₀ s' ∧ s'.loc o = s₀.loc o ∧
      s'.loc (o + 2) = s₀.loc (o + 2) ∧
      gnodesW S.sa H (s₀.loc o) (s₀.loc (o + 2)) (s₀.loc (o + 7)) (s₀.loc (o + 4)) (s₀.loc (o + 3))
        s₀.mem = some s'.mem; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := shiftS o (nodeLoopB S)) rfl]
  simp only [shiftS, shiftC, shiftE]
  simp only [Nat.add_comm _ o, Nat.add_zero]
  vcgen [step, evalE, evalC, setLoc, ld64, st64, ih, hH (exec p n), probeLoop_step_spec p S o n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval, decide_eq_true_eq,
    Nat.add_left_cancel_iff, Nat.left_eq_add, Nat.reduceEqDiff, ite_true, ite_false] at *)
  all_goals grind [lang_grind, arena_grind, KeepLo, Keep2]

theorem nodeLoop_step_spec (p : Prog) (S : GrowSch) (o : Nat) (H : Mem → Word → Word → Word)
    (hH : HashOK p S o H) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (shiftS o (nodeLoopB S))
    ⦃fun r s' => r = .normal ∧ KeepLo o s₀ s' ∧ s'.loc o = s₀.loc o ∧
      s'.loc (o + 2) = s₀.loc (o + 2) ∧
      gnodesW S.sa H (s₀.loc o) (s₀.loc (o + 2)) (s₀.loc (o + 7)) (s₀.loc (o + 4)) (s₀.loc (o + 3))
        s₀.mem = some s'.mem; ⊤⦄ :=
  Triple.step_exec (nodeLoop_spec p S o H hH (n + 1) s₀)

section tiers
variable (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (n t : Word) (m : Mem)

theorem gtiersW_done (h : ¬ t < 2) : gtiersW sa ca H n t m = some m := by
  rw [gtiersW]; simp [h]

theorem gtiersW_step (b c i : Word) (ht : t < 2) (hb : b = rdW (m.arr64 CTL) SCB * t)
    (hc : c = rdW (m.arr64 CTL) (ca + t)) (hi : i = 0) (hs : (gnodesW sa H n t b c i m).isSome) :
    gtiersW sa ca H n t m = gtiersW sa ca H n (t + 1) ((gnodesW sa H n t b c i m).getD m) := by
  subst hb hc hi
  rw [gtiersW]; simp only [ht, ↓reduceIte]
  cases e : gnodesW sa H n t (rdW (m.arr64 CTL) SCB * t) (rdW (m.arr64 CTL) (ca + t)) 0 m <;> simp_all

end tiers

grind_pattern [arena_grind] gtiersW_done => gtiersW sa ca H n t m
grind_pattern [arena_grind] gtiersW_step => gtiersW sa ca H n t m, gnodesW sa H n t b c i m

theorem tierLoop_spec (p : Prog) (S : GrowSch) (o : Nat) (H : Mem → Word → Word → Word)
    (hH : HashOK p S o H) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (shiftS o (tierLoopB S))
    ⦃fun r s' => r = .normal ∧ KeepLo o s₀ s' ∧
      gtiersW S.sa S.ca H (s₀.loc o) (s₀.loc (o + 2)) s₀.mem = some s'.mem; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := shiftS o (tierLoopB S)) rfl]
  simp only [shiftS, shiftC, shiftE]
  simp only [Nat.add_comm _ o]
  vcgen [step, evalE, evalC, setLoc, ld64, st64, ih, nodeLoop_step_spec p S o H hH n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval, decide_eq_true_eq,
    Nat.add_left_cancel_iff, Nat.left_eq_add, Nat.reduceEqDiff, ite_true, ite_false] at *)
  all_goals grind [lang_grind, arena_grind, KeepLo]

theorem tierLoop_step_spec (p : Prog) (S : GrowSch) (o : Nat) (H : Mem → Word → Word → Word)
    (hH : HashOK p S o H) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (shiftS o (tierLoopB S))
    ⦃fun r s' => r = .normal ∧ KeepLo o s₀ s' ∧
      gtiersW S.sa S.ca H (s₀.loc o) (s₀.loc (o + 2)) s₀.mem = some s'.mem; ⊤⦄ :=
  Triple.step_exec (tierLoop_spec p S o H hH (n + 1) s₀)

section zero
variable (sa : ArrId) (n k : Word) (m : Mem)

theorem gzeroW_done (h : ¬ k < n) : gzeroW sa n k m = m := by
  rw [gzeroW]; simp [h]

theorem gzeroW_step (h : k < n) (hn : n < 9223372036854775808) :
    gzeroW sa n k m = gzeroW sa n (k + 8) ((((((((m.set64 sa k 0).set64 sa (k + 1) 0).set64 sa
      (k + 2) 0).set64 sa (k + 3) 0).set64 sa (k + 4) 0).set64 sa (k + 5) 0).set64 sa (k + 6) 0).set64
      sa (k + 7) 0) := by
  have : k.toNat + 8 < 2 ^ 64 := by
    have := UInt64.lt_iff_toNat_lt.mp h; have := UInt64.lt_iff_toNat_lt.mp hn
    have e : (9223372036854775808 : Word).toNat = 9223372036854775808 := rfl
    omega
  rw [gzeroW]; simp only [h, this, and_self, ↓reduceIte, zero8]

end zero

grind_pattern [arena_grind] gzeroW_done => gzeroW sa n k m
grind_pattern [arena_grind] gzeroW_step => gzeroW sa n k m

theorem zeroLoop_spec (p : Prog) (S : GrowSch) (o : Nat) (n : Nat) (s₀ : St)
    (hn : s₀.loc o < 9223372036854775808) :
    ⦃fun s => s = s₀⦄
    exec p n (shiftS o (zeroLoopB S))
    ⦃fun r s' => r = .normal ∧ KeepLo o s₀ s' ∧ s'.loc o = s₀.loc o ∧
      s'.mem = gzeroW S.sa (s₀.loc o) (s₀.loc (o + 1)) s₀.mem; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := shiftS o (zeroLoopB S)) rfl]
  simp only [shiftS, shiftC, shiftE]
  simp only [Nat.add_comm _ o, Nat.add_zero]
  vcgen [step, evalE, evalC, setLoc, ld64, st64, ih]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval, decide_eq_true_eq,
    Nat.left_eq_add, Nat.reduceEqDiff, ite_true, ite_false] at *)
  all_goals grind [lang_grind, arena_grind, KeepLo]

theorem zeroLoop_step_spec (p : Prog) (S : GrowSch) (o : Nat) (n : Nat) (s₀ : St)
    (hn : s₀.loc o < 9223372036854775808) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (shiftS o (zeroLoopB S))
    ⦃fun r s' => r = .normal ∧ KeepLo o s₀ s' ∧ s'.loc o = s₀.loc o ∧
      s'.mem = gzeroW S.sa (s₀.loc o) (s₀.loc (o + 1)) s₀.mem; ⊤⦄ :=
  Triple.step_exec (zeroLoop_spec p S o (n + 1) s₀ hn)

/-- A halved word is below `2^63` (the zero loop's bound). -/
theorem shr1_lt (x : Word) : x >>> 1 < 9223372036854775808 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_shiftRight]
  have := x.toNat_lt
  have e : (9223372036854775808 : Word).toNat = 9223372036854775808 := rfl
  simp only [e]; simp; omega

theorem growM_ok (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (m : Mem)
    (h : ¬ (m.len64 sa - 1) >>> 1 < gnW sa m * 2) :
    growM sa ca H m = gtiersW sa ca H (gnW sa m * 2) 0
      (gzeroW sa (gnW sa m * 2) 0 (m.set64 sa (m.len64 sa - 1) (gexpW sa m + 1))) := by
  rw [growM]; simp only [h, ↓reduceIte]

grind_pattern [arena_grind] growM_ok => growM sa ca H m

/-- **The growth block spliced at `o`**: it keeps the variables below `o`, completes normally, and
leaves `growM`'s memory. -/
theorem growBlkG_spec (p : Prog) (S : GrowSch) (sa : ArrId) (ca : Word) (hsa : S.sa = sa)
    (hca : S.ca = ca) (o : Nat) (H : Mem → Word → Word → Word) (hH : HashOK p S o H) (n : Nat)
    (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (growBlkG S o)
    ⦃fun r s' => r = .normal ∧ KeepLo o s₀ s' ∧ growM sa ca H s₀.mem = some s'.mem; ⊤⦄ := by
  subst hsa hca
  unfold growBlkG
  simp only [growB, L.Notation.blk, shiftS, shiftC, shiftE]
  simp only [Nat.add_comm _ o, Nat.add_zero]
  vcgen [step, evalE, evalC, setLoc, ld64, st64, zeroLoop_step_spec p S o n,
    tierLoop_step_spec p S o H hH n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval, decide_eq_true_eq,
    Nat.left_eq_add, Nat.reduceEqDiff, ite_true, ite_false] at *)
  all_goals grind [lang_grind, arena_grind, KeepLo, gnW, gexpW, shr1_lt]

end L.Arena
