import ConAgua.Arena.IndPartsSpec.MemberNames
import ConAgua.Arena.PinsNatOp
import ConAgua.Scan.Common

/-!
# EqW

`eqW`, `eqW_len`, `eqW_nil`, `eqW_ne`, `eqW_next`, `slEq_spec` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `sl_eq` -/

/-- The model of `sl_eq`. -/
def eqW : Nat → Mem → Word → Word → Word → Word → Option Word
  | 0, _, _, _, _, _ => none
  | n + 1, m, o1, l1, o2, l2 =>
    if l1 ≠ l2 then some 0
    else if l1 = 0 then some 1
    else if rdW (m.arr64 IW) o1 ≠ rdW (m.arr64 IW) o2 then some 0
    else eqW n m (o1 + 1) (l1 - 1) (o2 + 1) (l2 - 1)

section arms
variable (n : Nat) (m : Mem) (o1 l1 o2 l2 : Word)
theorem eqW_len (h : l1 ≠ l2) : eqW (n + 1) m o1 l1 o2 l2 = some 0 := by simp [eqW, h]
theorem eqW_nil (h : l1 = l2) (h0 : l1 = 0) : eqW (n + 1) m o1 l1 o2 l2 = some 1 := by
  subst h; simp [eqW, h0]
theorem eqW_ne (h : l1 = l2) (h0 : l1 ≠ 0) (hx : rdW (m.arr64 IW) o1 ≠ rdW (m.arr64 IW) o2) :
    eqW (n + 1) m o1 l1 o2 l2 = some 0 := by subst h; simp [eqW, h0, hx]
theorem eqW_next (h : l1 = l2) (h0 : l1 ≠ 0) (hx : rdW (m.arr64 IW) o1 = rdW (m.arr64 IW) o2) :
    eqW (n + 1) m o1 l1 o2 l2 = eqW n m (o1 + 1) (l1 - 1) (o2 + 1) (l2 - 1) := by
  subst h; simp [eqW, h0, hx]
end arms

grind_pattern [ind_grind] eqW_len => eqW (n + 1) m o1 l1 o2 l2
grind_pattern [ind_grind] eqW_nil => eqW (n + 1) m o1 l1 o2 l2
grind_pattern [ind_grind] eqW_ne => eqW (n + 1) m o1 l1 o2 l2
grind_pattern [ind_grind] eqW_next => eqW (n + 1) m o1 l1 o2 l2

section specs
variable (p : Prog) (hp : p.lookup "sl_eq" = some slEq)
include hp

theorem slEq_spec (n : Nat) : ∀ (s₀ : St) (o1 l1 o2 l2 : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "sl_eq" [o1, l1, o2, l2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ eqW n s₀.mem o1 l1 o2 l2 = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o1 l1 o2 l2; rw [invoke_eq _ hp]; simp only [callFn, slEq]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o1 l1 o2 l2
    rw [invoke_eq _ hp]
    simp only [callFn, slEq]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20) [rdW_eq, LocEq]

end specs

theorem slR_length {m : Mem} {o l : Word} {ws : List Word} (h : SlR m o l ws) :
    ws.length = l.toNat := by
  induction h with
  | nil => rfl
  | @cons o l ws hl _ ih =>
    have : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
    have e : (l - 1).toNat = l.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
    simp only [List.length_cons, ih, e]; omega

theorem eqW_ok (n : Nat) : ∀ (m : Mem) (o1 l1 o2 l2 r : Word) (ws1 ws2 : List Word),
    SlR m o1 l1 ws1 → SlR m o2 l2 ws2 → eqW n m o1 l1 o2 l2 = some r →
    r = if ws1 = ws2 then 1 else 0 := by
  induction n with
  | zero => intro m o1 l1 o2 l2 r ws1 ws2 _ _ h; simp [eqW] at h
  | succ n ih =>
    intro m o1 l1 o2 l2 r ws1 ws2 h1 h2 h
    cases h1 with
    | nil =>
      cases h2 with
      | nil => rw [eqW_nil n m o1 0 o2 0 rfl rfl] at h; simp at h; simp [h]
      | cons hl2 _ =>
        rw [eqW_len n m o1 0 o2 _ (Ne.symm hl2)] at h; simp at h; simp [← h]
    | @cons _ _ ws1' hl1 hs1 =>
      cases h2 with
      | nil =>
        rw [eqW_len n m o1 _ o2 0 hl1] at h; simp at h; simp [← h]
      | @cons _ _ ws2' hl2 hs2 =>
        by_cases hll : l1 = l2
        · by_cases hx : rdW (m.arr64 IW) o1 = rdW (m.arr64 IW) o2
          · rw [eqW_next n m o1 l1 o2 l2 hll hl1 hx] at h
            have := ih m _ _ _ _ r ws1' ws2' hs1 hs2 h
            rw [this, hx]
            simp
          · rw [eqW_ne n m o1 l1 o2 l2 hll hl1 hx] at h
            simp at h; subst h
            simp [hx]
        · rw [eqW_len n m o1 l1 o2 l2 hll] at h
          simp at h; subst h
          have e1 := slR_length (SlR.cons hl1 hs1)
          have e2 := slR_length (SlR.cons hl2 hs2)
          have hne : ¬ (rdW (m.arr64 IW) o1 :: ws1' = rdW (m.arr64 IW) o2 :: ws2') := by
            intro heq; rw [heq] at e1; apply hll
            exact UInt64.toNat_inj.mp (by rw [← e1, e2])
          simp [hne]

/-! ## `block_rec_lps_ok` -/

/-- The model of `block_rec_lps_one` (its callees run at `n - 1`). -/
def lpsOneW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, rc, wo, wl =>
    loK1 n wo wl (erToIwW n m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) rc + 1))
      (rdW (m.arr64 EREC) (rdW (m.arr64 IW) rc + 2)))
where
  loK1 (n : Nat) (wo wl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (rp, m1) => loK2 m1 (eqW n m1 (rp.headD 0) (rp.getD 1 0) wo wl)
  loK2 (m1 : Mem) : Option Word → Option (List Word × Mem)
    | none => none
    | some e => some ([e], m1)

section armsO
variable (n : Nat) (m m1 : Mem) (rc wo wl : Word) (rp : List Word) (e : Word)
theorem lpsOneW_step : lpsOneW (n + 1) m rc wo wl = lpsOneW.loK1 n wo wl
    (erToIwW n m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) rc + 1))
      (rdW (m.arr64 EREC) (rdW (m.arr64 IW) rc + 2))) := by simp [lpsOneW]
theorem loK1_some : lpsOneW.loK1 n wo wl (some (rp, m1)) =
    lpsOneW.loK2 m1 (eqW n m1 (rp.headD 0) (rp.getD 1 0) wo wl) := by simp [lpsOneW.loK1]
theorem loK2_some : lpsOneW.loK2 m1 (some e) = some ([e], m1) := by simp [lpsOneW.loK2]
end armsO

grind_pattern [ind_grind] lpsOneW_step => lpsOneW (n + 1) m rc wo wl
grind_pattern [ind_grind] loK1_some => lpsOneW.loK1 n wo wl (some (rp, m1))
grind_pattern [ind_grind] loK2_some => lpsOneW.loK2 m1 (some e)

mutual
/-- **The model of `block_rec_lps_ok_go`.** -/
def lpsGoW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, ro, rl, wo, wl =>
    if rl = 0 then some ([1], m)
    else lgK1 n ro rl wo wl (lpsOneW n m (rdW (m.arr64 IW) ro) wo wl)

/-- After `block_rec_lps_one`. -/
def lgK1 (n : Nat) (ro rl wo wl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0], m1) else lgK3 (lpsGoW n m1 (ro + 1) (rl - 1) wo wl)

/-- After the recursive call. -/
def lgK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0], m2)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (ro rl wo wl : Word) (r1 r : List Word)
theorem lpsGoW_nil (h : rl = 0) : lpsGoW (n + 1) m ro rl wo wl = some ([1], m) := by simp [lpsGoW, h]
theorem lpsGoW_cons (h : rl ≠ 0) : lpsGoW (n + 1) m ro rl wo wl = lgK1 n ro rl wo wl
    (lpsOneW n m (rdW (m.arr64 IW) ro) wo wl) := by simp [lpsGoW, h]
theorem lgK1_zero (h : r1.headD 0 = 0) : lgK1 n ro rl wo wl (some (r1, m1)) = some ([0], m1) := by
  simp only [lgK1]; rw [ite_eq_left h]
theorem lgK1_ne (h : r1.headD 0 ≠ 0) :
    lgK1 n ro rl wo wl (some (r1, m1)) = lgK3 (lpsGoW n m1 (ro + 1) (rl - 1) wo wl) := by
  simp only [lgK1]; rw [ite_eq_right h]
theorem lgK3_some : lgK3 (some (r, m2)) = some ([r.headD 0], m2) := by simp [lgK3]
end arms

grind_pattern [ind_grind] lpsGoW_nil => lpsGoW (n + 1) m ro rl wo wl
grind_pattern [ind_grind] lpsGoW_cons => lpsGoW (n + 1) m ro rl wo wl
grind_pattern [ind_grind] lgK1_zero => lgK1 n ro rl wo wl (some (r1, m1))
grind_pattern [ind_grind] lgK1_ne => lgK1 n ro rl wo wl (some (r1, m1))
grind_pattern [ind_grind] lgK3_some => lgK3 (some (r, m2))

theorem lpsW_two {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : lpsW n m p = some (r, m')) : r = [r.headD 0, r.getD 1 0] := by
  cases n with
  | zero => simp [lpsW] at h
  | succ n =>
    by_cases hz : rdW (m.arr64 IW) (p + 1) = 0
    · rw [lpsW_nil n m p hz] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h; rfl
    · rw [lpsW_cons n m p hz] at h
      have := erToIwW_two h
      simpa using this

theorem blockShapeLps_spec2 (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw)
    (hp : p.lookup "block_shape_lps" = some blockShapeLps) (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_shape_lps" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ lpsW n s₀.mem q = some (r, s'.mem) ∧ r = [r.headD 0, r.getD 1 0]; ⊤⦄ :=
  triple_post (blockShapeLps_spec p ha hc he hp n s₀ q) (fun _r _s' ⟨h1, h2⟩ => ⟨h1, h2, lpsW_two h2⟩)

mutual
/-- **The model of `block_rec_lps_ok`.** -/
def lokW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, p => lokK1 n p (lpsW n m p)

/-- After `block_shape_lps`. -/
def lokK1 (n : Nat) (p : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (lr, m1) =>
    if rdW (m1.arr64 IW) (p + 7) ≠ 0 then
      lokK2 n p (consW n m1 (rdW (m1.arr64 IW) (p + 5)) (lr.headD 0) (lr.getD 1 0))
    else lokK3 (lpsGoW n m1 (rdW (m1.arr64 IW) (p + 2)) (rdW (m1.arr64 IW) (p + 3))
      (lr.headD 0) (lr.getD 1 0))

/-- After `sl_cons`. -/
def lokK2 (n : Nat) (p : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (cr, m2) => lokK3 (lpsGoW n m2 (rdW (m2.arr64 IW) (p + 2)) (rdW (m2.arr64 IW) (p + 3))
      (cr.headD 0) (cr.getD 1 0))

/-- After the recursor loop. -/
def lokK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([r.headD 0], m3)
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (p : Word) (lr cr r : List Word)
theorem lokW_step : lokW (n + 1) m p = lokK1 n p (lpsW n m p) := by simp [lokW]
theorem lokK1_large (h : rdW (m1.arr64 IW) (p + 7) ≠ 0) : lokK1 n p (some (lr, m1)) =
    lokK2 n p (consW n m1 (rdW (m1.arr64 IW) (p + 5)) (lr.headD 0) (lr.getD 1 0)) := by
  simp only [lokK1]; rw [ite_eq_left h]
theorem lokK1_small (h : rdW (m1.arr64 IW) (p + 7) = 0) : lokK1 n p (some (lr, m1)) =
    lokK3 (lpsGoW n m1 (rdW (m1.arr64 IW) (p + 2)) (rdW (m1.arr64 IW) (p + 3))
      (lr.headD 0) (lr.getD 1 0)) := by
  simp only [lokK1]; rw [ite_eq_right (by simpa using h)]
theorem lokK2_some : lokK2 n p (some (cr, m2)) =
    lokK3 (lpsGoW n m2 (rdW (m2.arr64 IW) (p + 2)) (rdW (m2.arr64 IW) (p + 3))
      (cr.headD 0) (cr.getD 1 0)) := by simp [lokK2]
theorem lokK3_some : lokK3 (some (r, m3)) = some ([r.headD 0], m3) := by simp [lokK3]
end arms

grind_pattern [ind_grind] lokW_step => lokW (n + 1) m p
grind_pattern [ind_grind] lokK1_large => lokK1 n p (some (lr, m1))
grind_pattern [ind_grind] lokK1_small => lokK1 n p (some (lr, m1))
grind_pattern [ind_grind] lokK2_some => lokK2 n p (some (cr, m2))
grind_pattern [ind_grind] lokK3_some => lokK3 (some (r, m3))

theorem getD1 (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  cases r with
  | nil => rfl
  | cons a as => cases as <;> rfl

theorem map_decI_beq (ws1 ws2 : List Word) (h1 : ∀ w ∈ ws1, w.toNat < 2 ^ 32)
    (h2 : ∀ w ∈ ws2, w.toNat < 2 ^ 32) :
    ((ws1.map (decI : Word → NIdx)) == ws2.map decI) = decide (ws1 = ws2) := by
  induction ws1 generalizing ws2 with
  | nil => cases ws2 <;> simp
  | cons a as ih =>
    cases ws2 with
    | nil => simp
    | cons b bs =>
      simp only [List.map_cons, List.cons_beq_cons]
      rw [L.Arena.decI_beq a b (h1 a (List.mem_cons_self ..)) (h2 b (List.mem_cons_self ..)),
        ih bs (fun w hw => h1 w (List.mem_cons_of_mem _ hw)) (fun w hw => h2 w (List.mem_cons_of_mem _ hw))]
      by_cases hab : a = b <;> by_cases hbs : as = bs <;> simp [hab, hbs]

end L.Ind

end
