import ConAgua.Arena.RomLevel
import ConAgua.Arena.Env
import ConAgua.Front.ApplyExprRefine
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Layout

/-!
# The ROM's universe-argument lists: `rom_levels(pos)` refines `internLevels`

`internLevels us` interns the levels in order (`internLevelList`) and then the list node
(`internLsNode`), which in L takes the handles as a pool slice. A parameter's name writes its
bytes to the pool top between two levels, so the handles go to a **stack** first: the word array
`RSTK` (138), top `CTL[131]` (a ROM interner's scratch; nothing else reads it). Then
`stk_pool(b, k)` copies them to the pool top and `intern_ls` interns the slice; the stack is
popped back to its base.

* `encLevels us`: the count (8 bytes), then each level.
* `stk_push(h)`, `rom_lvls_go(q, k)` (`k` levels from `q`, pushed), `stk_pool(b, k)`,
  `rom_levels(pos)`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Rom

open L.Arena

/-- Its top, `CTL[131]`. -/
def stkTop (m : Mem) : Word := rdW (m.arr64 CTL) 131

/-! ## The encoding -/

/-- The levels one after the other. -/
def encLevelList : List ConLeche.Level → List UInt8
  | [] => []
  | u :: us => encLevel u ++ encLevelList us

/-- A universe-argument list: its length, then the levels. -/
def encLevels (us : List ConLeche.Level) : List UInt8 := u64B us.length ++ encLevelList us

/-! ## `stk_push(h)` -/

/-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values) -/
def stkPush : FunDecl := lfn (h) locals (o) {
  o := CTL.u64[131];
  if len(RSTK.u64) <= o { abort };
  RSTK.u64[o] := h;
  CTL.u64[131] := o + 1;
  return 0
}

/-- The memory after pushing `h`. -/
def pushMem (m : Mem) (h : Word) : Mem := (m.set64 RSTK (stkTop m) h).set64 CTL 131 (stkTop m + 1)

theorem stkPush_spec (p : Prog) (hp : p.lookup "stk_push" = some stkPush) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "stk_push" [h]
    ⦃fun _ s' => LocEq s' s₀ ∧ (stkTop s₀.mem).toNat < (s₀.mem.arr64 RSTK).size ∧
      s'.mem = pushMem s₀.mem h; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, stkPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
      finish [pushMem, stkTop]

/-! ## `rom_lvls_go(q, k)` -/

section go
variable (rom : List UInt8)

/-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values) -/
def romLvlsGo : FunDecl := lfn (q, k) locals (h, z, r) {
  if k == 0 { return q };
  (h, q) := call rom_level(q);
  z := call stk_push(h);
  r := call rom_lvls_go(q, k - 1);
  return r
}

mutual
/-- **The model of `rom_lvls_go`** at L fuel `n`: the position after, the memory after. -/
def romLvlsW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, q, k => if k = 0 then some (q, m) else lvlsK n k (romLevelW rom n m q)

/-- After one level. -/
def lvlsK (n : Nat) (k : Word) : Option (Word × Word × Mem) → Option (Word × Mem)
  | none => none
  | some (h, q', m₁) =>
    if (stkTop m₁).toNat < (m₁.arr64 RSTK).size then romLvlsW n (pushMem m₁ h) q' (k - 1) else none
end

theorem romLvlsW_zero (n : Nat) (m : Mem) (q : Word) : romLvlsW rom (n + 1) m q 0 = some (q, m) := by
  simp [romLvlsW]
theorem romLvlsW_succ (n : Nat) (m : Mem) (q k : Word) (hk : k ≠ 0) :
    romLvlsW rom (n + 1) m q k = lvlsK rom n k (romLevelW rom n m q) := by simp [romLvlsW, hk]
theorem lvlsK_some (n : Nat) (k h q' : Word) (m₁ : Mem) (hd : (stkTop m₁).toNat < (m₁.arr64 RSTK).size) :
    lvlsK rom n k (some (h, q', m₁)) = romLvlsW rom n (pushMem m₁ h) q' (k - 1) := by
  simp [lvlsK, hd]

end go

grind_pattern [arena_grind] romLvlsW_zero => romLvlsW rom (n + 1) m q 0
grind_pattern [arena_grind] romLvlsW_succ => romLvlsW rom (n + 1) m q k
grind_pattern [arena_grind] lvlsK_some => lvlsK rom n k (some (h, q', m₁))

/-! ## `stk_pool(b, k)`: stack words to the pool top -/

/-- The model of the copy loop: `RSTK[b + j ‥ b + k]` to `POOL⟨pt⟩[pb + j ‥ pb + k]`. -/
def sputW (m : Mem) (pt pb b k j : Word) : Mem :=
  if j < k then sputW (m.set64 (tierA 0 pt) (pb + j) (rdW (m.arr64 RSTK) (b + j))) pt pb b k (j + 1) else m
termination_by k.toNat - j.toNat
decreasing_by
  have : j.toNat < k.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹j < k›
  have := k.toNat_lt
  have : (j + 1).toNat = j.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

theorem sputW_end (m : Mem) (pt pb b k j : Word) (hj : ¬ j < k) : sputW m pt pb b k j = m := by
  rw [sputW]; simp only [hj, ↓reduceIte]

theorem sputW_step (m m' : Mem) (pt pb b k j j' : Word) (hj : j < k) (hj' : j' = j + 1)
    (hm' : m' = m.set64 (tierA 0 pt) (pb + j) (rdW (m.arr64 RSTK) (b + j))) :
    sputW m pt pb b k j = sputW m' pt pb b k j' := by
  subst hj' hm'
  rw [sputW]; simp only [hj, ↓reduceIte]

grind_pattern [arena_grind] sputW_end => sputW m pt pb b k j
grind_pattern [arena_grind] sputW_step => sputW m pt pb b k j, sputW m' pt pb b k j'

def sputLoop : Stmt := lblk (b, k, top, j, pt, pb) {
  while j < k {
    POOL⟨pt⟩[pb + j] := RSTK.u64[b + j];
    j += 1
  }
}

/-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values) -/
def stkPool : FunDecl := lfn (b, k) locals (top, j, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if len(POOL⟨pt⟩) < pb { abort };
  if len(POOL⟨pt⟩) - pb < k { abort };
  ⟪sputLoop⟫;
  CTL.u64[0] := top + k;
  return top
}

section sput
variable (p : Prog)

theorem sputLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n sputLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧
      s'.mem = sputW s₀.mem (s₀.loc 4) (s₀.loc 5) (s₀.loc 0) (s₀.loc 1) (s₀.loc 3); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := sputLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, st64, ih] <;> finish

theorem sputLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) sputLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧
      s'.mem = sputW s₀.mem (s₀.loc 4) (s₀.loc 5) (s₀.loc 0) (s₀.loc 1) (s₀.loc 3); ⊤⦄ :=
  Triple.step_exec (sputLoop_spec p (n + 1) s₀)

/-- `stk_pool`'s checks: room above the pool top. -/
def stkPoolOK (m : Mem) (k : Word) : Prop :=
  (m.top &&& (1099511627775 : Word)) ≤ m.len64 (tierA 0 (m.top >>> 40)) ∧
    k ≤ m.len64 (tierA 0 (m.top >>> 40)) - (m.top &&& 1099511627775)

theorem sputW_size (pt pb b k : Word) (a : ArrId) :
    ∀ (d : Nat) (m : Mem) (j : Word), k.toNat - j.toNat = d →
      ((sputW m pt pb b k j).arr64 a).size = (m.arr64 a).size := by
  intro d
  induction d with
  | zero =>
    intro m j hd
    have hjn : ¬ j < k := by rw [UInt64.lt_iff_toNat_lt]; omega
    rw [sputW_end _ _ _ _ _ _ hjn]
  | succ d ih =>
    intro m j hd
    have hjn : j < k := by rw [UInt64.lt_iff_toNat_lt]; omega
    have hjn' := UInt64.lt_iff_toNat_lt.mp hjn
    have := k.toNat_lt
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    rw [sputW]; simp only [hjn, ↓reduceIte]
    rw [ih _ _ (by omega), size_set64]

@[arena_grind =] theorem sputW_pcap (m : Mem) (pt pb b k j : Word) :
    pcap (sputW m pt pb b k j) = pcap m :=
  pcap_congr (sputW_size pt pb b k POOL _ m j rfl) (sputW_size pt pb b k POOL1 _ m j rfl)

theorem stkPoolOK_room (m : Mem) (k : Word) (h : stkPoolOK m k)
    (hs : (m.arr64 (tierA 0 (m.top >>> 40))).size < 2 ^ 63) :
    (m.top &&& 1099511627775).toNat + k.toNat ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size := by
  obtain ⟨h3, h4⟩ := h
  have hlen : (m.len64 (tierA 0 (m.top >>> 40))).toNat = (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    simp only [Mem.len64]; exact L.Front.toNat_ofNat_size _ hs
  have := UInt64.le_iff_toNat_le.mp h4
  have := UInt64.le_iff_toNat_le.mp h3
  rw [UInt64.toNat_sub_of_le _ _ h3, hlen] at *
  omega

grind_pattern [arena_grind] stkPoolOK_room => stkPoolOK m k, (m.arr64 (tierA 0 (m.top >>> 40))).size

/-- `stk_pool`'s checks bound the appended slice by the pool's capacity, for a top in a tier. -/
theorem stkPoolOK_cap (m : Mem) (k : Word) (h : stkPoolOK m k) (hc : pcap m < 2 ^ 64)
    (ht : m.top.toNat < 2 ^ 41) : m.top.toNat + k.toNat ≤ pcap m := by
  have hsz := pcap_tier m (m.top >>> 40) hc
  have hsplit := tag_split m.top
  have htier := tag_tier_le m.top ht
  have hroom := stkPoolOK_room m k h (by omega)
  rw [pcap_eq m hc]
  omega
grind_pattern [arena_grind] stkPoolOK_cap => stkPoolOK m k, pcap m

theorem stkPool_specW (hp : p.lookup "stk_pool" = some stkPool) (n : Nat) (s₀ : St) (b k : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "stk_pool" [b, k]
    ⦃fun r s' => LocEq s' s₀ ∧ stkPoolOK s₀.mem k ∧ r = [s₀.mem.top] ∧
      s'.mem = (sputW s₀.mem (s₀.mem.top >>> 40) (s₀.mem.top &&& 1099511627775) b k 0).set64 CTL 0 (s₀.mem.top + k) ∧
      (s'.mem.arr64 POOL).size = (s₀.mem.arr64 POOL).size; ⊤⦄ := by
  have hsz := fun m pt pb => sputW_size pt pb b k POOL _ m 0 rfl
  rw [invoke_eq _ hp]
  simp only [callFn, stkPool]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64, sputLoop_step_spec p n] <;>
      finish [stkPoolOK]

end sput

instance (m : Mem) (k : Word) : Decidable (stkPoolOK m k) := by unfold stkPoolOK; infer_instance

/-! ## `rom_levels(pos)` -/

section lv
variable (rom : List UInt8)

/-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values) -/
def romLevels : FunDecl := lfn (pos) locals (k, b, q, o, h) {
  k := call rom_u64(pos);
  if k >= 1152921504606846976 { abort };
  b := CTL.u64[131];
  q := call rom_lvls_go(pos + 8, k);
  o := call stk_pool(b, k);
  CTL.u64[131] := b;
  h := call intern_ls(o, k);
  if h >= 4294967296 { abort };
  return (h, q)
}

/-- After the list node. -/
def lsK (q : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (h, m') => if 4294967296 ≤ h then none else some (h, q, m')

/-- After the levels: copy, pop, intern. -/
def lvsK (b k : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (q, m₁) =>
    if stkPoolOK m₁ k then
      lsK q (lsinternW (((sputW m₁ (m₁.top >>> 40) (m₁.top &&& 1099511627775) b k 0).set64 CTL 0 (m₁.top + k)).set64 CTL 131 b) m₁.top k)
    else none

/-- **The model of `rom_levels`** at L fuel `n` (the count inside the ROM and below `2^60`). -/
def romLevelsW : Nat → Mem → Word → Option (Word × Word × Mem)
  | 0, _, _ => none
  | n + 1, m, pos =>
    if ¬ u64OK rom pos then none
    else if 1152921504606846976 ≤ u64W rom pos then none
    else lvsK (stkTop m) (u64W rom pos) (romLvlsW rom n m (pos + 8) (u64W rom pos))

end lv

theorem lsK_some (q h : Word) (m : Mem) (hh : ¬ 4294967296 ≤ h) : lsK q (some (h, m)) = some (h, q, m) := by
  simp [lsK, hh]
theorem lvsK_some (b k q : Word) (m₁ : Mem) (hok : stkPoolOK m₁ k) :
    lvsK b k (some (q, m₁)) =
      lsK q (lsinternW (((sputW m₁ (m₁.top >>> 40) (m₁.top &&& 1099511627775) b k 0).set64 CTL 0 (m₁.top + k)).set64 CTL 131 b) m₁.top k) := by
  simp only [lvsK]; rw [ite_eq_left hok]
theorem romLevelsW_eq (rom : List UInt8) (n : Nat) (m : Mem) (pos : Word)
    (hu : u64OK rom pos) (hk : ¬ 1152921504606846976 ≤ u64W rom pos) :
    romLevelsW rom (n + 1) m pos = lvsK (stkTop m) (u64W rom pos) (romLvlsW rom n m (pos + 8) (u64W rom pos)) := by
  simp only [romLevelsW, hu, hk, ite_false, not_true_eq_false]

attribute [arena_grind =] lsK_some
grind_pattern [arena_grind] romLevelsW_eq => romLevelsW rom (n + 1) m pos
grind_pattern [arena_grind] lvsK_some => lvsK b k (some (q, m₁)), stkPoolOK m₁ k

/-! ## The models keep the top in a tier -/

@[arena_grind =] theorem pushMem_mtop (m : Mem) (h : Word) : (pushMem m h).top = m.top := by
  simp only [pushMem]
  rw [top_set64_ne _ _ _ (by decide)]
  simp only [Mem.top, Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ RSTK by decide)]

@[arena_grind =] theorem pushMem_pcap (m : Mem) (h : Word) : pcap (pushMem m h) = pcap m := by
  simp only [pushMem, pcap_set64]

theorem flag_set64_ctl (m : Mem) (c v : Word) (hc : c.toNat ≠ 1) : (m.set64 CTL c v).flag = m.flag := by
  have e : (m.set64 CTL c v).arr64 CTL = (m.arr64 CTL).set! c.toNat v := Mem.arr64_set64_same _ _ _ _
  simp only [Mem.flag, e, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [hc]

theorem setCtl_topK (m : Mem) (c v : Word) (h0 : c.toNat ≠ 0 := by decide) (h1 : c.toNat ≠ 1 := by decide) :
    TopK m (m.set64 CTL c v) :=
  TopK.of_eq (top_set64_ne _ _ _ h0) (pcap_set64 _ _ _ _) (flag_set64_ctl _ _ _ h1)

theorem pushMem_topK (m : Mem) (h : Word) : TopK m (pushMem m h) := by
  simp only [pushMem]
  exact (TopK.of_eq (top_set64_arr _ _ _ _ (by decide)) (pcap_set64 _ _ _ _)
    (Mem.flag_set64_ne _ _ _ _ (by decide))).trans (setCtl_topK _ _ _)

theorem sputW_arr (pt pb b0 k : Word) (b : ArrId) (hb : b ≠ POOL ∧ b ≠ POOL1) :
    ∀ (d : Nat) (m : Mem) (j : Word), k.toNat - j.toNat = d →
      (sputW m pt pb b0 k j).arr64 b = m.arr64 b := by
  intro d
  induction d with
  | zero =>
    intro m j hd
    have hjn : ¬ j < k := by rw [UInt64.lt_iff_toNat_lt]; omega
    rw [sputW_end _ _ _ _ _ _ hjn]
  | succ d ih =>
    intro m j hd
    have hjn : j < k := by rw [UInt64.lt_iff_toNat_lt]; omega
    have hjn' := UInt64.lt_iff_toNat_lt.mp hjn
    have := k.toNat_lt
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    rw [sputW]; simp only [hjn, ↓reduceIte]
    rw [ih _ _ (by omega), arr64_set64_tier_ne _ _ _ _ _ hb]

/-- **`stk_pool`'s memory keeps the top in its tier**, the capacity and the mode. -/
theorem stkPool_topK {m : Mem} {b k : Word} (hok : stkPoolOK m k) :
    TopK m ((sputW m (m.top >>> 40) (m.top &&& 1099511627775) b k 0).set64 CTL 0 (m.top + k)) := by
  intro hc ht
  have hsz := pcap_tier m (m.top >>> 40) hc
  have hsplit := tag_split m.top
  have htier := tag_tier_le m.top ht
  have hroom := stkPoolOK_room m k hok (by omega)
  have hT : (m.top + k).toNat = m.top.toNat + k.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hctl : (sputW m (m.top >>> 40) (m.top &&& 1099511627775) b k 0).arr64 CTL = m.arr64 CTL :=
    sputW_arr _ _ _ _ CTL ⟨by decide, by decide⟩ _ m 0 rfl
  have hflag : ((sputW m (m.top >>> 40) (m.top &&& 1099511627775) b k 0).set64 CTL 0 (m.top + k)).flag
      = m.flag := by rw [Mem.flag_set64_top]; simp only [Mem.flag, hctl]
  have htop0 : (sputW m (m.top >>> 40) (m.top &&& 1099511627775) b k 0).top = m.top :=
    congrArg (fun a : Array Word => a[0]?.getD 0) hctl
  refine ⟨?_, by rw [pcap_set64, sputW_pcap], fun hm => ?_⟩
  · rcases top_set64_cases (sputW m (m.top >>> 40) (m.top &&& 1099511627775) b k 0) (m.top + k) with e | e
    · rw [e, hT]; omega
    · rw [e, htop0]; exact ht
  · rcases hm with hf | h0
    · exact .inl (by rw [hflag]; exact hf)
    · right
      rcases top_set64_cases (sputW m (m.top >>> 40) (m.top &&& 1099511627775) b k 0) (m.top + k) with e | e
      · rw [e, hT]; omega
      · rw [e, htop0]; exact h0

theorem romLvlsW_top (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (q k q' : Word) (m' : Mem),
    romLvlsW rom n m q k = some (q', m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m q k q' m' hW; simp [romLvlsW] at hW
  | succ n ih =>
    intro m q k q' m' hW
    by_cases hk : k = 0
    · subst hk
      rw [romLvlsW_zero] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW
      exact TopK.refl _
    rw [romLvlsW_succ rom n m q k hk] at hW
    cases hP : romLevelW rom n m q with
    | none => rw [hP] at hW; simp [lvlsK] at hW
    | some r =>
      obtain ⟨h, q₁, m₁⟩ := r
      rw [hP] at hW
      by_cases hd : (stkTop m₁).toNat < (m₁.arr64 RSTK).size
      · rw [lvlsK_some rom n k h q₁ m₁ hd] at hW
        exact ((romLevelW_topK hP).trans (pushMem_topK m₁ h)).trans (ih _ _ _ _ _ hW)
      · simp [lvlsK, hd] at hW

theorem romLvlsW_topK {rom : List UInt8} {n : Nat} {m : Mem} {q k q' : Word} {m' : Mem}
    (hW : romLvlsW rom n m q k = some (q', m')) : TopK m m' := romLvlsW_top rom n m q k q' m' hW

theorem romLvlsW_top' (rom : List UInt8) (n : Nat) (m : Mem) (q k q' : Word) (m' : Mem)
    (hW : romLvlsW rom n m q k = some (q', m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romLvlsW_top rom n m q k q' m' hW hc ht).1
grind_pattern [arena_grind] romLvlsW_top' => romLvlsW rom n m q k, some (q', m')

theorem romLevelsW_top (rom : List UInt8) (n : Nat) (m : Mem) (pos h q : Word) (m' : Mem)
    (hW : romLevelsW rom n m pos = some (h, q, m')) : TopK m m' := by
  cases n with
  | zero => simp [romLevelsW] at hW
  | succ n =>
    by_cases hu : u64OK rom pos
    case neg => simp [romLevelsW, hu] at hW
    by_cases hk : 1152921504606846976 ≤ u64W rom pos
    case pos => simp [romLevelsW, hu, hk] at hW
    rw [romLevelsW_eq rom n m pos hu hk] at hW
    cases hP : romLvlsW rom n m (pos + 8) (u64W rom pos) with
    | none => rw [hP] at hW; simp [lvsK] at hW
    | some r =>
      obtain ⟨q₁, m₁⟩ := r
      rw [hP] at hW
      by_cases hok : stkPoolOK m₁ (u64W rom pos)
      case neg => simp [lvsK, hok] at hW
      rw [lvsK_some _ _ _ _ hok] at hW
      cases hI : lsinternW (((sputW m₁ (m₁.top >>> 40) (m₁.top &&& 1099511627775) (stkTop m)
          (u64W rom pos) 0).set64 CTL 0 (m₁.top + u64W rom pos)).set64 CTL 131 (stkTop m)) m₁.top
          (u64W rom pos) with
      | none => rw [hI] at hW; simp [lsK] at hW
      | some r =>
        obtain ⟨w, m₃⟩ := r
        rw [hI] at hW
        simp only [lsK] at hW
        split at hW
        · simp at hW
        simp only [Option.some.injEq, Prod.mk.injEq] at hW
        obtain ⟨-, -, rfl⟩ := hW
        exact (((romLvlsW_topK hP).trans (stkPool_topK hok)).trans (setCtl_topK _ _ _)).trans
          (cons_topK lsCS_wf (by decide) (by decide) hI)

theorem romLevelsW_topK {rom : List UInt8} {n : Nat} {m : Mem} {pos h q : Word} {m' : Mem}
    (hW : romLevelsW rom n m pos = some (h, q, m')) : TopK m m' := romLevelsW_top rom n m pos h q m' hW

theorem romLevelsW_top' (rom : List UInt8) (n : Nat) (m : Mem) (pos h q : Word) (m' : Mem)
    (hW : romLevelsW rom n m pos = some (h, q, m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romLevelsW_top rom n m pos h q m' hW hc ht).1
grind_pattern [arena_grind] romLevelsW_top' => romLevelsW rom n m pos, some (h, q, m')

/-- The functions `rom_levels` calls. -/
structure LevelsProg (rom : List UInt8) (p : Prog) : Prop extends LevelProg rom p where
  stk_push : p.lookup "stk_push" = some stkPush
  rom_lvls_go : p.lookup "rom_lvls_go" = some romLvlsGo
  stk_pool : p.lookup "stk_pool" = some stkPool
  ls_match : p.lookup "ls_match" = some lsMatch
  ls_find : p.lookup "ls_find" = some lsFind
  ls_push : p.lookup "ls_push" = some lsPush
  intern_ls : p.lookup "intern_ls" = some internLs
  rom_levels : p.lookup "rom_levels" = some romLevels

end L.Rom

namespace L.Rom

open L.Arena

section spec
variable (rom : List UInt8) (p : Prog) (hL : LevelsProg rom p)
include hL

theorem romLvlsGo_specW (n : Nat) : ∀ (s₀ : St) (q k : Word),
    pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41 →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_lvls_go" [q, k]
    ⦃fun r s' => LocEq s' s₀ ∧ romLvlsW rom n s₀.mem q k = some (r.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ q k _
    rw [invoke_eq _ hL.rom_lvls_go]; simp only [callFn, romLvlsGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ q k hs
    have ih' := fun s₁ q₁ k₁ h₁ => Triple.keep hL.no_st8 (ih s₁ q₁ k₁ h₁)
    have hl' := fun s₁ q₁ h₁ => Triple.keep hL.no_st8 (romLevel_specW rom p hL.toLevelProg n s₁ q₁ h₁)
    have hp' := fun s₁ h₁ => Triple.keep hL.no_st8 (stkPush_spec p hL.stk_push n s₁ h₁)
    rw [invoke_eq _ hL.rom_lvls_go]
    simp only [callFn, romLvlsGo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hl', hp', ih'] <;>
      finish [Keep.size, Keep.pcap]

theorem romLevels_specW (n : Nat) (s₀ : St) (pos : Word)
    (hs : pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_levels" [pos]
    ⦃fun r s' => LocEq s' s₀ ∧ romLevelsW rom n s₀.mem pos = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.rom_levels]
  simp only [callFn, romLevels]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hg := fun s₁ q₁ k₁ h₁ => Triple.keep hL.no_st8 (romLvlsGo_specW rom p hL n s₁ q₁ k₁ h₁)
    have hq := fun s₁ b k => Triple.keep hL.no_st8 (stkPool_specW p hL.stk_pool n s₁ b k)
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, hg, hq,
        romU64_spec rom p hL.rom_u64 n,
        internLs_spec p hL.lit_hash hL.limbs_eq hL.ls_match hL.ls_find hL.ls_push hL.intern_ls n] <;>
      finish [Keep.size, Keep.pcap, stkTop]

end spec

end L.Rom

namespace L.Rom

open L.Arena

/-! ## The pure side -/

/-- The ROM interner's frame: the store tier and the stack. -/
def RomA : List ArrId := RSTK :: StoreA
def RomC : List Word := 131 :: StoreC

theorem frame_romA {m m' : Mem} (h : MemFrame StoreA StoreC m m') : MemFrame RomA RomC m m' :=
  h.mono (fun _b hb => List.mem_cons_of_mem _ hb) (fun _x hx => List.mem_cons_of_mem _ hx)

theorem pushMem_frame1 (m : Mem) (h : Word) : MemFrame [RSTK] [131] m (pushMem m h) := by
  simp only [pushMem]
  exact ((MemFrame.set64 _ RSTK (by decide) _ _).mono (by simp) (by simp)).trans
    ((MemFrame.setCtl _ 131 _).mono (by simp) (by simp))

theorem pushMem_frame (m : Mem) (h : Word) : MemFrame RomA RomC m (pushMem m h) :=
  (pushMem_frame1 m h).mono (by simp [RomA]) (by simp [RomC])

theorem pushMem_top (m : Mem) (h : Word) (hc : 131 < (m.arr64 CTL).size) :
    stkTop (pushMem m h) = stkTop m + 1 := by
  simp only [stkTop, pushMem, Mem.arr64_set64_same, rdW_set!,
    Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ RSTK by decide)]
  simp [hc]

theorem pushMem_stk (m : Mem) (h x : Word) (hx : (stkTop m).toNat < (m.arr64 RSTK).size) :
    rdW ((pushMem m h).arr64 RSTK) x = if x = stkTop m then h else rdW (m.arr64 RSTK) x := by
  simp only [pushMem, Mem.arr64_set64_ne _ _ _ _ _ (show RSTK ≠ CTL by decide), Mem.arr64_set64_same,
    rdW_set!]
  by_cases e : x = stkTop m
  · subst e; simp [hx]
  · have : ¬ (stkTop m).toNat = x.toNat := fun h' => e (UInt64.toNat_inj.mp h'.symm)
    simp [e, this]

theorem sputW_facts (pt pb b n : Word) (hv : b.toNat + n.toNat < 2 ^ 64) (ht : pt.toNat ≤ 1) :
    ∀ (d : Nat) (m : Mem) (j : Word), n.toNat - j.toNat = d → j ≤ n →
      pb.toNat + n.toNat ≤ (m.arr64 (tierA 0 pt)).size → (m.arr64 (tierA 0 pt)).size ≤ 2 ^ 40 →
      PFrame m (sputW m pt pb b n j) ∧
      ∀ x, (vpool (sputW m pt pb b n j))[x]? =
        if pt.toNat * 2 ^ 40 + pb.toNat + j.toNat ≤ x ∧ x < pt.toNat * 2 ^ 40 + pb.toNat + n.toNat then
          some (rdW (m.arr64 RSTK) (b + UInt64.ofNat (x - (pt.toNat * 2 ^ 40 + pb.toNat))))
        else (vpool m)[x]? := by
  intro d
  induction d with
  | zero =>
    intro m j hd hj _ _
    have hjn : ¬ j < n := by rw [UInt64.lt_iff_toNat_lt]; omega
    rw [sputW_end _ _ _ _ _ _ hjn]
    refine ⟨PFrame.refl _, fun x => ?_⟩
    have : ¬ (pt.toNat * 2 ^ 40 + pb.toNat + j.toNat ≤ x ∧
        x < pt.toNat * 2 ^ 40 + pb.toNat + n.toNat) := by
      have := UInt64.le_iff_toNat_le.mp hj; omega
    simp [this]
  | succ d ih =>
    intro m j hd hj hp hs
    have hjn : j < n := by rw [UInt64.lt_iff_toNat_lt]; omega
    have hjn' := UInt64.lt_iff_toNat_lt.mp hjn
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hpj : (pb + j).toNat = pb.toNat + j.toNat := by rw [UInt64.toNat_add]; simp; omega
    rw [sputW]; simp only [hjn, ↓reduceIte]
    have hRS : (m.set64 (tierA 0 pt) (pb + j) (rdW (m.arr64 RSTK) (b + j))).arr64 RSTK = m.arr64 RSTK :=
      arr64_set64_tier_ne _ _ _ _ _ ⟨by decide, by decide⟩
    have hsz : ((m.set64 (tierA 0 pt) (pb + j) (rdW (m.arr64 RSTK) (b + j))).arr64 (tierA 0 pt)).size =
        (m.arr64 (tierA 0 pt)).size := size_set64 _ _ _ _ _
    obtain ⟨hf, hx⟩ := ih (m.set64 (tierA 0 pt) (pb + j) (rdW (m.arr64 RSTK) (b + j))) (j + 1) (by omega)
      (UInt64.le_iff_toNat_le.mpr (by omega)) (by omega) (by omega)
    refine ⟨PFrame.trans (PFrame.set64 _ _ _ (PFrame.refl _)) hf, fun x => ?_⟩
    rw [hx, hRS, vpool_set64t m pt (pb + j) _ ht (by omega) hs, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds]
    simp only [hpj, hj1, vpool_size]
    by_cases h1 : pt.toNat * 2 ^ 40 + pb.toNat + (j.toNat + 1) ≤ x ∧
        x < pt.toNat * 2 ^ 40 + pb.toNat + n.toNat
    · have h2 : pt.toNat * 2 ^ 40 + (pb.toNat + j.toNat) ≠ x := by omega
      simp [h1, show pt.toNat * 2 ^ 40 + pb.toNat + j.toNat ≤ x by omega]
    · by_cases h2 : pt.toNat * 2 ^ 40 + (pb.toNat + j.toNat) = x
      · subst h2
        have e : pt.toNat * 2 ^ 40 + (pb.toNat + j.toNat) - (pt.toNat * 2 ^ 40 + pb.toNat) = j.toNat := by
          omega
        simp [show pt.toNat * 2 ^ 40 + (pb.toNat + j.toNat) < 2 ^ 41 by omega, e]
        try omega
      · have : ¬ (pt.toNat * 2 ^ 40 + pb.toNat + j.toNat ≤ x ∧
            x < pt.toNat * 2 ^ 40 + pb.toNat + n.toNat) := by omega
        simp [h1, h2, this]

/-- **`stk_pool`'s memory**: the pool grew by the stack words `[b, b + k)`, at the old top. -/
theorem stkPoolW_facts (m : Mem) (b k : Word) (hpool : PoolOK m) (hok : stkPoolOK m k)
    (hbk : b.toNat + k.toNat < 2 ^ 63) :
    Grows m ((sputW m (m.top >>> 40) (m.top &&& 1099511627775) b k 0).set64 CTL 0 (m.top + k)) ∧
    SliceOK ((sputW m (m.top >>> 40) (m.top &&& 1099511627775) b k 0).set64 CTL 0 (m.top + k)) m.top k ∧
    sliceL (vpool ((sputW m (m.top >>> 40) (m.top &&& 1099511627775) b k 0).set64 CTL 0 (m.top + k)))
      m.top.toNat k.toNat =
      (List.range k.toNat).map (fun j => rdW (m.arr64 RSTK) (b + UInt64.ofNat j)) := by
  have hsm := hpool.small
  have h41 := hpool.top41
  have hsz := hsm.tier (m.top >>> 40)
  have hsplit := tag_split m.top
  have htier := tag_tier_le m.top h41
  have hctl0 : 0 < (m.arr64 CTL).size := hpool.2.1
  have hroom := stkPoolOK_room m k hok (by omega)
  obtain ⟨hf, hx⟩ := sputW_facts (m.top >>> 40) (m.top &&& 1099511627775) b k (by omega) htier
    _ m 0 rfl (UInt64.le_iff_toNat_le.mpr (by simp)) (by omega) (by omega)
  simp only [UInt64.toNat_zero, Nat.add_zero, hsplit] at hx
  have hctl : 0 < ((sputW m (m.top >>> 40) (m.top &&& 1099511627775) b k 0).arr64 CTL).size := by
    rw [hf.ctl]; exact hctl0
  have htop' := Mem.top_set64 _ (m.top + k) hctl
  have hg := Grows.write m _ k hpool hf (fun x hxt => by rw [hx, ite_eq_right (by omega)]) (by omega)
  refine ⟨hg, SliceOK.fresh hg htop', ?_⟩
  rw [vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩, sliceL, List.ext_getElem_iff]
  refine ⟨by simp, fun j hk₁ hk₂ => ?_⟩
  simp only [List.length_ofFn] at hk₁
  simp only [List.getElem_ofFn, hx, List.getElem_map, List.getElem_range]
  simp [show m.top.toNat + j < m.top.toNat + k.toNat by omega]

theorem not_mem_storeC (c : Word) (hc : 64 ≤ c.toNat) : c ∉ StoreC := by
  simp only [StoreC, List.mem_map, List.mem_range, not_exists, not_and]
  intro x hx h
  have := congrArg UInt64.toNat h
  rw [UInt64.toNat_ofNat'] at this
  omega

section ref
variable (rom : List UInt8) (hr : RomOK rom)
include hr

set_option linter.constructorNameAsVariable false in
/-- **`rom_lvls_go` refines `internLevelList`**, the handles pushed on the stack in order. -/
theorem romLvlsW_ok (us : List ConLeche.Level) (hus : us.all levelFits = true) :
    ∀ (n : Nat) (m : Mem) (a : AState) (q : Word) (rest : List UInt8) (k r : Word) (m' : Mem),
    ArenaD m a → ModeOK m → rom.drop q.toNat = encLevelList us ++ rest → k.toNat = us.length →
    (stkTop m).toNat + us.length < 2 ^ 63 → 131 < (m.arr64 CTL).size →
    romLvlsW rom n m q k = some (r, m') →
    AM.ok (internLevelList us) a ∧ ArenaD m' (AM.st (internLevelList us) a) ∧
    r.toNat = q.toNat + (encLevelList us).length ∧ MemFrame RomA RomC m m' ∧
    stkTop m' = stkTop m + UInt64.ofNat us.length ∧
    lsWords (AM.res (internLevelList us) a) =
      (List.range us.length).map (fun j => rdW (m'.arr64 RSTK) (stkTop m + UInt64.ofNat j)) ∧
    (∀ i : Word, i.toNat < (stkTop m).toNat → rdW (m'.arr64 RSTK) i = rdW (m.arr64 RSTK) i) := by
  induction us with
  | nil =>
    intro n m a q rest k r m' hA hmo hd hk ht hc hW
    have hk0 : k = 0 := by simp at hk; exact UInt64.toNat_inj.mp (by simpa using hk)
    subst hk0
    cases n with
    | zero => simp [romLvlsW] at hW
    | succ n =>
    rw [romLvlsW_zero] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    exact ⟨trivial, hA, by simp [encLevelList], MemFrame.refl _ _ _, by simp, by simp [lsWords]; rfl,
      fun _ _ => rfl⟩
  | cons x xs ih =>
    intro n m a q rest k r m' hA hmo hd hk ht hc hW
    simp only [List.all_cons, Bool.and_eq_true] at hus
    have hk0 : k ≠ 0 := by intro h; subst h; simp at hk
    cases n with
    | zero => simp [romLvlsW] at hW
    | succ n =>
    rw [romLvlsW_succ rom n m q k hk0] at hW
    have hd' : rom.drop q.toNat = encLevel x ++ (encLevelList xs ++ rest) := by
      rw [hd, encLevelList, List.append_assoc]
    cases hN : romLevelW rom n m q with
    | none => rw [hN] at hW; simp [lvlsK] at hW
    | some t =>
    obtain ⟨h₁, q₁, m₁⟩ := t
    rw [hN] at hW
    obtain ⟨ok1, hR1, res1, hlt1, hq1, hf1⟩ := romLevelW_ok rom hr x hus.1 n m a q _ h₁ q₁ m₁ hA hmo hd' hN
    simp only [lvlsK] at hW
    split at hW
    case isFalse => simp at hW
    rename_i hdlt
    have hR2 : ArenaD (pushMem m₁ h₁) (AM.st (internLevel x) a) :=
      ArenaD.frameHi (pushMem_frame1 m₁ h₁) (by simp [RSTK]) (by simp) hR1
    have ht1 : stkTop m₁ = stkTop m := hf1.2.1 131 (not_mem_storeC _ (by decide))
    have hc1 : 131 < (m₁.arr64 CTL).size := by rw [hf1.2.2.1]; exact hc
    have hS1 : m₁.arr64 RSTK = m.arr64 RSTK := hf1.1 RSTK (by decide) (by decide)
    have hdq : rom.drop q₁.toNat = encLevelList xs ++ rest :=
      drop_shift rom hr q (encLevel x) (encLevelList xs) rest (by rw [hd', List.append_assoc]) q₁ hq1
    have hk1 : (k - 1).toNat = xs.length := by
      have : 1 ≤ k.toNat := by simp at hk; omega
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using this))]
      simp at hk ⊢; omega
    have htp : stkTop (pushMem m₁ h₁) = stkTop m + 1 := by rw [pushMem_top _ _ hc1, ht1]
    have htN : (stkTop m + 1).toNat = (stkTop m).toNat + 1 := by
      rw [UInt64.toNat_add]; simp at ht ⊢; omega
    obtain ⟨ok2, hR3, hr2, hf3, htop2, hws2, hkeep2⟩ := ih hus.2 n _ _ q₁ rest (k - 1) r m' hR2
      (((romLevelW_topK hN).trans (pushMem_topK m₁ h₁)).mode hA.1.lit.1 hmo) hdq hk1
      (by rw [htp, htN]; simp at ht; omega) (by rw [(pushMem_frame1 m₁ h₁).2.2.1]; exact hc1) hW
    rw [htp] at htop2 hws2 hkeep2
    have hX : internLevelList (x :: xs) =
        internLevel x >>= fun h => internLevelList xs >>= fun hs => pure (h :: hs) := rfl
    have okX : AM.ok (internLevelList (x :: xs)) a := by
      rw [hX, AM.ok_bind, AM.ok_bind]; exact ⟨ok1, ok2, trivial⟩
    have hok1 : AM.ok (internLevelList xs >>= fun hs => pure (AM.res (internLevel x) a :: hs))
        (AM.st (internLevel x) a) := by rw [AM.ok_bind]; exact ⟨ok2, trivial⟩
    have hst : AM.st (internLevelList (x :: xs)) a = AM.st (internLevelList xs) (AM.st (internLevel x) a) := by
      rw [hX, AM.st_bind _ _ _ (hX ▸ okX), AM.st_bind _ _ _ hok1]; rfl
    have hres : AM.res (internLevelList (x :: xs)) a =
        AM.res (internLevel x) a :: AM.res (internLevelList xs) (AM.st (internLevel x) a) := by
      rw [hX, AM.res_bind _ _ _ ok1, AM.res_bind _ _ _ ok2]; rfl
    have hlt : (stkTop m).toNat < (m₁.arr64 RSTK).size := by rw [← ht1]; exact hdlt
    have h0 : rdW (m'.arr64 RSTK) (stkTop m) = h₁ := by
      rw [hkeep2 _ (by rw [htN]; omega), pushMem_stk _ _ _ (by rw [ht1]; exact hlt), ht1]; simp
    refine ⟨okX, hst ▸ hR3, ?_, (frame_romA hf1).trans ((pushMem_frame m₁ h₁).trans hf3), ?_, ?_, ?_⟩
    · rw [hr2, hq1]; simp [encLevelList]; omega
    · rw [htop2]; apply UInt64.toNat_inj.mp
      simp only [List.length_cons, UInt64.toNat_add, UInt64.toNat_ofNat']; simp at ht ⊢; omega
    · rw [hres]
      simp only [lsWords, List.map_cons, List.length_cons, List.range_succ_eq_map, List.map_map]
      refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
      · rw [res1, decI_word_self _ hlt1]; simpa using h0.symm
      · have := hws2; simp only [lsWords] at this; rw [this]
        apply List.map_congr_left; intro j _
        simp only [Function.comp]
        congr 1
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add]
        simp; omega
    · intro i hi
      rw [hkeep2 i (by rw [htN]; omega), pushMem_stk _ _ _ (by rw [ht1]; exact hlt), ht1, hS1]
      have : i ≠ stkTop m := fun e => by subst e; omega
      simp [this]

set_option linter.constructorNameAsVariable false in
/-- **The model of `rom_levels` refines `internLevels`**: the stack is back at its base. -/
theorem romLevelsW_ok (us : List ConLeche.Level) (hus : us.all levelFits = true) (n : Nat) (m : Mem)
    (a : AState) (pos : Word) (rest : List UInt8) (h q : Word) (m' : Mem) (hA : ArenaD m a)
    (hmo : ModeOK m) (hd : rom.drop pos.toNat = encLevels us ++ rest) (ht : (stkTop m).toNat + us.length < 2 ^ 62)
    (hc : 131 < (m.arr64 CTL).size) (hW : romLevelsW rom n m pos = some (h, q, m')) :
    AM.ok (internLevels us) a ∧ ArenaD m' (AM.st (internLevels us) a) ∧
    AM.res (internLevels us) a = decI h ∧ h.toNat < 2 ^ 32 ∧
    q.toNat = pos.toNat + (encLevels us).length ∧ MemFrame RomA RomC m m' ∧ stkTop m' = stkTop m := by
  cases n with
  | zero => simp [romLevelsW] at hW
  | succ n =>
  have hlen := drop_len rom _ _ _ hd (by simp [encLevels, u64B])
  simp only [encLevels, u64B, List.length_append, List.length_cons, List.length_nil] at hlen
  simp only [RomOK] at hr
  have hd0 : rom.drop pos.toNat = u64B us.length ++ (encLevelList us ++ rest) := by
    rw [hd, encLevels, List.append_assoc]
  have hl : u64W rom pos = UInt64.ofNat us.length := u64W_of_drop rom pos _ _ hd0 (by omega) hr
  have hp8 : (pos + 8).toNat = pos.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have hu : u64OK rom pos := u64OK_of_drop rom _ _ _ hd0 hr
  by_cases hk : 1152921504606846976 ≤ u64W rom pos
  · simp [romLevelsW, hu, hk] at hW
  rw [romLevelsW_eq rom n m pos hu hk] at hW
  have hd8 : rom.drop (pos + 8).toNat = encLevelList us ++ rest := by
    rw [hp8, ← List.drop_drop, hd0]; simp [u64B]
  have hkN : (UInt64.ofNat us.length).toNat = us.length := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  rw [hl] at hW
  cases hG : romLvlsW rom n m (pos + 8) (UInt64.ofNat us.length) with
  | none => rw [hG] at hW; simp [lvsK] at hW
  | some t =>
  obtain ⟨q₁, m₁⟩ := t
  rw [hG] at hW
  obtain ⟨ok1, hR1, hq1, hf1, htop1, hws1, -⟩ := romLvlsW_ok rom hr us hus n m a (pos + 8) rest _ q₁ m₁ hA hmo
    hd8 hkN (by omega) hc hG
  simp only [lvsK] at hW
  split at hW
  case isFalse => simp at hW
  rename_i hok
  have hB : (stkTop m).toNat + (UInt64.ofNat us.length).toNat < 2 ^ 63 := by rw [hkN]; omega
  obtain ⟨hg, hsl, hk⟩ := stkPoolW_facts m₁ (stkTop m) _ hR1.1.lit.1 hok hB
  have hR2 := ArenaD.grow _ _ hg _ hR1
  generalize hm₂ : (sputW m₁ (m₁.top >>> 40) (m₁.top &&& 1099511627775) (stkTop m) (UInt64.ofNat us.length) 0).set64 CTL 0
    (m₁.top + UInt64.ofNat us.length) = m₂ at hg hsl hk hR2 hW
  have hf3 : MemFrame [] [131] m₂ (m₂.set64 CTL 131 (stkTop m)) := MemFrame.setCtl _ _ _
  have hR3 := ArenaD.frameHi hf3 (by simp) (by simp) hR2
  have hsl3 : SliceOK (m₂.set64 CTL 131 (stkTop m)) m₁.top (UInt64.ofNat us.length) := by
    have : (m₂.set64 CTL 131 (stkTop m)).top = m₂.top := by
      simp only [Mem.top, Mem.arr64_set64_same]; rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      simp
    exact (SliceOK_congr _ _ this (ptop0_congr (Mem.arr64_set64_ne _ _ _ _ _ (by decide)))).mpr hsl
  have hk3 : sliceL (vpool (m₂.set64 CTL 131 (stkTop m))) m₁.top.toNat (UInt64.ofNat us.length).toNat =
      lsWords (AM.res (internLevelList us) a) := by
    rw [vpool_set64_ne _ _ _ _ (by decide), hk, hws1, hkN]
  cases hI : lsinternW (m₂.set64 CTL 131 (stkTop m)) m₁.top (UInt64.ofNat us.length) with
  | none => rw [hI] at hW; simp [lsK] at hW
  | some t =>
  obtain ⟨w, m₄⟩ := t
  rw [hI] at hW
  simp only [lsK] at hW
  split at hW
  · simp at hW
  rename_i hlt
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl, rfl⟩ := hW
  have hmo3 : ModeOK (m₂.set64 CTL 131 (stkTop m)) := by
    rw [← hm₂]
    exact (((romLvlsW_topK hG).trans (stkPool_topK hok)).trans (setCtl_topK _ _ _)).mode hA.1.lit.1 hmo
  obtain ⟨ok2, hR4, res2, hf4⟩ := L.Front.internLs_D _ _ hR3 w m₄ _ _ hsl3 _ hk3 (ModeOK.slice0 hmo3 hsl3) hI
  obtain ⟨okX, stX, resX⟩ := AM.bind_facts _ internLsNode a ok1 ok2
  have e : internLevels us = internLevelList us >>= internLsNode := rfl
  have hf4' := frame_store hf4 (by simp [lsSch, LSREC, LSSLOT, LSHP]) (by simp [lsSch])
  refine ⟨e ▸ okX, by rw [e, stX]; exact hR4, by rw [e, resX]; exact res2,
    by simp at hlt; exact UInt64.lt_iff_toNat_lt.mp hlt, ?_, ?_, ?_⟩
  · rw [hq1, hp8]; simp [encLevels, u64B]; omega
  · refine hf1.trans (((frame_romA (frame_grows hg)).trans ?_).trans (frame_romA hf4'))
    exact hf3.mono (by simp) (by simp [RomC])
  · have : stkTop m₄ = stkTop (m₂.set64 CTL 131 (stkTop m)) := hf4'.2.1 131 (not_mem_storeC _ (by decide))
    rw [this]; simp only [stkTop, Mem.arr64_set64_same, rdW_set!]
    have hc2 : 131 < (m₂.arr64 CTL).size := by
      rw [(frame_grows hg).2.2.1, hf1.2.2.1]; exact hc
    simp [hc2]

end ref

/-- **`rom_lvls_go` refines `internLevelList`**: the handles pushed on `RSTK` in order. -/
@[refines ConRon.Arena.internLevelList]
theorem romLvlsGo_refines (rom : List UInt8) (p : Prog) (hL : LevelsProg rom p) (hr : RomOK rom)
    (us : List ConLeche.Level) (hus : us.all levelFits = true) (n : Nat) (s₀ : St) (a₀ : AState)
    (q k : Word) (rest : List UInt8) (hA : ArenaD s₀.mem a₀) (hmo : ModeOK s₀.mem)
    (hd : rom.drop q.toNat = encLevelList us ++ rest) (hk : k.toNat = us.length)
    (ht : (stkTop s₀.mem).toNat + us.length < 2 ^ 63) (hc : 131 < (s₀.mem.arr64 CTL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_lvls_go" [q, k]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLevelList us) a₀ ∧
      ArenaD s'.mem (AM.st (internLevelList us) a₀) ∧
      (r.headD 0).toNat = q.toNat + (encLevelList us).length ∧ MemFrame RomA RomC s₀.mem s'.mem ∧
      stkTop s'.mem = stkTop s₀.mem + UInt64.ofNat us.length ∧
      lsWords (AM.res (internLevelList us) a₀) =
        (List.range us.length).map (fun j => rdW (s'.mem.arr64 RSTK) (stkTop s₀.mem + UInt64.ofNat j)); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (romLvlsGo_specW rom p hL n s₀ q k ⟨hA.1.lit.1.2.2.1, hA.1.lit.1.top41⟩)
  subst hs
  obtain ⟨a1, a2, a3, a4, a5, a6, -⟩ := romLvlsW_ok rom hr us hus n _ a₀ q rest k _ _ hA hmo hd hk ht hc hW
  exact ⟨hloc, a1, a2, a3, a4, a5, a6⟩

/-- **`rom_levels` refines `internLevels`** at a position holding the list's encoding. -/
@[refines ConRon.Arena.internLevels]
theorem romLevels_refines (rom : List UInt8) (p : Prog) (hL : LevelsProg rom p) (hr : RomOK rom)
    (us : List ConLeche.Level) (hus : us.all levelFits = true) (n : Nat) (s₀ : St) (a₀ : AState)
    (pos : Word) (rest : List UInt8) (hA : ArenaD s₀.mem a₀) (hmo : ModeOK s₀.mem)
    (hd : rom.drop pos.toNat = encLevels us ++ rest) (ht : (stkTop s₀.mem).toNat + us.length < 2 ^ 62)
    (hc : 131 < (s₀.mem.arr64 CTL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_levels" [pos]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLevels us) a₀ ∧ ArenaD s'.mem (AM.st (internLevels us) a₀) ∧
      AM.res (internLevels us) a₀ = decI (r.headD 0) ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      (r.tail.headD 0).toNat = pos.toNat + (encLevels us).length ∧ MemFrame RomA RomC s₀.mem s'.mem ∧
      stkTop s'.mem = stkTop s₀.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (romLevels_specW rom p hL n s₀ pos ⟨hA.1.lit.1.2.2.1, hA.1.lit.1.top41⟩)
  subst hs
  exact ⟨hloc, romLevelsW_ok rom hr us hus n _ a₀ pos rest _ _ _ hA hmo hd ht hc hW⟩

end L.Rom
