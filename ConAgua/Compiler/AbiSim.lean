module

public import ConAgua.Compiler.Abi
public import ConAgua.Compiler.Step
public import ConAgua.Compiler.Rel
import all Kraken.Mem

@[expose] public section

/-!
# The entry stub's stores, on the machine

`sim_stores`: the stub's body `storesCode d vs` writes word `i` of `vs` at `r8 + d + 8i` and
changes no register but `rax` (and the flags). The values (`SVal.val`) are read from the registers
at the start.
-/

namespace L.Compiler

/-- The byte `j` of a word store. -/
theorem get?_wrW_byte {d : DataMem} {x j : Nat} {v : BitVec 64} (hj : j < 8) :
    (wrW d (A x) v).get? (A (x + j)) = (UInt64.ofBitVec v).toBytes[j]? := by
  have hA : A (x + j) = A x + BitVec.ofNat 64 j := (A_add x j).symm
  rw [hA]
  simp only [wrW, _root_.Mem.storeInt, _root_.Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?]
  rw [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  have h := get?_At_idx (Int.toBytes 8 v.toInt) (A x) j (by omega) (by simp [Int.toBytes_length])
  simp only [Std.ExtHashMap.get?_eq_getElem?] at h
  rw [h]
  have : (Int.toBytes 8 v.toInt)[j]?.isSome := by simp [Int.toBytes_length, hj]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp this
  rw [hb]
  simp only [Option.some_or]
  rw [← hb]; rfl

/-- The word an `SVal` stands for, in registers `R`. -/
def SVal.val (R : Reg64s) : SVal → BitVec 64
  | .reg r => R.get64 r
  | .imm w => w.toBitVec
  | .addr off => off.toUInt64.toBitVec + R.get64 .r8

/-- The memory after the stores of `vs` from `[base + d]` on, with the values from `R`. -/
def stores (R : Reg64s) (base : Nat) : DataMem → Nat → List SVal → DataMem
  | m, _, [] => m
  | m, d, v :: vs => stores R base (wrW m (A (base + d)) (v.val R)) (d + 8) vs

/-- The registers `vs` reads are not `rax`. -/
def SVal.noRax : SVal → Prop
  | .reg r => r ≠ .rax
  | _ => True

theorem romVals_length : ∀ bs : List UInt8, (romVals bs).length = (bs.length + 7) / 8
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs => by
    simp only [romVals, List.length_cons, romVals_length bs]; omega
  | [] => rfl
  | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _] => by simp [romVals]

/-- What the stub needs of the table: two byte arrays, the table within the first `2^31` bytes
(the stores' displacements are 32-bit), and the region size below `2^64`. -/
def abiTabOk (tab : Tab) : Bool :=
  tab.nb == 2 && decide (16 + 16 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng ≤ 2 ^ 31) &&
    decide (abiNeed tab < 2 ^ 64)

theorem abiVals_length (tab : Tab) (h : tab.nb = 2) :
    (abiVals tab).length = 6 + 2 * tab.nw + tab.romWords := by
  simp only [abiVals, h, List.length_append, List.length_cons, List.length_nil, romVals_length,
    Tab.romWords, ← tab.romLen_eq]
  simp [List.length_flatMap, List.map_const']
  omega

theorem stores_only (R : Reg64s) (base : Nat) :
    ∀ (vs : List SVal) (m : DataMem) (d : Nat), base + d + 8 * vs.length ≤ 2 ^ 64 →
    Only (base + d) (base + d + 8 * vs.length) m (stores R base m d vs)
  | [], m, d, _ => by simpa [stores] using Only.refl _ _ m
  | v :: vs, m, d, h => by
    simp only [List.length_cons] at h
    simp only [stores, List.length_cons]
    exact Only.union (Only.wrW (by omega)) (stores_only R base vs _ (d + 8) (by omega))
      (by omega) (by omega) (by omega) (by omega)

theorem stores_rdW (R : Reg64s) (base : Nat) :
    ∀ (vs : List SVal) (m : DataMem) (d i : Nat) (hi : i < vs.length), base + d + 8 * vs.length ≤ 2 ^ 64 →
    rdW (stores R base m d vs) (A (base + d + 8 * i)) = some (UInt64.ofBitVec (vs[i].val R))
  | [], _, _, _, hi, _ => absurd hi (by simp)
  | v :: vs, m, d, i, hi, h => by
    simp only [List.length_cons] at h hi
    simp only [stores]
    cases i with
    | zero =>
      rw [(stores_only R base vs _ (d + 8) (by omega)).rdW_eq (by omega) (by omega)]
      simpa using rdW_wrW_same _ _ _
    | succ i =>
      have := stores_rdW R base vs (wrW m (A (base + d)) (v.val R)) (d + 8) i (by omega) (by omega)
      rw [show base + (d + 8) + 8 * i = base + d + 8 * (i + 1) by omega] at this
      simpa using this

theorem stores_byte (R : Reg64s) (base : Nat) :
    ∀ (vs : List SVal) (m : DataMem) (d i j : Nat) (hi : i < vs.length), j < 8 →
    base + d + 8 * vs.length ≤ 2 ^ 64 →
    (stores R base m d vs).get? (A (base + d + 8 * i + j)) = (UInt64.ofBitVec (vs[i].val R)).toBytes[j]?
  | [], _, _, _, _, hi, _, _ => absurd hi (by simp)
  | v :: vs, m, d, i, j, hi, hj, h => by
    simp only [List.length_cons] at h hi
    simp only [stores]
    cases i with
    | zero =>
      rw [(stores_only R base vs _ (d + 8) (by omega)).same _ (by omega) (by omega)]
      simpa using get?_wrW_byte hj
    | succ i =>
      have := stores_byte R base vs (wrW m (A (base + d)) (v.val R)) (d + 8) i j (by omega) hj (by omega)
      rw [show base + (d + 8) + 8 * i + j = base + d + 8 * (i + 1) + j by omega] at this
      simpa using this

section
variable [Host]

theorem sim_stores (Q : MachineState → Prop) (R : Reg64s) (base : Nat) (hb : R.r8.toNat = base) :
    ∀ (vs : List SVal) (d k : Nat) (s : MachineData), Code (storesCode d vs) k →
    (∀ r, r ≠ .rax → s.regs.get64 r = R.get64 r) → (∀ v ∈ vs, v.noRax) →
    d + 8 * vs.length ≤ 2 ^ 31 → base + d + 8 * vs.length ≤ 2 ^ 64 →
    (∀ j < 8 * vs.length, (s.dmem.get? (A (base + d + j))).isSome) →
    (∀ s', s'.dmem = stores R base s.dmem d vs → (∀ r, r ≠ .rax → s'.regs.get64 r = R.get64 r) →
      Ev Q s' (at_ (k + (storesCode d vs).length))) →
    Ev Q s (at_ k) := by
  intro vs
  induction vs with
  | nil =>
    intro d k s _ hR _ _ _ _ hK
    exact ev_congr (hK s rfl hR) (by simp [storesCode])
  | cons v vs ih =>
    intro d k s hc hR hno hd hend hmap hK
    simp only [List.length_cons] at hd hend hmap
    have hr8 : (s.regs.get64 .r8).toNat = base := by
      rw [hR .r8 (by decide)]; simpa using hb
    have hoff : SmallOff ((d : Nat) : Int) := ⟨by omega, by omega⟩
    have hcell : (rdW s.dmem (A (base + d))).isSome :=
      isSome_rdW fun j hj => by rw [A_add]; exact hmap j (by omega)
    have hmap' : ∀ (m : DataMem), (∀ y, (s.dmem.get? y).isSome → (m.get? y).isSome) →
        ∀ j < 8 * vs.length, (m.get? (A (base + (d + 8) + j))).isSome :=
      fun m hm j hj => hm _ (by rw [show base + (d + 8) + j = base + d + (8 + j) by omega]; exact hmap _ (by omega))
    simp only [storesCode, List.append_assoc] at hc
    have hrest := hc.right
    cases v with
    | reg r =>
      have hnr : r ≠ .rax := hno _ List.mem_cons_self
      simp only [SVal.code, List.length_cons, List.length_nil] at hrest hc
      refine ev_movMR hc.left.head hoff (by rw [hr8]; simpa using hcell) ?_
      refine ih (d + 8) (k + 1) _ hrest hR (fun v hv => hno v (List.mem_cons_of_mem _ hv)) (by omega) (by omega)
        (hmap' _ fun y hy => isSome_get?_storeInt hy) ?_
      intro s' hs' hR'
      refine ev_congr (hK s' ?_ hR') (by simp [storesCode, SVal.code]; omega)
      rw [hs']; simp only [stores, SVal.val, hr8, Int.toNat_natCast, hR r hnr]
    | imm w =>
      simp only [SVal.code, List.length_cons, List.length_nil] at hrest hc
      refine ev_movRI hc.left.head ?_
      refine ev_movMR hc.left.tail.head hoff ?_ ?_
      · simp only [Reg64s.set64_rax, Reg64s.get64_r8] at hr8 ⊢; rw [hr8]; simpa using hcell
      refine ih (d + 8) (k + 1 + 1) _ hrest ?_ (fun v hv => hno v (List.mem_cons_of_mem _ hv)) (by omega) (by omega)
        (hmap' _ fun y hy => isSome_get?_storeInt hy) ?_
      · intro r hr; rw [← hR r hr]; cases r <;> first | exact absurd rfl hr | rfl
      intro s' hs' hR'
      refine ev_congr (hK s' ?_ hR') (by simp [storesCode, SVal.code]; omega)
      rw [hs']; simp only [stores, SVal.val, Reg64s.set64_rax, Reg64s.get64_r8, Reg64s.get64_rax] at hr8 ⊢
      rw [hr8]; simp
    | addr off =>
      simp only [SVal.code, List.length_cons, List.length_nil] at hrest hc
      refine ev_movRI hc.left.head ?_
      refine ev_binO (op := .add) (o := oR .r8) rfl hc.left.tail.head
        (Or.inr (Or.inr ⟨.r8, rfl, rfl⟩)) ?_
      intro st
      refine ev_movMR hc.left.tail.tail.head hoff ?_ ?_
      · simp only [Reg64s.set64_rax, Reg64s.get64_r8] at hr8 ⊢; rw [hr8]; simpa using hcell
      refine ih (d + 8) (k + 1 + 1 + 1) _ hrest ?_ (fun v hv => hno v (List.mem_cons_of_mem _ hv)) (by omega) (by omega)
        (hmap' _ fun y hy => isSome_get?_storeInt hy) ?_
      · intro r hr; rw [← hR r hr]; cases r <;> first | exact absurd rfl hr | rfl
      intro s' hs' hR'
      refine ev_congr (hK s' ?_ hR') (by simp [storesCode, SVal.code]; omega)
      rw [hs']; simp only [stores, SVal.val, Reg64s.set64_rax, Reg64s.get64_r8, Reg64s.get64_rax] at hr8 ⊢
      have h8 := hR .r8 (by decide)
      simp only [Reg64s.get64_r8] at h8
      rw [hr8]; simp [BinOp.eval, h8]

theorem abiTabOk_spec {tab : Tab} (h : abiTabOk tab = true) :
    tab.nb = 2 ∧ 16 + 16 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng ≤ 2 ^ 31 ∧
      abiNeed tab < 2 ^ 64 := by
  simpa [abiTabOk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

theorem abiVals_noRax (tab : Tab) : ∀ v ∈ abiVals tab, v.noRax := by
  intro v hv
  simp only [abiVals, List.mem_append, List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false] at hv
  have hrom : ∀ bs : List UInt8, ∀ v ∈ romVals bs, v.noRax := by
    intro bs
    induction bs using romVals.induct with
    | case1 _ _ _ _ _ _ _ _ _ ih =>
      intro v hv; simp only [romVals, List.mem_cons] at hv
      rcases hv with rfl | hv
      · trivial
      · exact ih v hv
    | case2 => intro v hv; simp [romVals] at hv
    | case3 bs h1 h2 =>
      intro v hv
      rw [romVals.eq_3 bs h1 h2] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      subst hv; trivial
  rcases hv with ((((h | h | h | h) | h) | h) | h) | h
  · subst h; trivial
  · subst h; trivial
  · subst h; simp [SVal.noRax]
  · subst h; simp [SVal.noRax]
  · split at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp [SVal.noRax]
    · simp at h
  · obtain ⟨a, _, h | h⟩ := h <;> subst h <;> trivial
  · obtain ⟨a, _, h | h⟩ := h <;> subst h <;> trivial
  · exact hrom _ v h

/-- **The stub.** From `ca_start`, with the region's first table words mapped: if `base_len`
(`r9`) is below `abiNeed`, the stub returns with `rdx = 1`; otherwise it writes the table's words
(`stores … (abiVals tab)`) and jumps to `ca_enter` with `rdi = base`, `rsi = abiFuel`, the other
registers but `rax` unchanged. -/
theorem sim_abiStub (tab : Tab) (hok : abiTabOk tab = true) (k0 : Nat) (hc : Code (abiStub tab) k0)
    (Q : MachineState → Prop) (s : MachineData) (ra : Word)
    (hmap : ∀ j < 8 * (abiVals tab).length, (s.dmem.get? (A (s.regs.r8.toNat + j))).isSome)
    (hend : s.regs.r8.toNat + 8 * (abiVals tab).length ≤ 2 ^ 64)
    (hra : rdW s.dmem s.regs.rsp.toBitVec = some ra)
    (hdec : ∀ st : MachineState, st.pc = Int64.ofBitVec ra.toBitVec → st.data.regs.rdx = 1 → Q st)
    (hgo : abiNeed tab ≤ s.regs.r9.toNat → ∀ s' : MachineData,
      s'.dmem = stores s.regs s.regs.r8.toNat s.dmem 0 (abiVals tab) →
      s'.regs.rdi = s.regs.r8 → s'.regs.rsi.toNat = abiFuel →
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → s'.regs.get64 r = s.regs.get64 r) →
      Ev Q s' (label enterL)) :
    Ev Q s (label abiStartL) := by
  obtain ⟨hnb, htab, hneed⟩ := abiTabOk_spec hok
  have hlen := abiVals_length tab hnb
  have hcH := hc.left.left
  have hcS := hc.left.right
  have hcT := hc.right
  simp only [abiHead] at hcH
  simp only [abiTail] at hcT
  rw [Code.label (i := 0) hcH rfl]
  refine ev_label (Code.get (i := 0) hcH rfl) ?_
  refine ev_movRI (Code.get (i := 1) hcH rfl) ?_
  refine ev_cmpRO (r := .r9) (o := oR .rax) (v := (abiNeed tab).toUInt64) (Code.get (i := 2) hcH rfl)
    (Or.inr (Or.inr ⟨.rax, rfl, rfl⟩)) ?_
  refine ev_jcc (Code.get (i := 3) hcH rfl) (fun hlt => ?_) (fun hge => ?_)
  · -- declined
    simp only [CondCode.interp, cmpFlags_cf, decide_eq_true_eq, Reg64s.get64_r9, Reg64s.set64_rax,
      UInt64.toNat_toBitVec] at hlt
    rw [Code.label (i := 3) hcT rfl]
    refine ev_label (Code.get (i := 3) hcT rfl) ?_
    refine ev_movRI (Code.get (i := 4) hcT rfl) ?_
    refine ev_movRI (Code.get (i := 5) hcT rfl) ?_
    refine ev_ret (Code.get (i := 6) hcT rfl) (ra := ra)
      (by simpa [Reg64s.set64_rax, Reg64s.set64_rdx] using hra) ?_
    exact Eventually.done _ (hdec _ rfl (by simp [Reg64s.set64_rax, Reg64s.set64_rdx, Reg64s.set64_rsp]))
  · simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not, Reg64s.get64_r9, Reg64s.set64_rax,
      UInt64.toNat_toBitVec, Nat.not_lt] at hge
    have hge' : abiNeed tab ≤ s.regs.r9.toNat := by
      simpa [Nat.toUInt64, UInt64.toNat_ofNat, Nat.mod_eq_of_lt hneed] using hge
    refine sim_stores Q s.regs s.regs.r8.toNat rfl (abiVals tab) 0 _ _ hcS ?_ (abiVals_noRax tab)
      (by omega) (by simpa using hend) (by simpa using hmap) ?_
    · intro r hr; cases r <;> first | exact absurd rfl hr | rfl
    intro s1 hs1 hR1
    have hk : k0 + 0 + 1 + 1 + 1 + 1 + (storesCode 0 (abiVals tab)).length =
        k0 + (abiHead tab ++ storesCode 0 (abiVals tab)).length := by simp [abiHead]; omega
    rw [hk]
    refine ev_movRR (Code.get (i := 0) hcT rfl) ?_
    refine ev_movRI (Code.get (i := 1) hcT rfl) ?_
    refine ev_jmp (Code.get (i := 2) hcT rfl) ?_
    refine hgo hge' _ (by simpa using hs1) ?_ ?_ ?_
    · have := hR1 .r8 (by decide); simp at this
      simp [Reg64s.set64_rdi, Reg64s.set64_rsi, this]
    · simp [Reg64s.set64_rdi, Reg64s.set64_rsi, abiFuel]; rfl
    · intro r h1 h2 h3
      rw [← hR1 r h1]
      cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | rfl

end

end L.Compiler
