module

public import ConAgua.Compiler.Abi
public import ConAgua.Compiler.Step
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

end

end L.Compiler
