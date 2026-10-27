module

public import ConAgua.L.Semantics

@[expose] public section

/-!
# Blocks: basic facts (lane blkcopy)

What `Mem.copy64`, `Mem.copy8w` and `scanN` leave alone, and how they unfold.
-/

namespace L

theorem Mem.copy64_bytes (m : Mem) (d : ArrId) (di : Word) (s : ArrId) (si : Word) (n : Nat) :
    (m.copy64 d di s si n).bytes = m.bytes := by
  induction n generalizing m di si with
  | zero => rfl
  | succ n ih => simp only [Mem.copy64, ih]; rfl

theorem Mem.copy64_glob (m : Mem) (d : ArrId) (di : Word) (s : ArrId) (si : Word) (n : Nat) :
    (m.copy64 d di s si n).glob = m.glob := by
  induction n generalizing m di si with
  | zero => rfl
  | succ n ih => simp only [Mem.copy64, ih]; rfl

theorem Mem.copy8w_bytes (m : Mem) (d : ArrId) (di : Word) (b : Array UInt8) (si : Word) (n : Nat) :
    (m.copy8w d di b si n).bytes = m.bytes := by
  induction n generalizing m di si with
  | zero => rfl
  | succ n ih => simp only [Mem.copy8w, ih]; rfl

theorem Mem.copy8w_glob (m : Mem) (d : ArrId) (di : Word) (b : Array UInt8) (si : Word) (n : Nat) :
    (m.copy8w d di b si n).glob = m.glob := by
  induction n generalizing m di si with
  | zero => rfl
  | succ n ih => simp only [Mem.copy8w, ih]; rfl

theorem Mem.copy64_arr8 (m : Mem) (d : ArrId) (di : Word) (s : ArrId) (si : Word) (n : Nat) (a : ArrId) :
    (m.copy64 d di s si n).arr8 a = m.arr8 a := by
  simp only [Mem.arr8, Mem.copy64_bytes]

theorem Mem.copy8w_arr8 (m : Mem) (d : ArrId) (di : Word) (b : Array UInt8) (si : Word) (n : Nat) (a : ArrId) :
    (m.copy8w d di b si n).arr8 a = m.arr8 a := by
  simp only [Mem.arr8, Mem.copy8w_bytes]

theorem Mem.copy64_zero (m : Mem) (d : ArrId) (di : Word) (s : ArrId) (si : Word) :
    m.copy64 d di s si 0 = m := rfl

theorem Mem.copy64_succ (m : Mem) (d : ArrId) (di : Word) (s : ArrId) (si : Word) (n : Nat) :
    m.copy64 d di s si (n + 1) = (m.set64 d di ((m.arr64 s)[si.toNat]!)).copy64 d (di + 1) s (si + 1) n := rfl

theorem Mem.copy8w_zero (m : Mem) (d : ArrId) (di : Word) (b : Array UInt8) (si : Word) :
    m.copy8w d di b si 0 = m := rfl

theorem Mem.copy8w_succ (m : Mem) (d : ArrId) (di : Word) (b : Array UInt8) (si : Word) (n : Nat) :
    m.copy8w d di b si (n + 1) = (m.set64 d di (b[si.toNat]!).toUInt64).copy8w d (di + 1) b (si + 1) n := rfl

theorem scanN_end (b : Array UInt8) (c : List UInt8) (i e : Nat) (h : ¬ i < e) : scanN b c i e = i := by
  rw [scanN]; simp [h]

theorem scanN_hit (b : Array UInt8) (c : List UInt8) (i e : Nat) (h : i < e) (hc : c[(b[i]!).toNat]! ≠ 0) :
    scanN b c i e = i := by
  rw [scanN]; rw [ite_eq_left h, ite_eq_left hc]

theorem scanN_miss (b : Array UInt8) (c : List UInt8) (i e : Nat) (h : i < e) (hc : c[(b[i]!).toNat]! = 0) :
    scanN b c i e = scanN b c (i + 1) e := by
  rw [scanN, ite_eq_left h]; simp [hc]

theorem scanN_le_end (b : Array UInt8) (c : List UInt8) : ∀ i e, i ≤ e → scanN b c i e ≤ e := by
  intro i e h
  induction i using scanN.induct b c e with
  | case1 i hi hc => rw [scanN_hit b c i e hi hc]; omega
  | case2 i hi hc ih => rw [scanN_miss b c i e hi (by simpa using hc)]; exact ih (by omega)
  | case3 i hi => rw [scanN_end b c i e hi]; omega

theorem scanN_ge (b : Array UInt8) (c : List UInt8) : ∀ i e, i ≤ scanN b c i e := by
  intro i e
  induction i using scanN.induct b c e with
  | case1 i hi hc => rw [scanN_hit b c i e hi hc]; omega
  | case2 i hi hc ih => rw [scanN_miss b c i e hi (by simpa using hc)]; omega
  | case3 i hi => rw [scanN_end b c i e hi]; omega

end L
