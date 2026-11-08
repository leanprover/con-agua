module

import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.Env
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndCopy2
public import ConAgua.Arena.IndParts
import all ConAgua.Arena.IndParts

@[expose] public section

/-!
# MemberNames: `ConRon.Arena.BlockParts.complete`, `ConRon.Arena.BlockShape.lps`, `ConRon.Arena.BlockShape.memberNames`

The refinement theorems `blockShapeMemberNames_refines`, `blockPartsComplete_refines`, `blockShapeLps_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A handle slice whose words decode one by one decodes as the list. -/
theorem decHL_of_get {k : IdxKind} (m : Mem) : ∀ (xs : List (Idx k)) (o : Nat),
    (∀ j (hj : j < xs.length), iwH m (o + j) = some xs[j]) → decHL m o xs.length = some xs
  | [], o, _ => by simp [decHL, hslice?]
  | x :: xs, o, h => by
    have h0 : iwH m o = some x := h 0 (by simp)
    have ih := decHL_of_get m xs (o + 1) (fun j hj => by
      have := h (j + 1) (by simpa using hj)
      have e : o + (j + 1) = o + 1 + j := by omega
      simpa [e] using this)
    show hslice? (iwA m) o (xs.length + 1) = _
    rw [hslice?_succ]
    have ih' : hslice? (iwA m) (o + 1) xs.length = some xs := ih
    have h0' : hd? (iwA m) o = some x := h0
    simp [h0', ih']

/-- The model of `member_names_copy`. -/
def nameCopyW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, d, s, l =>
    if l = 0 then some m
    else nameCopyW n
      (m.set64 IW d (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) s)))) (d + 1) (s + 1) (l - 1)

section arms
variable (n : Nat) (m : Mem) (d s l : Word)
theorem nameCopyW_nil (hl : l = 0) : nameCopyW (n + 1) m d s l = some m := by
  simp [nameCopyW, hl]
theorem nameCopyW_step (hl : l ≠ 0) :
    nameCopyW (n + 1) m d s l =
      nameCopyW n (m.set64 IW d (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) s))))
        (d + 1) (s + 1) (l - 1) := by
  simp [nameCopyW, hl]
end arms

grind_pattern [ind_grind] nameCopyW_nil => nameCopyW (n + 1) m d s l
grind_pattern [ind_grind] nameCopyW_step => nameCopyW (n + 1) m d s l

theorem memberNamesCopy_spec (p : Prog) (hp : p.lookup "member_names_copy" = some memberNamesCopy)
    (n : Nat) :
    ∀ (s₀ : St) (d s l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "member_names_copy" [d, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ nameCopyW n s₀.mem d s l = some s'.mem; ⊤⦄ := by
  sorry

/-- **What `member_names_copy` leaves.** -/
theorem nameCopyW_get (n : Nat) : ∀ (m m' : Mem) (d s l : Word), nameCopyW n m d s l = some m' →
    s.toNat + l.toNat ≤ d.toNat → d.toNat + l.toNat ≤ (m.arr64 IW).size →
    (m.arr64 IW).size < 2 ^ 64 →
    (∀ j < l.toNat, (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + j))).toNat < d.toNat) →
    (∀ b : TieredArray, b ≠ ↑IW → m'.arr64 b = m.arr64 b) ∧ (m'.arr64 IW).size = (m.arr64 IW).size ∧
    ∀ i, (m'.arr64 IW)[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + l.toNat
      then some (rdW (m.arr64 EREC)
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + (i - d.toNat))))))
      else (m.arr64 IW)[i]? :=
  ipCopyW_get nameCopyW (fun m x => rdW (m.arr64 EREC) (rdW (m.arr64 IW) x)) (fun x d => x.toNat < d)
    (fun _ _ _ _ => by simp [nameCopyW]) (nameCopyW_nil · · · · ·) (nameCopyW_step · · · · ·)
    (fun m d v x hx => by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), rdW_set64_IW_ne m d v x (by omega)])
    (fun _ _ h => by omega) n

/-- The model of `block_shape_member_names`. -/
def memberNamesW (n : Nat) (m : Mem) (p : Word) : Option (List Word × Mem) :=
  match allocW m (rdW (m.arr64 IW) (p + 1)) with
  | none => none
  | some (q, m1) =>
    match nameCopyW (n - 1) m1 q (rdW (m.arr64 IW) p) (rdW (m.arr64 IW) (p + 1)) with
    | none => none
    | some m2 => some ([q, rdW (m.arr64 IW) (p + 1)], m2)

theorem blockShapeMemberNames_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "member_names_copy" = some memberNamesCopy)
    (hp : p.lookup "block_shape_member_names" = some blockShapeMemberNames) (n : Nat) (s₀ : St)
    (q : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_shape_member_names" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ memberNamesW n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeMemberNames]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hmod : ∀ a m1 m2, allocW s₀.mem (rdW (s₀.mem.arr64 IW) (q + 1)) = some (a, m1) →
        nameCopyW n m1 a (rdW (s₀.mem.arr64 IW) q) (rdW (s₀.mem.arr64 IW) (q + 1)) = some m2 →
        memberNamesW (n + 1) s₀.mem q = some ([a, rdW (s₀.mem.arr64 IW) (q + 1)], m2) := by
      intro a m1 m2 h1 h2
      simp [memberNamesW, h1, h2]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n, memberNamesCopy_spec p hc n] <;>
      finish (gen := 20)

theorem memberNamesW_dec {n : Nat} {m m' : Mem} {p : Word} {r : List Word} {bs : BlockShape}
    (h : memberNamesW n m p = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hq : decBS m p.toNat = some bs)
    (hb : p.toNat + 9 < 2 ^ 64)
    (hsrc : ∀ o l, iwN m p.toNat = some o → iwN m (p.toNat + 1) = some l → o + l ≤ iwTop m)
    (hptr : ∀ o l j v, iwN m p.toNat = some o → iwN m (p.toNat + 1) = some l → j < l →
      iwN m (o + j) = some v → v < iwTop m) :
    r = [rdW (m.arr64 CTL) 200, UInt64.ofNat bs.k] ∧
    decHL m' (rdW (m.arr64 CTL) 200).toNat bs.k = some bs.memberNames ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
    (rdW (m.arr64 CTL) 200).toNat + bs.k = iwTop m' := by
  sorry

/-- **`block_shape_member_names` is `BlockShape.memberNames`**: the new `IW` slice holds the
members' names. -/
@[refines ConRon.Arena.BlockShape.memberNames]
theorem blockShapeMemberNames_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "member_names_copy" = some memberNamesCopy)
    (hp : p.lookup "block_shape_member_names" = some blockShapeMemberNames) (n : Nat) (s₀ : St)
    (q : Word) (bs : BlockShape) (hq : decBS s₀.mem q.toNat = some bs) (hb : q.toNat + 9 < 2 ^ 64)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hcl : 200 < (s₀.mem.arr64 CTL).size)
    (hsrc : ∀ o l, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l →
      o + l ≤ iwTop s₀.mem)
    (hptr : ∀ o l j v, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l → j < l →
      iwN s₀.mem (o + j) = some v → v < iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_member_names" [q]
    ⦃fun r s' => r = [rdW (s₀.mem.arr64 CTL) 200, UInt64.ofNat bs.k] ∧
      decHL s'.mem (rdW (s₀.mem.arr64 CTL) 200).toNat bs.k = some bs.memberNames ∧
      IWGrow s₀.mem s'.mem ∧ MemFrame [IW] [200] s₀.mem s'.mem ∧
      (rdW (s₀.mem.arr64 CTL) 200).toNat + bs.k = iwTop s'.mem; ⊤⦄ := by
  refine triple_post (blockShapeMemberNames_spec p ha hc hp n s₀ q) ?_
  intro r s' ⟨_, h⟩
  exact memberNamesW_dec h hsz hcl hq hb hsrc hptr

/-! ## `BlockParts.complete` -/

/-! ## `BlockShape.lps` -/

/-- A successful handle slice read is in bounds. -/
theorem hslice?_bound {k : IdxKind} (a : Array Word) : ∀ (c o : Nat) (xs : List (Idx k)),
    hslice? (aread a) o c = some xs → 0 < c → o + c ≤ a.size := by
  sorry

/-- Copying zero words reads no source: the source offset is irrelevant. -/
theorem erToIwW_src0 {n : Nat} {m : Mem} {o l : Word} (hl : l = 0) :
    erToIwW n m o l = erToIwW n m 0 l := by
  subst hl
  have : ∀ k m1 q, erCopyW k m1 q o 0 = erCopyW k m1 q 0 0 := by
    intro k m1 q; cases k <;> simp [erCopyW]
  simp only [erToIwW, this]

/-- The pool's top stays within the pool: what a callee that only allocates keeps of `IWOK`. -/
def IWRoom (m m' : Mem) : Prop := iwTop m ≤ (m.arr64 IW).size → iwTop m' ≤ (m'.arr64 IW).size

theorem IWRoom.refl (m : Mem) : IWRoom m m := fun h => h

theorem IWRoom.trans {m₁ m₂ m₃ : Mem} (h₁ : IWRoom m₁ m₂) (h₂ : IWRoom m₂ m₃) : IWRoom m₁ m₃ :=
  fun h => h₂ (h₁ h)

/-- An allocation ending at the new top, within the old pool, the size kept. -/
theorem IWRoom.of_alloc {m m' : Mem} {A : List TieredArray} {C : List Word} (hf : MemFrame A C m m')
    {t : Nat} (ht : t = iwTop m') (hroom : t ≤ (m.arr64 IW).size) : IWRoom m m' :=
  fun _ => by rw [hf.size IW, ← ht]; exact hroom

theorem erToIwW_room {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : erToIwW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (rdW (m.arr64 CTL) 200).toNat + l.toNat ≤ (m.arr64 IW).size := by
  simp only [erToIwW] at h
  rcases hal : allocW m l with _ | ⟨q, m1⟩
  · simp [hal] at h
  obtain ⟨hq, -, hroom⟩ := allocW_facts hal hsz
  rw [← hq]; exact hroom

/-- **`erToIwW_dec` when the slice decodes**: a successful `hslice?` of the source already bounds it
(a nonempty slice lies in `EREC`; an empty one reads nothing). -/
theorem erToIwW_decS {k : IdxKind} {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    {xs : List (Idx k)}
    (h : erToIwW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hE : (m.arr64 EREC).size < 2 ^ 64)
    (hsl : hslice? (erA m) o.toNat l.toNat = some xs) :
    r = [rdW (m.arr64 CTL) 200, l] ∧
    (decHL m' (rdW (m.arr64 CTL) 200).toNat l.toNat : Option (List (Idx k))) =
      hslice? (erA m) o.toNat l.toNat ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ m'.arr64 EREC = m.arr64 EREC ∧
    (rdW (m.arr64 CTL) 200).toNat + l.toNat = iwTop m' ∧ IWRoom m m' := by
  sorry

theorem erToIwW_two {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : erToIwW n m o l = some (r, m')) : r = [r.headD 0, r.tail.headD 0] := by
  simp only [erToIwW] at h
  rcases hal : allocW m l with _ | ⟨q, m1⟩
  · simp [hal] at h
  simp only [hal] at h
  rcases hcp : erCopyW (n - 1) m1 q o l with _ | m2
  · simp [hcp] at h
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  rfl

/-- `er_to_iw`'s spec with the result's shape (two words) spelt out. -/
theorem erToIw_specW2 (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "er_copy" = some erCopy) (hp : p.lookup "er_to_iw" = some erToIw) (n : Nat)
    (s₀ : St) (o l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "er_to_iw" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ erToIwW n s₀.mem o l = some (r, s'.mem) ∧
      r = [r.headD 0, r.tail.headD 0]; ⊤⦄ :=
  triple_post (erToIw_specW p ha hc hp n s₀ o l) (fun _r _s' ⟨h1, h2⟩ => ⟨h1, h2, erToIwW_two h2⟩)

/-- The model of `block_shape_lps` (its callee runs at `n - 1`). -/
def lpsW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, p =>
    if rdW (m.arr64 IW) (p + 1) = 0 then some ([0, 0], m)
    else erToIwW n m
      (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) + 1))
      (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) + 2))

section arms
variable (n : Nat) (m : Mem) (p : Word)
theorem lpsW_nil (h : rdW (m.arr64 IW) (p + 1) = 0) : lpsW (n + 1) m p = some ([0, 0], m) := by
  simp [lpsW, h]
theorem lpsW_cons (h : rdW (m.arr64 IW) (p + 1) ≠ 0) : lpsW (n + 1) m p =
    erToIwW n m
      (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) + 1))
      (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) + 2)) := by
  simp [lpsW, h]
end arms

grind_pattern [ind_grind] lpsW_nil => lpsW (n + 1) m p
grind_pattern [ind_grind] lpsW_cons => lpsW (n + 1) m p

theorem blockShapeLps_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw)
    (hp : p.lookup "block_shape_lps" = some blockShapeLps) (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_shape_lps" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ lpsW n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  sorry

theorem lpsW_dec {n : Nat} {m m' : Mem} {p : Word} {r : List Word} {bs : BlockShape}
    (h : lpsW n m p = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hE : (m.arr64 EREC).size < 2 ^ 64)
    (hq : decBS m p.toNat = some bs) (hb : p.toNat + 9 < 2 ^ 64) :
    r = [r.headD 0, r.tail.headD 0] ∧
    decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some bs.lps ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
    (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ IWRoom m m' := by
  sorry

/-- **`block_shape_lps` is `BlockShape.lps`**: a fresh `IW` copy of member 0's level parameters. -/
@[refines ConRon.Arena.BlockShape.lps]
theorem blockShapeLps_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw)
    (hp : p.lookup "block_shape_lps" = some blockShapeLps) (n : Nat) (s₀ : St) (q : Word)
    (bs : BlockShape) (hq : decBS s₀.mem q.toNat = some bs) (hb : q.toNat + 9 < 2 ^ 64)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hcl : 200 < (s₀.mem.arr64 CTL).size)
    (hE : (s₀.mem.arr64 EREC).size < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_lps" [q]
    ⦃fun r s' => r = [r.headD 0, r.tail.headD 0] ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat = some bs.lps ∧
      IWGrow s₀.mem s'.mem ∧ MemFrame [IW] [200] s₀.mem s'.mem ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧ IWRoom s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (blockShapeLps_spec p ha hc he hp n s₀ q) ?_
  intro r s' ⟨_, h⟩
  exact lpsW_dec h hsz hcl hE hq hb

end L.Ind

end
