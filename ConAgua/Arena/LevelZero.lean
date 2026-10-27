module

meta import ConAgua.L.Semantics
public import ConAgua.Arena.LevelApd
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `zeronessOf`: the zero-ness datum of a level

con-leche's `Level.zeronessOf` (Rust `kernel/level.rs:506`): `never`, or `ifAllZero ps` with
`ps` the parameters along the `max`/`imax`-right spine, left to right (`inter` concatenates).
In L the datum is a **flag and a slice of the heap**: `lv_zero(l)` appends the parameters' name
words to the heap (`lh_push`, one word each) and returns `1` for `never`, else `0`; the datum is
`ifAllZero` of the words pushed since the call. On `never` the pushed words are garbage (the twin's
`inter` drops them too). A caller copies the slice into its record (`EnvRec.lean`'s `decPW`
layout: kind, name slice).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `lh_push(w)`: one word on the heap -/

/-- **The model of `lh_push`**: the word's offset and the memory after. -/
def lhPushW (m : Mem) (w : Word) : Option (Word × Mem) :=
  if htop m >>> 40 ≠ 0 ∨ m.len64 LH ≤ htop m ∨ (m.arr64 CTL).size ≤ 192 then none
  else some (htop m, (m.set64 LH (htop m) w).set64 CTL 192 (htop m + 1))

/-- con-ron: none — the level scratch heap (the twin reads `ConLeche.Level` trees back, `readLevelM`) -/
def lhPush : FunDecl := lfn (w) locals (o) {
  o := CTL.u64[192];
  if o >> 40 != 0 || len(LH.u64) <= o { abort };
  LH.u64[o] := w;
  CTL.u64[192] := o + 1;
  return o
}

theorem lhPush_spec (p : Prog) (hp : p.lookup "lh_push" = some lhPush) (n : Nat) (s₀ : St)
    (w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lh_push" [w]
    ⦃fun r s' => LocEq s' s₀ ∧ lhPushW s₀.mem w = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lhPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
      finish [lhPushW, htop]

/-! ## `lv_zero(l)` -/

/-- After pushing a parameter's name: not `never`. -/
def pushK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (_, m₁) => some (0, m₁)

mutual
/-- **The model of `lv_zero`**: `1` for `never`, else `0` (the names pushed on the heap). -/
def zeroW : Nat → Mem → Word → Option (Word × Mem)
  | 0, _, _ => none
  | n + 1, m, l =>
    if lvG m l = 0 then some (0, m)
    else if lvG m l = 1 then some (1, m)
    else if lvG m l = 4 then pushK (lhPushW m (lvA m l))
    else if lvG m l = 3 then zeroW n m (lvB m l)
    else zK n (lvB m l) (zeroW n m (lvA m l))

/-- After a `max`'s left side: `never` absorbs. -/
def zK (n : Nat) (b : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => if x ≠ 0 then some (1, m₁) else zeroW n m₁ b
end

section arms
variable (n : Nat) (m m₁ : Mem) (l b x o : Word)
theorem pushK_some : pushK (some (o, m₁)) = some (0, m₁) := rfl
theorem zeroW_z (h : lvG m l = 0) : zeroW (n + 1) m l = some (0, m) := by rw [zeroW]; simp [h]
theorem zeroW_s (_h0 : lvG m l ≠ 0) (h : lvG m l = 1) : zeroW (n + 1) m l = some (1, m) := by
  rw [zeroW]; simp [h]
theorem zeroW_p (_h0 : lvG m l ≠ 0) (_h1 : lvG m l ≠ 1) (h : lvG m l = 4) :
    zeroW (n + 1) m l = pushK (lhPushW m (lvA m l)) := by rw [zeroW]; simp [h]
theorem zeroW_i (_h0 : lvG m l ≠ 0) (_h1 : lvG m l ≠ 1) (_h4 : lvG m l ≠ 4) (h : lvG m l = 3) :
    zeroW (n + 1) m l = zeroW n m (lvB m l) := by rw [zeroW]; simp [h]
theorem zeroW_m (h0 : lvG m l ≠ 0) (h1 : lvG m l ≠ 1) (h4 : lvG m l ≠ 4) (h3 : lvG m l ≠ 3) :
    zeroW (n + 1) m l = zK n (lvB m l) (zeroW n m (lvA m l)) := by rw [zeroW]; simp [h0, h1, h4, h3]
theorem zK_ne (hx : x ≠ 0) : zK n b (some (x, m₁)) = some (1, m₁) := by rw [zK]; simp [hx]
theorem zK_zero : zK n b (some (0, m₁)) = zeroW n m₁ b := by rw [zK]; simp
end arms

grind_pattern [level_grind] pushK_some => pushK (some (o, m₁))
grind_pattern [level_grind] zeroW_z => zeroW (n + 1) m l
grind_pattern [level_grind] zeroW_s => zeroW (n + 1) m l
grind_pattern [level_grind] zeroW_p => zeroW (n + 1) m l
grind_pattern [level_grind] zeroW_i => zeroW (n + 1) m l
grind_pattern [level_grind] zeroW_m => zeroW (n + 1) m l
grind_pattern [level_grind] zK_ne => zK n b (some (x, m₁))
grind_pattern [level_grind] zK_zero => zK n b (some (0, m₁))

/-- con-leche: ConLeche/Kernel/Level.lean:187-197 ConLeche.Level.zeronessOf -/
@[l_impl ConLeche.Level.zeronessOf]
def lvZero : FunDecl := lfn (l) locals (g, a, b, x) {
  (g, a, b) := call lv_node(l);
  if g == 0 { return 0 };
  if g == 1 { return 1 };
  if g == 4 { x := call lh_push(a); return 0 };
  if g == 3 { x := call lv_zero(b); return x };
  x := call lv_zero(a);
  if x != 0 { return 1 };
  x := call lv_zero(b);
  return x
}

section spec
variable (p : Prog) (hpn : p.lookup "lv_node" = some lvNode) (hpp : p.lookup "lh_push" = some lhPush)
  (hp : p.lookup "lv_zero" = some lvZero)

include hpn hpp hp in
theorem lvZero_spec (n : Nat) : ∀ (s₀ : St) (l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_zero" [l]
    ⦃fun r s' => LocEq s' s₀ ∧ zeroW n s₀.mem l = some (r.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ l; rw [invoke_eq _ hp]; simp only [callFn, lvZero]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ l
    rw [invoke_eq _ hp]
    simp only [callFn, lvZero]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvNode_spec p hpn n,
        lhPush_spec p hpp n, ih] <;>
      finish (gen := 20)

end spec

/-! ## The refinement -/

open ConLeche

variable {N : Word → Name → Prop}

theorem lhPushW_ext {m m' : Mem} {w o : Word} (h : lhPushW m w = some (o, m')) :
    HeapExt m m' ∧ o = htop m ∧ (htop m').toNat = (htop m).toNat + 1 ∧
      rdW (m'.arr64 LH) (htop m) = w := by
  simp only [lhPushW] at h
  split at h
  · simp at h
  · rename_i hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simp only [not_or, UInt64.not_le, ne_eq, Decidable.not_not, Nat.not_le] at hc
    obtain ⟨h40, hlen, hctl⟩ := hc
    have ht : (htop m).toNat < 2 ^ 40 := by
      have := congrArg UInt64.toNat h40
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow] at this
      omega
    have hl : (htop m).toNat < (m.arr64 LH).size := by
      rw [UInt64.lt_iff_toNat_lt] at hlen
      simp [Mem.len64] at hlen
      have := Nat.mod_le (m.arr64 LH).size 18446744073709551616
      omega
    have e1 : (htop m + 1).toNat = (htop m).toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hLC : (LH : ArrId) ≠ CTL := by decide
    have htop' : htop ((m.set64 LH (htop m) w).set64 CTL 192 (htop m + 1)) = htop m + 1 := by
      simp only [htop, rdW_set64L, size_set64L]; simp [hctl]
    refine ⟨HeapFrame.ext ⟨fun A h1 h2 => ?_, fun k hk => ?_, by rw [htop', e1]; omega,
      fun k hk => ?_, fun b => by simp only [size_set64L],
      by simp only [Mem.words_size_set64]⟩, rfl, by rw [htop', e1], ?_⟩
    · rw [Mem.arr64_set64_ne _ _ _ _ _ h1, Mem.arr64_set64_ne _ _ _ _ _ h2]
    · simp only [rdW_set64L, size_set64L]; simp [Ne.symm hk, Ne.symm hLC]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ hLC]
      simp only [rdW_set64L]
      have : htop m ≠ k := fun e => by rw [e] at hk; omega
      simp [this]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ hLC]; simp only [rdW_set64L]; simp [hl]

theorem NmsR.mono_lh {m m' : Mem} (he : HeapExt m m') :
    ∀ {o k : Word} {ps : List Name}, NmsR N m LH o k ps → o.toNat + k.toNat ≤ (htop m).toNat →
      NmsR N m' LH o k ps := by
  intro o k ps h
  induction h with
  | nil => intro _; exact .nil
  | @cons o k x xs hk hx _ ih =>
    intro hb
    have hk1 : 1 ≤ k.toNat := by
      rcases Nat.eq_zero_or_pos k.toNat with e | e
      · exact absurd (UInt64.toNat_inj.mp (by simpa using e)) hk
      · exact e
    have ho : (o + 1).toNat = o.toNat + 1 := by
      have := (htop m).toNat_lt; rw [UInt64.toNat_add]; simp; omega
    have hk' : (k - 1).toNat = k.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    refine .cons hk ?_ (ih (by rw [ho, hk']; omega))
    rw [he.lh o (by omega)]; exact hx

theorem NmsR.append {m : Mem} {A : ArrId} :
    ∀ {o k : Word} {ps : List Name}, NmsR N m A o k ps → ∀ {k' : Word} {qs : List Name},
      NmsR N m A (o + k) k' qs → o.toNat + k.toNat + k'.toNat < 2 ^ 64 →
      NmsR N m A o (k + k') (ps ++ qs) := by
  intro o k ps h
  induction h with
  | nil => intro k' qs h2 _; simpa using h2
  | @cons o k x xs hk hx _ ih =>
    intro k' qs h2 hb
    have hk1 : 1 ≤ k.toNat := by
      rcases Nat.eq_zero_or_pos k.toNat with e | e
      · exact absurd (UInt64.toNat_inj.mp (by simpa using e)) hk
      · exact e
    have hkk : (k + k').toNat = k.toNat + k'.toNat := by rw [UInt64.toNat_add]; simp; omega
    have hk' : (k - 1).toNat = k.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have ho : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have e1 : o + 1 + (k - 1) = o + k := by
      rw [UInt64.add_assoc, UInt64.add_comm 1, UInt64.sub_add_cancel]
    have e2 : k - 1 + k' = k + k' - 1 := by
      grind
    refine .cons (fun e => by rw [e] at hkk; simp at hkk; omega) hx ?_
    rw [← e2]
    exact ih (by rw [e1]; exact h2) (by rw [ho, hk']; omega)

/-- The datum `pw`, from the flag `x` and the words pushed between the tops `t₀` and `t₁`. -/
def ZR (N : Word → Name → Prop) (m : Mem) (t₀ t₁ x : Word) (pw : PropWhen) : Prop :=
  (x = 1 ∧ pw = .never) ∨ (x = 0 ∧ ∃ ps, pw = .ifAllZero ps ∧ NmsR N m LH t₀ (t₁ - t₀) ps)

/-- **`lv_zero` is `zeronessOf`.** -/
@[refines ConLeche.Level.zeronessOf]
theorem zeroW_ok (n : Nat) : ∀ (m m' : Mem) (l x : Word) (L : Level), LvR N m l L →
    zeroW n m l = some (x, m') → HeapExt m m' ∧ ZR N m' (htop m) (htop m') x (Level.zeronessOf L) := by
  induction n with
  | zero => intro m m' l x L _ h; simp [zeroW] at h
  | succ n ih =>
    intro m m' l x L hl h
    cases hl with
    | zero hv =>
      rw [zeroW_z n m l (lv_fields hv).1] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨HeapExt.refl _, Or.inr ⟨rfl, [], by simp [Level.zeronessOf], by simpa using NmsR.nil⟩⟩
    | succ hv _ =>
      rw [zeroW_s n m l (by simp [lvG, hv]) (lv_fields hv).1] at h; simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨HeapExt.refl _, Or.inl ⟨rfl, by simp [Level.zeronessOf]⟩⟩
    | @param _ a _ nm hv hn =>
      rw [zeroW_p n m l (by simp [lvG, hv]) (by simp [lvG, hv]) (lv_fields hv).1,
        (lv_fields hv).2.1] at h
      cases e : lhPushW m a with
      | none => rw [e] at h; simp [pushK] at h
      | some w =>
        obtain ⟨o, m₁⟩ := w
        rw [e, pushK_some] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨he, -, ht, hw⟩ := lhPushW_ext e
        refine ⟨he, Or.inr ⟨rfl, [nm], by simp [Level.zeronessOf], ?_⟩⟩
        have h1 : htop m₁ - htop m = 1 := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]; simp; omega
        rw [h1]
        exact .cons (by decide) (by rw [hw]; exact hn) (by simpa using NmsR.nil)
    | imax hv _ hb =>
      rw [zeroW_i n m l (by simp [lvG, hv]) (by simp [lvG, hv]) (by simp [lvG, hv])
        (lv_fields hv).1, (lv_fields hv).2.2] at h
      obtain ⟨he, hz⟩ := ih _ _ _ _ _ hb h
      exact ⟨he, by simpa [Level.zeronessOf] using hz⟩
    | @max _ a b L₁ L₂ hv ha hb =>
      rw [zeroW_m n m l (by simp [lvG, hv]) (by simp [lvG, hv]) (by simp [lvG, hv])
        (by simp [lvG, hv]), (lv_fields hv).2.1, (lv_fields hv).2.2] at h
      cases e : zeroW n m a with
      | none => rw [e] at h; simp [zK] at h
      | some w =>
        obtain ⟨y, m₁⟩ := w
        rw [e] at h
        obtain ⟨he₁, hz₁⟩ := ih _ _ _ _ _ ha e
        rcases hz₁ with ⟨rfl, hn₁⟩ | ⟨rfl, ps, hp₁, hs₁⟩
        · rw [zK_ne (hx := by decide)] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨he₁, Or.inl ⟨rfl, by simp [Level.zeronessOf, hn₁, PropWhen.inter]⟩⟩
        · rw [zK_zero] at h
          obtain ⟨he₂, hz₂⟩ := ih _ _ _ _ _ (hb.mono he₁) h
          refine ⟨he₁.trans he₂, ?_⟩
          rcases hz₂ with ⟨rfl, hn₂⟩ | ⟨rfl, qs, hp₂, hs₂⟩
          · exact Or.inl ⟨rfl, by simp [Level.zeronessOf, hp₁, hn₂, PropWhen.inter]⟩
          · refine Or.inr ⟨rfl, ps ++ qs, by simp [Level.zeronessOf, hp₁, hp₂, PropWhen.inter], ?_⟩
            have t₁ := he₁.top
            have t₂ := he₂.top
            have hd₁ : (htop m₁ - htop m).toNat = (htop m₁).toNat - (htop m).toNat := by
              rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
            have hd₂ : (htop m' - htop m₁).toNat = (htop m').toNat - (htop m₁).toNat := by
              rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
            have e₁ : htop m + (htop m₁ - htop m) = htop m₁ := by
              rw [UInt64.add_comm, UInt64.sub_add_cancel]
            have e₂ : htop m₁ - htop m + (htop m' - htop m₁) = htop m' - htop m := by
              apply UInt64.toNat_inj.mp
              rw [UInt64.toNat_add, hd₁, hd₂,
                UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
              have := (htop m').toNat_lt; simp; omega
            have hs₁' := hs₁.mono_lh he₂ (by rw [hd₁]; omega)
            have := NmsR.append hs₁' (by rw [e₁]; exact hs₂)
              (by rw [hd₁, hd₂]; have := (htop m').toNat_lt; omega)
            rwa [e₂] at this

end L.Arena
