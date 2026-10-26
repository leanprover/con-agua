module

public import ConAgua.Arena.LevelZero
public import ConAgua.Arena.LevelSubst
public import ConAgua.Arena.LevelSimpRel
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

@[expose] public section

/-!
# `subst` with lists, and `substPW`

con-leche's `Level.subst ks vs l` and `Level.subst.go` (Rust `kernel/level.rs:201-224`) with the
keys a slice of name words in an array `KA` and the values a slice of level pointers in an array
`VA` (the caller's choices: the declaration's level parameters and a `const`'s level list,
`instLPGo`), and `Level.substPW ks vs pw` (`PropWhen.bindZ` of `zeronessOf ∘ subst.go`) with the
datum's names a slice of an array `PA`. The L code is generic in the arrays (as `lv_mem`'s).

* `lv_lookup(ko, kc, vo, vc, w)`: `subst.go`: `(1, v)` for the first key `w` (and a value at the
  same position), else `(0, 0)` (the twin's `.param n`);
* `lv_substl(l, ko, kc, vo, vc)`: `subst ks vs l`;
* `lv_spw(po, pc, …)`: `bindZ.go` over the names: per name its value's `lv_zero`, or the name
  itself pushed; `lv_substpw(kd, po, pc, …)`: `substPW` (`kd = 0` is `never`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

section code
variable (KA VA PA : ArrId)

/-- **The model of `lv_lookup`**: `(found, value)`. -/
def lookupW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Word)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, ko, kc, vo, vc, w =>
    if kc = 0 ∨ vc = 0 then some (0, 0)
    else if rdW (m.arr64 KA) ko = w then some (1, trd m VA vo)
    else lookupW n m (ko + 1) (kc - 1) (vo + 1) (vc - 1) w

theorem lookupW_end (n : Nat) (m : Mem) (ko kc vo vc w : Word) (h : kc = 0 ∨ vc = 0) :
    lookupW KA VA (n + 1) m ko kc vo vc w = some (0, 0) := by simp [lookupW, h]
theorem lookupW_hit (n : Nat) (m : Mem) (ko kc vo vc w : Word) (h : ¬ (kc = 0 ∨ vc = 0))
    (hw : rdW (m.arr64 KA) ko = w) :
    lookupW KA VA (n + 1) m ko kc vo vc w = some (1, trd m VA vo) := by
  rw [lookupW]; simp only [h, hw, ↓reduceIte]
theorem lookupW_next (n : Nat) (m : Mem) (ko kc vo vc w : Word) (h : ¬ (kc = 0 ∨ vc = 0))
    (hw : rdW (m.arr64 KA) ko ≠ w) :
    lookupW KA VA (n + 1) m ko kc vo vc w = lookupW KA VA n m (ko + 1) (kc - 1) (vo + 1) (vc - 1) w := by
  rw [lookupW]; simp only [h, hw, ↓reduceIte]

/-- con-leche: ConLeche/Kernel/Level.lean:31-42 ConLeche.Level.subst -/
def lvLookupG : FunDecl := lfn (ko, kc, vo, vc, w) locals (f, v) {
  if kc == 0 || vc == 0 { return (0, 0) };
  if KA.u64[ko] == w { return (1, VA⦃vo⦄) };
  (f, v) := call lv_lookup(ko + 1, kc - 1, vo + 1, vc - 1, w);
  return (f, v)
}

/-- After the lookup at a `param`: its value, or the level unchanged. -/
def lkK (l : Word) (m : Mem) : Option (Word × Word) → Option (Word × Mem)
  | none => none
  | some (f, v) => if f ≠ 0 then some (v, m) else some (l, m)

mutual
/-- **The model of `lv_substl`.** -/
def substLW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, l, ko, kc, vo, vc =>
    if lvG m l = 0 then some (l, m)
    else if lvG m l = 4 then lkK l m (lookupW KA VA n m ko kc vo vc (lvA m l))
    else if lvG m l = 1 then succK (substLW n m (lvA m l) ko kc vo vc)
    else slK n ko kc vo vc (lvG m l) (lvB m l) (substLW n m (lvA m l) ko kc vo vc)

/-- After the first child of a `max`/`imax`. -/
def slK (n : Nat) (ko kc vo vc g b : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => subK₂ g x (substLW n m₁ b ko kc vo vc)
end

section arms
variable (n : Nat) (m m₁ : Mem) (l ko kc vo vc g b x f v : Word)
theorem lkK_hit (hf : f ≠ 0) : lkK l m (some (f, v)) = some (v, m) := by simp [lkK, hf]
theorem lkK_miss : lkK l m (some (0, v)) = some (l, m) := by simp [lkK]
theorem substLW_zero (h : lvG m l = 0) : substLW KA VA (n + 1) m l ko kc vo vc = some (l, m) := by
  rw [substLW]; simp [h]
theorem substLW_param (_h0 : lvG m l ≠ 0) (h : lvG m l = 4) :
    substLW KA VA (n + 1) m l ko kc vo vc = lkK l m (lookupW KA VA n m ko kc vo vc (lvA m l)) := by
  rw [substLW]; simp [h]
theorem substLW_succ (_h0 : lvG m l ≠ 0) (_h4 : lvG m l ≠ 4) (h : lvG m l = 1) :
    substLW KA VA (n + 1) m l ko kc vo vc = succK (substLW KA VA n m (lvA m l) ko kc vo vc) := by
  rw [substLW]; simp [h]
theorem substLW_bin (h0 : lvG m l ≠ 0) (h4 : lvG m l ≠ 4) (h1 : lvG m l ≠ 1) :
    substLW KA VA (n + 1) m l ko kc vo vc =
      slK KA VA n ko kc vo vc (lvG m l) (lvB m l) (substLW KA VA n m (lvA m l) ko kc vo vc) := by
  rw [substLW]; simp [h0, h4, h1]
theorem slK_some : slK KA VA n ko kc vo vc g b (some (x, m₁)) =
    subK₂ g x (substLW KA VA n m₁ b ko kc vo vc) := by rw [slK]
end arms

/-- con-leche: ConLeche/Kernel/Level.lean:31-42 ConLeche.Level.subst
con-leche: ConLeche/Kernel/Level.lean:31-42 ConLeche.Level.subst.go -/
@[l_impl ConLeche.Level.subst ConLeche.Level.subst.go]
def lvSubstL : FunDecl := lfn (l, ko, kc, vo, vc) locals (g, a, b, x, y, f, v) {
  (g, a, b) := call lv_node(l);
  if g == 0 { return l };
  if g == 4 {
    (f, v) := call lv_lookup(ko, kc, vo, vc, a);
    if f != 0 { return v };
    return l
  };
  x := call lv_substl(a, ko, kc, vo, vc);
  if g == 1 { x := call lh_mk(1, x, 0); return x };
  y := call lv_substl(b, ko, kc, vo, vc);
  x := call lh_mk(g, x, y);
  return x
}

/-- After the lookup of a name `w`: its value's datum, or `w` itself pushed. -/
def lfK (n : Nat) (m : Mem) (w : Word) : Option (Word × Word) → Option (Word × Mem)
  | none => none
  | some (f, v) => if f ≠ 0 then zeroW n m v else pushK (lhPushW m w)

mutual
/-- **The model of `lv_spw`** (`bindZ.go`). -/
def spwW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, po, pc, ko, kc, vo, vc =>
    if pc = 0 then some (0, m)
    else spK n po pc ko kc vo vc
      (lfK n m (rdW (m.arr64 PA) po) (lookupW KA VA n m ko kc vo vc (rdW (m.arr64 PA) po)))

/-- After a name's datum: `never` absorbs. -/
def spK (n : Nat) (po pc ko kc vo vc : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => if x ≠ 0 then some (1, m₁) else spwW n m₁ (po + 1) (pc - 1) ko kc vo vc
end

section arms2
variable (n : Nat) (m m₁ : Mem) (po pc ko kc vo vc w f v x : Word)
theorem lfK_hit (hf : f ≠ 0) : lfK n m w (some (f, v)) = zeroW n m v := by simp [lfK, hf]
theorem lfK_miss : lfK n m w (some (0, v)) = pushK (lhPushW m w) := by simp [lfK]
theorem spwW_nil (h : pc = 0) : spwW KA VA PA (n + 1) m po pc ko kc vo vc = some (0, m) := by
  rw [spwW]; simp [h]
theorem spwW_cons (h : pc ≠ 0) : spwW KA VA PA (n + 1) m po pc ko kc vo vc =
    spK KA VA PA n po pc ko kc vo vc
      (lfK n m (rdW (m.arr64 PA) po) (lookupW KA VA n m ko kc vo vc (rdW (m.arr64 PA) po))) := by
  rw [spwW]; simp [h]
theorem spK_ne (hx : x ≠ 0) : spK KA VA PA n po pc ko kc vo vc (some (x, m₁)) = some (1, m₁) := by
  rw [spK]; simp [hx]
theorem spK_zero : spK KA VA PA n po pc ko kc vo vc (some (0, m₁)) =
    spwW KA VA PA n m₁ (po + 1) (pc - 1) ko kc vo vc := by rw [spK]; simp
end arms2

/-- con-leche: ConLeche/Kernel/Level.lean:199-205 ConLeche.Level.substPW -/
def lvSpwG : FunDecl := lfn (po, pc, ko, kc, vo, vc) locals (f, v, x, w) {
  if pc == 0 { return 0 };
  w := PA.u64[po];
  (f, v) := call lv_lookup(ko, kc, vo, vc, w);
  if f != 0 { x := call lv_zero(v) } else { x := call lh_push(w); x := 0 };
  if x != 0 { return 1 };
  x := call lv_spw(po + 1, pc - 1, ko, kc, vo, vc);
  return x
}

/-- **The model of `lv_substpw`**: `kd = 0` is `never`. -/
def substPWW (n : Nat) (m : Mem) (kd po pc ko kc vo vc : Word) : Option (Word × Mem) :=
  match n with
  | 0 => none
  | n + 1 => if kd = 0 then some (1, m) else spwW KA VA PA n m po pc ko kc vo vc

/-- con-leche: ConLeche/Kernel/Level.lean:199-205 ConLeche.Level.substPW -/
@[l_impl ConLeche.Level.substPW]
def lvSubstPW : FunDecl := lfn (kd, po, pc, ko, kc, vo, vc) locals (x) {
  if kd == 0 { return 1 };
  x := call lv_spw(po, pc, ko, kc, vo, vc);
  return x
}

end code

grind_pattern [level_grind] lookupW_end => lookupW KA VA (n + 1) m ko kc vo vc w
grind_pattern [level_grind] lookupW_hit => lookupW KA VA (n + 1) m ko kc vo vc w
grind_pattern [level_grind] lookupW_next => lookupW KA VA (n + 1) m ko kc vo vc w
grind_pattern [level_grind] lkK_hit => lkK l m (some (f, v))
grind_pattern [level_grind] lkK_miss => lkK l m (some (0, v))
grind_pattern [level_grind] substLW_zero => substLW KA VA (n + 1) m l ko kc vo vc
grind_pattern [level_grind] substLW_param => substLW KA VA (n + 1) m l ko kc vo vc
grind_pattern [level_grind] substLW_succ => substLW KA VA (n + 1) m l ko kc vo vc
grind_pattern [level_grind] substLW_bin => substLW KA VA (n + 1) m l ko kc vo vc
grind_pattern [level_grind] slK_some => slK KA VA n ko kc vo vc g b (some (x, m₁))
grind_pattern [level_grind] lfK_hit => lfK n m w (some (f, v))
grind_pattern [level_grind] lfK_miss => lfK n m w (some (0, v))
grind_pattern [level_grind] spwW_nil => spwW KA VA PA (n + 1) m po pc ko kc vo vc
grind_pattern [level_grind] spwW_cons => spwW KA VA PA (n + 1) m po pc ko kc vo vc
grind_pattern [level_grind] spK_ne => spK KA VA PA n po pc ko kc vo vc (some (x, m₁))
grind_pattern [level_grind] spK_zero => spK KA VA PA n po pc ko kc vo vc (some (0, m₁))

section specs
variable (KA VA PA : ArrId) (p : Prog) (hpl : p.lookup "lv_lookup" = some (lvLookupG KA VA))

include hpl in
theorem lvLookup_spec (n : Nat) : ∀ (s₀ : St) (ko kc vo vc w : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_lookup" [ko, kc, vo, vc, w]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      lookupW KA VA n s₀.mem ko kc vo vc w = some (r.headD 0, r.tail.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ ko kc vo vc w; rw [invoke_eq _ hpl]; simp only [callFn, lvLookupG]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ko kc vo vc w
    rw [invoke_eq _ hpl]
    simp only [callFn, lvLookupG]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)

include hpl in
theorem lvSubstL_spec (hpn : p.lookup "lv_node" = some lvNode) (hpm : p.lookup "lh_mk" = some lhMk)
    (hp : p.lookup "lv_substl" = some lvSubstL) (n : Nat) : ∀ (s₀ : St) (l ko kc vo vc : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_substl" [l, ko, kc, vo, vc]
    ⦃fun r s' => LocEq s' s₀ ∧ substLW KA VA n s₀.mem l ko kc vo vc = some (r.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ l ko kc vo vc; rw [invoke_eq _ hp]; simp only [callFn, lvSubstL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ l ko kc vo vc
    rw [invoke_eq _ hp]
    simp only [callFn, lvSubstL]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvNode_spec p hpn n,
        lhMk_spec p hpm n, lvLookup_spec KA VA p hpl n, ih] <;>
      finish (gen := 20)

include hpl in
theorem lvSpw_spec (hpn : p.lookup "lv_node" = some lvNode) (hpp : p.lookup "lh_push" = some lhPush)
    (hpz : p.lookup "lv_zero" = some lvZero) (hp : p.lookup "lv_spw" = some (lvSpwG PA)) (n : Nat) :
    ∀ (s₀ : St) (po pc ko kc vo vc : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_spw" [po, pc, ko, kc, vo, vc]
    ⦃fun r s' => LocEq s' s₀ ∧
      spwW KA VA PA n s₀.mem po pc ko kc vo vc = some (r.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ po pc ko kc vo vc; rw [invoke_eq _ hp]; simp only [callFn, lvSpwG]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ po pc ko kc vo vc
    rw [invoke_eq _ hp]
    simp only [callFn, lvSpwG]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, lvLookup_spec KA VA p hpl n,
        lvZero_spec p hpn hpp hpz n, lhPush_spec p hpp n, ih] <;>
      finish (gen := 20)

end specs

/-! ## The refinements -/

open ConLeche

variable {N : Word → Name → Prop}

/-- The words `A[o .. o + k)` are pointers to the levels `ls` (`LvsR` on any array). -/
inductive LvsAR (N : Word → Name → Prop) (m : Mem) (A : ArrId) : Word → Word → List Level → Prop
  | nil {o : Word} : LvsAR N m A o 0 []
  | cons {o k : Word} {l : Level} {ls : List Level} : k ≠ 0 → LvR N m (trd m A o) l →
      LvsAR N m A (o + 1) (k - 1) ls → LvsAR N m A o k (l :: ls)

theorem LvsAR.mono {m m' : Mem} {A : ArrId} (he : HeapExt m m') (hA : A ≠ LH ∧ A ≠ CTL ∧ A < 256)
    {o k : Word} {ls : List Level} (h : LvsAR N m A o k ls) : LvsAR N m' A o k ls := by
  have e : ∀ x, trd m' A x = trd m A x := fun x => by
    simp only [trd]
    rw [he.arr _ (tierA_ne_small _ _ hA.2.2 (by decide) hA.1.symm _)
      (tierA_ne_small _ _ hA.2.2 (by decide) hA.2.1.symm _)]
  induction h with
  | nil => exact .nil
  | cons hk hl _ ih => exact .cons hk (by rw [e]; exact hl.mono he) ih

theorem NmsR.mono {m m' : Mem} {A : ArrId} (he : HeapExt m m') (hA : A ≠ LH ∧ A ≠ CTL)
    {o k : Word} {ps : List Name} (h : NmsR N m A o k ps) : NmsR N m' A o k ps := by
  induction h with
  | nil => exact .nil
  | cons hk hx _ ih => exact .cons hk (by rw [he.arr _ hA.1 hA.2]; exact hx) ih

/-- **`lv_lookup` is `subst.go`**: found, the value is related to `subst.go`'s answer; not
found, that answer is `param`. -/
theorem lookupW_ok (hN : NameRel N) {KA VA : ArrId} (n : Nat) : ∀ (m : Mem) (ko kc vo vc w f v : Word)
    (ks : List Name) (vs : List Level) (nm : Name), NmsR N m KA ko kc ks → LvsAR N m VA vo vc vs →
    N w nm → lookupW KA VA n m ko kc vo vc w = some (f, v) →
    (f ≠ 0 ∧ LvR N m v (Level.subst.go ks vs nm)) ∨
      (f = 0 ∧ Level.subst.go ks vs nm = .param nm) := by
  induction n with
  | zero => intro m ko kc vo vc w f v ks vs nm _ _ _ h; simp [lookupW] at h
  | succ n ih =>
    intro m ko kc vo vc w f v ks vs nm hk hv hw h
    cases hk with
    | nil =>
      rw [lookupW_end KA VA n m ko 0 vo vc w (Or.inl rfl)] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨rfl, by simp [Level.subst.go]⟩
    | @cons _ kc' k ks' hk0 hkx hks =>
      cases hv with
      | nil =>
        rw [lookupW_end KA VA n m ko _ vo 0 w (Or.inr rfl)] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
        exact Or.inr ⟨rfl, by simp [Level.subst.go]⟩
      | @cons _ vc' V vs' hv0 hvl hvs =>
        have hne : ¬ (kc = 0 ∨ vc = 0) := by simp [hk0, hv0]
        by_cases e : rdW (m.arr64 KA) ko = w
        · rw [lookupW_hit KA VA n m ko _ vo _ w hne e] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
          rw [e] at hkx
          have : k = nm := hN.fn _ _ _ hkx hw
          exact Or.inl ⟨by decide, by simpa [Level.subst.go, this] using hvl⟩
        · rw [lookupW_next KA VA n m ko _ vo _ w hne e] at h
          have : k ≠ nm := fun h' => e (hN.inj _ _ _ hkx (h' ▸ hw))
          have := ih _ _ _ _ _ _ _ _ _ _ _ hks hvs hw h
          simpa [Level.subst.go, ‹k ≠ nm›] using this

/-- **`lv_substl` is `subst`.** -/
@[refines ConLeche.Level.subst ConLeche.Level.subst.go]
theorem substLW_ok (hN : NameRel N) {KA VA : ArrId} (hKA : KA ≠ LH ∧ KA ≠ CTL)
    (hVA : VA ≠ LH ∧ VA ≠ CTL ∧ VA < 256) (ks : List Name) (vs : List Level) (n : Nat) :
    ∀ (m m' : Mem) (l ko kc vo vc x : Word) (L : Level), LvR N m l L → NmsR N m KA ko kc ks →
      LvsAR N m VA vo vc vs → substLW KA VA n m l ko kc vo vc = some (x, m') →
      HeapExt m m' ∧ LvR N m' x (Level.subst ks vs L) := by
  induction n with
  | zero => intro m m' l ko kc vo vc x L _ _ _ h; simp [substLW] at h
  | succ n ih =>
    intro m m' l ko kc vo vc x L hl hk hv h
    cases hl with
    | zero hw =>
      rw [substLW_zero KA VA n m l ko kc vo vc (lv_fields hw).1] at h; simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨HeapExt.refl _, by simpa [Level.subst] using LvR.zero hw⟩
    | @param _ a b nm hw hn =>
      rw [substLW_param KA VA n m l ko kc vo vc (by simp [lvG, hw]) (lv_fields hw).1,
        (lv_fields hw).2.1] at h
      cases e : lookupW KA VA n m ko kc vo vc a with
      | none => rw [e] at h; simp [lkK] at h
      | some fv =>
        obtain ⟨f, v⟩ := fv
        rw [e] at h
        rcases lookupW_ok hN n _ _ _ _ _ _ _ _ _ _ _ hk hv hn e with ⟨hf, hvl⟩ | ⟨rfl, hgo⟩
        · rw [lkK_hit (hf := hf)] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨HeapExt.refl _, by simpa [Level.subst] using hvl⟩
        · rw [lkK_miss] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨HeapExt.refl _, by simpa [Level.subst, hgo] using LvR.param hw hn⟩
    | succ hw ha =>
      rw [substLW_succ KA VA n m l ko kc vo vc (by simp [lvG, hw]) (by simp [lvG, hw])
        (lv_fields hw).1, (lv_fields hw).2.1] at h
      obtain ⟨y, m₁, hy, hm⟩ := succK_inv h
      obtain ⟨he₁, hy'⟩ := ih _ _ _ _ _ _ _ _ _ ha hk hv hy
      obtain ⟨he₂, hx⟩ := mk_succ hm hy'
      exact ⟨he₁.trans he₂, by simpa [Level.subst] using hx⟩
    | max hw ha hb =>
      rw [substLW_bin KA VA n m l ko kc vo vc (by simp [lvG, hw]) (by simp [lvG, hw])
        (by simp [lvG, hw]), (lv_fields hw).1, (lv_fields hw).2.1, (lv_fields hw).2.2] at h
      cases e₁ : substLW KA VA n m _ ko kc vo vc with
      | none => rw [e₁] at h; simp [slK] at h
      | some w₁ =>
        obtain ⟨x₁, m₁⟩ := w₁
        rw [e₁, slK_some] at h
        obtain ⟨he₁, hx₁⟩ := ih _ _ _ _ _ _ _ _ _ ha hk hv e₁
        cases e₂ : substLW KA VA n m₁ _ ko kc vo vc with
        | none => rw [e₂] at h; simp [subK₂] at h
        | some w₂ =>
          obtain ⟨y, m₂⟩ := w₂
          rw [e₂, subK₂_some] at h
          obtain ⟨he₂, hy⟩ := ih _ _ _ _ _ _ _ _ _ (hb.mono he₁) (hk.mono he₁ hKA)
            (hv.mono he₁ hVA) e₂
          obtain ⟨he₃, hz⟩ := mk_max h (hx₁.mono he₂) hy
          exact ⟨(he₁.trans he₂).trans he₃, by simpa [Level.subst] using hz⟩
    | imax hw ha hb =>
      rw [substLW_bin KA VA n m l ko kc vo vc (by simp [lvG, hw]) (by simp [lvG, hw])
        (by simp [lvG, hw]), (lv_fields hw).1, (lv_fields hw).2.1, (lv_fields hw).2.2] at h
      cases e₁ : substLW KA VA n m _ ko kc vo vc with
      | none => rw [e₁] at h; simp [slK] at h
      | some w₁ =>
        obtain ⟨x₁, m₁⟩ := w₁
        rw [e₁, slK_some] at h
        obtain ⟨he₁, hx₁⟩ := ih _ _ _ _ _ _ _ _ _ ha hk hv e₁
        cases e₂ : substLW KA VA n m₁ _ ko kc vo vc with
        | none => rw [e₂] at h; simp [subK₂] at h
        | some w₂ =>
          obtain ⟨y, m₂⟩ := w₂
          rw [e₂, subK₂_some] at h
          obtain ⟨he₂, hy⟩ := ih _ _ _ _ _ _ _ _ _ (hb.mono he₁) (hk.mono he₁ hKA)
            (hv.mono he₁ hVA) e₂
          obtain ⟨he₃, hz⟩ := mk_imax h (hx₁.mono he₂) hy
          exact ⟨(he₁.trans he₂).trans he₃, by simpa [Level.subst] using hz⟩

/-- Two data pushed one after the other intersect (`inter`'s concatenation). -/
theorem ZR.inter {m₁ m₂ : Mem} {t₀ t₁ t₂ x : Word} {ps : List Name} {pw : PropWhen}
    (h₁ : NmsR N m₁ LH t₀ (t₁ - t₀) ps) (hle₁ : t₀.toNat ≤ t₁.toNat) (htop₁ : t₁ = htop m₁)
    (he : HeapExt m₁ m₂) (htop₂ : t₂ = htop m₂) (h₂ : ZR N m₂ t₁ t₂ x pw) :
    ZR N m₂ t₀ t₂ x ((PropWhen.ifAllZero ps).inter pw) := by
  subst htop₁ htop₂
  rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, qs, rfl, hs₂⟩
  · exact Or.inl ⟨rfl, by simp [PropWhen.inter]⟩
  · refine Or.inr ⟨rfl, ps ++ qs, by simp [PropWhen.inter], ?_⟩
    have t₂ := he.top
    have hd₁ : (htop m₁ - t₀).toNat = (htop m₁).toNat - t₀.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
    have hd₂ : (htop m₂ - htop m₁).toNat = (htop m₂).toNat - (htop m₁).toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
    have e₁ : t₀ + (htop m₁ - t₀) = htop m₁ := by rw [UInt64.add_comm, UInt64.sub_add_cancel]
    have e₂ : htop m₁ - t₀ + (htop m₂ - htop m₁) = htop m₂ - t₀ := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, hd₁, hd₂,
        UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
      have := (htop m₂).toNat_lt; simp; omega
    have hs₁' := h₁.mono_lh he (by rw [hd₁]; omega)
    have := NmsR.append hs₁' (by rw [e₁]; exact hs₂)
      (by rw [hd₁, hd₂]; have := (htop m₂).toNat_lt; omega)
    rwa [e₂] at this

/-- `bindZ.go` of `zeronessOf ∘ subst.go`. -/
abbrev spwF (ks : List Name) (vs : List Level) : Name → PropWhen :=
  fun nm => Level.zeronessOf (Level.subst.go ks vs nm)

theorem spwW_ok (hN : NameRel N) {KA VA PA : ArrId} (hKA : KA ≠ LH ∧ KA ≠ CTL)
    (hVA : VA ≠ LH ∧ VA ≠ CTL ∧ VA < 256) (hPA : PA ≠ LH ∧ PA ≠ CTL) (ks : List Name) (vs : List Level)
    (n : Nat) : ∀ (m m' : Mem) (po pc ko kc vo vc x : Word) (ps : List Name),
      NmsR N m PA po pc ps → NmsR N m KA ko kc ks → LvsAR N m VA vo vc vs →
      spwW KA VA PA n m po pc ko kc vo vc = some (x, m') →
      HeapExt m m' ∧ ZR N m' (htop m) (htop m') x (PropWhen.bindZ.go (spwF ks vs) ps) := by
  induction n with
  | zero => intro m m' po pc ko kc vo vc x ps _ _ _ h; simp [spwW] at h
  | succ n ih =>
    intro m m' po pc ko kc vo vc x ps hp hk hv h
    cases hp with
    | nil =>
      rw [spwW_nil KA VA PA n m po 0 ko kc vo vc rfl] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨HeapExt.refl _, Or.inr ⟨rfl, [], by simp [PropWhen.bindZ.go], by simpa using NmsR.nil⟩⟩
    | @cons _ pc' p ps' hp0 hpx hps =>
      rw [spwW_cons KA VA PA n m po _ ko kc vo vc hp0] at h
      -- the head's datum
      have hd : ∃ x₁ m₁, lfK n m (rdW (m.arr64 PA) po)
          (lookupW KA VA n m ko kc vo vc (rdW (m.arr64 PA) po)) = some (x₁, m₁) ∧
          HeapExt m m₁ ∧ ZR N m₁ (htop m) (htop m₁) x₁ (spwF ks vs p) := by
        cases e : lookupW KA VA n m ko kc vo vc (rdW (m.arr64 PA) po) with
        | none => rw [e] at h; simp [lfK, spK] at h
        | some fv =>
          obtain ⟨f, v⟩ := fv
          rcases lookupW_ok hN n _ _ _ _ _ _ _ _ _ _ _ hk hv hpx e with ⟨hf, hvl⟩ | ⟨rfl, hgo⟩
          · rw [e, lfK_hit (hf := hf)] at h
            rw [lfK_hit (hf := hf)]
            cases e' : zeroW n m v with
            | none => rw [e'] at h; simp [spK] at h
            | some w =>
              obtain ⟨x₁, m₁⟩ := w
              obtain ⟨he, hz⟩ := zeroW_ok n _ _ _ _ _ hvl e'
              exact ⟨x₁, m₁, rfl, he, hz⟩
          · rw [e, lfK_miss] at h
            rw [lfK_miss]
            cases e' : lhPushW m (rdW (m.arr64 PA) po) with
            | none => rw [e'] at h; simp [pushK, spK] at h
            | some w =>
              obtain ⟨o, m₁⟩ := w
              obtain ⟨he, -, ht, hw⟩ := lhPushW_ext e'
              refine ⟨0, m₁, by rw [pushK_some], he, Or.inr ⟨rfl, [p], by simp [spwF, hgo,
                Level.zeronessOf], ?_⟩⟩
              have h1 : htop m₁ - htop m = 1 := by
                apply UInt64.toNat_inj.mp
                rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]; simp; omega
              rw [h1]
              exact .cons (by decide) (by rw [hw]; exact hpx) (by simpa using NmsR.nil)
      obtain ⟨x₁, m₁, e₁, he₁, hz₁⟩ := hd
      rw [e₁] at h
      rcases hz₁ with ⟨rfl, hn₁⟩ | ⟨rfl, qs, hq₁, hs₁⟩
      · rw [spK_ne (hx := by decide)] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨he₁, Or.inl ⟨rfl, by simp [PropWhen.bindZ.go, hn₁, PropWhen.inter]⟩⟩
      · rw [spK_zero] at h
        obtain ⟨he₂, hz₂⟩ := ih _ _ _ _ _ _ _ _ _ _ (hps.mono he₁ hPA) (hk.mono he₁ hKA)
          (hv.mono he₁ hVA) h
        refine ⟨he₁.trans he₂, ?_⟩
        have := ZR.inter hs₁ he₁.top rfl he₂ rfl hz₂
        simpa [PropWhen.bindZ.go, hq₁] using this

/-- The datum `pw` at `(kd, po, pc)`: `kd = 0` is `never`, else the names of the slice. -/
def PWR (N : Word → Name → Prop) (m : Mem) (A : ArrId) (kd po pc : Word) (pw : PropWhen) : Prop :=
  (kd = 0 ∧ pw = .never) ∨ (kd ≠ 0 ∧ ∃ ps, pw = .ifAllZero ps ∧ NmsR N m A po pc ps)

/-- **`lv_substpw` is `substPW`.** -/
@[refines ConLeche.Level.substPW]
theorem substPWW_ok (hN : NameRel N) {KA VA PA : ArrId} (hKA : KA ≠ LH ∧ KA ≠ CTL)
    (hVA : VA ≠ LH ∧ VA ≠ CTL ∧ VA < 256) (hPA : PA ≠ LH ∧ PA ≠ CTL) (ks : List Name) (vs : List Level)
    (n : Nat) (m m' : Mem) (kd po pc ko kc vo vc x : Word) (pw : PropWhen)
    (hp : PWR N m PA kd po pc pw) (hk : NmsR N m KA ko kc ks) (hv : LvsAR N m VA vo vc vs)
    (h : substPWW KA VA PA n m kd po pc ko kc vo vc = some (x, m')) :
    HeapExt m m' ∧ ZR N m' (htop m) (htop m') x (Level.substPW ks vs pw) := by
  cases n with
  | zero => simp [substPWW] at h
  | succ n =>
    simp only [substPWW] at h
    rcases hp with ⟨rfl, rfl⟩ | ⟨hkd, ps, rfl, hps⟩
    · simp at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨HeapExt.refl _, Or.inl ⟨rfl, by simp [Level.substPW, PropWhen.bindZ]⟩⟩
    · simp only [hkd, ↓reduceIte] at h
      have := spwW_ok hN hKA hVA hPA ks vs n _ _ _ _ _ _ _ _ _ _ hps hk hv h
      simpa [Level.substPW, PropWhen.bindZ] using this

end L.Arena
