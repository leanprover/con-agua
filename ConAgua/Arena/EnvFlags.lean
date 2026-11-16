module

public import ConAgua.Arena.WhnfBase
public import ConAgua.Arena.Env
import all ConAgua.Arena.Env
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

@[expose] public section

/-!
# The literal flags in L: `lit_name_at`, `lits_stored`, `env_push`, `env_set_flags`

The twin's `IFEnv` carries two literal flags (`natLit`, `strLit`, upstream #579), set where an
index is made and kept by every push; L keeps them in `CTL[160]`, `CTL[161]` and the frozen index's
ten literal names in `CTL[162‥171]` (`EnvR`, `Tiers.lean`). A push of a literal name while string
literals are not expandable recomputes them (`IFEnv.push`, `IFEnv.push_eq`: `pushRows` then the
recomputation as `setFlags`); a temporary extension's caller sets them back after its pops
(`env_set_flags`, `IFEnv.setFlags`). Generated models (`l_model`) and their refinements.
-/

set_option experimental.vcgen true

open ConRon.Arena Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The models (generated) -/

/-- **`lit_name_at` is its model** (generated). -/
l_model litNameAt_specW (p : Prog) (hp : p.lookup "lit_name_at" = some litNameAtL)
  fns [hp ↦ litNameAtW]
  grind [arena_grind]

/-- **`lits_stored` is its model** (generated). -/
l_model litsStored_specW (p : Prog) (hp : p.lookup "lits_stored" = some litsStoredL)
  fns [hp ↦ litsStoredW]
  specs [callW_spec p n "env_find"]
  grind [arena_grind]

/-- **`env_push` is its model** (generated). -/
l_model envPush_specW (p : Prog) (hp : p.lookup "env_push" = some envPushL)
  fns [hp ↦ envPushW list]
  specs [callW_spec p n "env_row_set", callW_spec p n "lit_name_at", callW_spec p n "lits_stored"]
  grind [arena_grind]

/-- **`env_set_flags` is its model** (generated). -/
l_model envSetFlags_specW (p : Prog) (hp : p.lookup "env_set_flags" = some envSetFlagsL)
  fns [hp ↦ envSetFlagsW]
  grind [arena_grind]

/-! ## The literal names -/

/-- **The frozen index's literal names are the ten words `CTL[162‥171]`.** -/
theorem lits_get {m : Mem} {lits : List NIdx} (hl : lits.map (·.word.toUInt64) = litWords m) :
    lits.length = 10 ∧ ∀ (i : Nat) (h : i < lits.length),
      lits[i].word.toUInt64 = rdW (m.arr64 CTL) (162 + UInt64.ofNat i) := by
  have hlen : lits.length = 10 := by
    have := congrArg List.length hl; simpa [litWords] using this
  refine ⟨hlen, fun i h => ?_⟩
  have := congrArg (·[i]?) hl
  simp only [List.getElem?_map, litWords, List.getElem?_range, hlen ▸ h,
    List.getElem?_eq_getElem h, Option.map_some, Option.some.injEq] at this
  simpa using this

theorem lits_dec {m : Mem} {lits : List NIdx} (hl : lits.map (·.word.toUInt64) = litWords m)
    (i : Nat) (h : i < lits.length) : lits[i] = decI (rdW (m.arr64 CTL) (162 + UInt64.ofNat i)) := by
  rw [← (lits_get hl).2 i h, decI_word]

theorem litW_lt32 {m : Mem} {lits : List NIdx} (hl : lits.map (·.word.toUInt64) = litWords m)
    (i : Nat) (h : i < 10) : (rdW (m.arr64 CTL) (162 + UInt64.ofNat i)).toNat < 2 ^ 32 := by
  have ⟨hlen, hg⟩ := lits_get hl
  rw [← hg i (by omega)]; exact idx_word_lt32 _

/-- **`lit_name_at`'s loop is `litNameAt`.** -/
theorem litNameAt_loop {m : Mem} {lits : List NIdx} (hl : lits.map (·.word.toUInt64) = litWords m)
    {w : Word} (hw : w.toNat < 2 ^ 32) :
    ∀ (n : Nat) (i r : Word) (m' : Mem), i.toNat ≤ 10 → litNameAtW.loop1 n m w i = some (r, m') →
      m' = m ∧ (r != 0) = litNameAt lits (decI w) i.toNat := by
  have ⟨hlen, hg⟩ := lits_get hl
  intro n
  induction n with
  | zero => intro i r m' _ h; rw [litNameAtW.loop1.eq_1] at h; cases h
  | succ n ih =>
    intro i r m' hi h
    rw [litNameAt]
    by_cases h10 : i < 10
    · have hi10 : i.toNat < 10 := h10
      have hlt : i.toNat < lits.length := by omega
      rw [dite_eq_left hlt]
      have hw' := hg i.toNat hlt
      simp only [UInt64.ofNat_toNat] at hw'
      by_cases he : rdW (m.arr64 CTL) (162 + i) = w
      · rw [litNameAtW.loop1.arm1 _ _ _ _ h10 he] at h
        cases h
        refine ⟨rfl, ?_⟩
        rw [ite_eq_left (by rw [nidx_beq, decI_word_self w hw, hw', he]; simp)]; rfl
      · rw [litNameAtW.loop1.arm2 _ _ _ _ h10 he] at h
        have e1 : (i + 1).toNat = i.toNat + 1 := by
          rw [UInt64.toNat_add]; simp; omega
        obtain ⟨h1, h2⟩ := ih (i + 1) r m' (by omega) h
        refine ⟨h1, ?_⟩
        rw [ite_eq_right (by rw [nidx_beq, decI_word_self w hw, hw']; simpa using Ne.symm he), h2, e1]
    · have hge : 10 ≤ i.toNat := by rw [UInt64.lt_iff_toNat_lt] at h10; simp at h10; omega
      rw [litNameAtW.loop1.eq_2, ite_eq_right h10] at h
      cases h
      exact ⟨rfl, by rw [dite_eq_right (by omega)]; rfl⟩

/-! ## `lits_stored` -/

/-- The lookups of the literal flags' functions. -/
structure EnvFlagsProg (p : Prog) : Prop where
  rowGet : p.lookup "env_row_get" = some envRowGetL
  rowSet : p.lookup "env_row_set" = some envRowSetL
  baseGet : p.lookup "base_row_get" = some baseRowGetL
  find : p.lookup "env_find" = some envFindL
  litNameAt : p.lookup "lit_name_at" = some litNameAtL
  litsStored : p.lookup "lits_stored" = some litsStoredL
  push : p.lookup "env_push" = some envPushL
  setFlags : p.lookup "env_set_flags" = some envSetFlagsL

variable {p : Prog}

theorem envFound_none {m : Mem} {f q : Word} : envFound m f q = none ↔ (f = 0 ∨ decCI (erecP m) q.toNat = none) := by
  unfold envFound; split <;> simp [*]

/-- **`lits_stored`'s loop is `IFEnv.litsStored`.** -/
theorem litsStored_loop (hP : EnvFlagsProg p) {m : Mem} {vis : Word} {fe : IFEnv} (hE : EnvR m vis fe) :
    ∀ (n : Nat) (i stop r : Word) (m' : Mem), i.toNat ≤ 10 →
      litsStoredW.loop1 p n m vis i stop = some (r, m') →
      m' = m ∧ (r != 0) = fe.litsStored i.toNat stop.toNat := by
  have ⟨hlen, _⟩ := lits_get hE.lits
  intro n
  induction n with
  | zero => intro i stop r m' _ h; rw [litsStoredW.loop1.eq_1] at h; cases h
  | succ n ih =>
    intro i stop r m' hi h
    rw [IFEnv.litsStored]
    by_cases hs : i < stop
    · have hs' : ¬ i.toNat ≥ stop.toNat := by rw [UInt64.lt_iff_toNat_lt] at hs; omega
      rw [ite_eq_right hs']
      by_cases h10 : 10 ≤ i
      · rw [litsStoredW.loop1.arm1 _ _ _ _ _ _ hs h10] at h
        cases h
        have : ¬ i.toNat < fe.base.lits.length := by rw [UInt64.le_iff_toNat_le] at h10; simp at h10; omega
        exact ⟨rfl, by rw [dite_eq_right this]; rfl⟩
      · have hi10 : i.toNat < 10 := by rw [UInt64.le_iff_toNat_le] at h10; simp at h10; omega
        have hlt : i.toNat < fe.base.lits.length := by omega
        rw [dite_eq_left hlt]
        rw [litsStoredW.loop1.eq_2, ite_eq_left hs, ite_eq_right h10] at h
        have hw32 := litW_lt32 hE.lits i.toNat hi10
        simp only [UInt64.ofNat_toNat] at hw32
        have hdec := lits_dec hE.lits i.toNat hlt
        simp only [UInt64.ofNat_toNat] at hdec
        rcases c : callW p n "env_find" [rdW (m.arr64 CTL) (162 + i), vis] m with _ | ⟨r₁, m₁⟩
        · rw [c, litsStoredW.k_env_find.none] at h; cases h
        rw [c] at h
        obtain ⟨s', hs'm, hm1, -, hf, hd⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
          (envFind_refines p hP.rowGet hP.baseGet hP.find n ⟨m, Locals.init []⟩ vis _ hE hw32) c
        have hm₁ : m₁ = m := by rw [← hs'm]; exact hm1
        subst hm₁
        rw [hdec, hf]
        by_cases h0 : r₁.headD 0 = 0
        · rw [litsStoredW.k_env_find.arm1 _ _ _ _ _ _ _ h0] at h
          cases h
          exact ⟨rfl, by simp only [envFound, h0, ite_true]; rfl⟩
        · rw [litsStoredW.k_env_find.arm2 _ _ _ _ _ _ _ h0] at h
          obtain ⟨ci, hci⟩ := hd h0
          have e1 : (i + 1).toNat = i.toNat + 1 := by
            rw [UInt64.toNat_add]; simp; omega
          obtain ⟨h1, h2⟩ := ih (i + 1) stop r m' (by omega) h
          refine ⟨h1, ?_⟩
          simp only [envFound, h0, ite_false, hci]
          rw [h2, e1]
    · have hs' : i.toNat ≥ stop.toNat := by rw [UInt64.lt_iff_toNat_lt] at hs; omega
      rw [litsStoredW.loop1.eq_2, ite_eq_right hs] at h
      cases h
      exact ⟨rfl, by rw [ite_eq_left hs']; rfl⟩

/-! ## The refinements -/

/-- **`lit_name_at(w, i)` refines `litNameAt`** over the frozen index's literal names. -/
@[refines ConRon.Arena.litNameAt]
theorem litNameAt_refines (hp : p.lookup "lit_name_at" = some litNameAtL) (n : Nat) (s₀ : St)
    {lits : List NIdx} (hl : lits.map (·.word.toUInt64) = litWords s₀.mem) (w i : Word)
    (hw : w.toNat < 2 ^ 32) (hi : i.toNat ≤ 10) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lit_name_at" [w, i]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ (r.headD 0 != 0) = litNameAt lits (decI w) i.toNat; ⊤⦄ :=
  triple_post (litNameAt_specW p hp n s₀ w i) fun r s ⟨hL, hm⟩ => by
    cases n with
    | zero => rw [litNameAtW.eq_1] at hm; cases hm
    | succ n =>
      rw [litNameAtW.arm1] at hm
      obtain ⟨h1, h2⟩ := litNameAt_loop hl hw (n + 1) i _ _ hi hm
      exact ⟨hL, h1, h2⟩

/-- **`lits_stored(vis, i, stop)` refines `IFEnv.litsStored`.** -/
@[refines ConRon.Arena.IFEnv.litsStored ConRon.Arena.IFEnv.natLitStoredBy ConRon.Arena.IFEnv.strLitStoredBy]
theorem litsStored_refines (hP : EnvFlagsProg p) (n : Nat) (s₀ : St) {fe : IFEnv} (vis i stop : Word)
    (hE : EnvR s₀.mem vis fe) (hi : i.toNat ≤ 10) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lits_stored" [vis, i, stop]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      (r.headD 0 != 0) = fe.litsStored i.toNat stop.toNat; ⊤⦄ :=
  triple_post (litsStored_specW p hP.litsStored n s₀ vis i stop) fun r s ⟨hL, hm⟩ => by
    cases n with
    | zero => rw [litsStoredW.eq_1] at hm; cases hm
    | succ n =>
      rw [litsStoredW.eq_2] at hm
      obtain ⟨h1, h2⟩ := litsStored_loop hP hE (n + 1) i stop _ _ hi hm
      exact ⟨hL, h1, h2⟩

/-! ## `env_push`, `env_set_flags` -/

/-- **The memory with the literal flags' words** `CTL[160]`, `CTL[161]` set to `a`, `b`. -/
def flagsSet (m : Mem) (a b : Word) : Mem := (m.set64 CTL 160 a).set64 CTL 161 b

theorem set64_rdW_self (m : Mem) (a : TieredArray) (k : Word) (h : k.toNat < (m.arr64 a).size) :
    m.set64 a k (rdW (m.arr64 a) k) = m := by
  cases m with
  | mk bs ws g =>
  simp only [Mem.set64, Mem.mk.injEq, true_and, and_true]
  funext s'
  split
  · subst s'
    simp only [Mem.arr64] at h ⊢
    rw [rdW, Array.getElem?_eq_getElem h, Option.getD_some, Array.set!_eq_setIfInBounds]
    apply Array.ext <;> simp
    grind
  · rfl

theorem flagsSet_self (m : Mem) (h : 161 < (m.arr64 CTL).size) :
    flagsSet m (rdW (m.arr64 CTL) 160) (rdW (m.arr64 CTL) 161) = m := by
  unfold flagsSet
  rw [set64_rdW_self m CTL 160 (by simp; omega)]
  exact set64_rdW_self m CTL 161 (by simp; omega)

theorem flagsSet_rd160 (m : Mem) (a b : Word) (h : 161 < (m.arr64 CTL).size) :
    rdW ((flagsSet m a b).arr64 CTL) 160 = a := by
  simp [flagsSet, rdW_set64, Mem.size64_set64]; omega

theorem flagsSet_rd161 (m : Mem) (a b : Word) (h : 161 < (m.arr64 CTL).size) :
    rdW ((flagsSet m a b).arr64 CTL) 161 = b := by
  simp [flagsSet, rdW_set64, Mem.size64_set64]; omega

/-- `flagsSet` writes the two flag words only. -/
theorem flagsSet_frame (m : Mem) (a b : Word) : MemFrame [] [160, 161] m (flagsSet m a b) :=
  ⟨fun x _ hx => by simp only [flagsSet, Mem.arr64_set64_ne _ _ _ _ _ hx],
   fun x hx => by
     simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
     exact rdW_set_ctl_160_161 m a b x hx.1 hx.2,
   fun x => by simp [flagsSet, Mem.size64_set64]⟩

theorem IFEnv.litsStored_setFlags (fe : IFEnv) (a b : Bool) (i stop : Nat) :
    (fe.setFlags a b).litsStored i stop = fe.litsStored i stop := by
  obtain ⟨k, hk⟩ : ∃ k, k = stop - i := ⟨_, rfl⟩
  induction k generalizing i with
  | zero =>
    conv => lhs; rw [IFEnv.litsStored]
    conv => rhs; rw [IFEnv.litsStored]
    simp [show stop ≤ i by omega]
  | succ k ih =>
    have e := ih (i + 1) (by omega)
    conv => lhs; rw [IFEnv.litsStored]
    conv => rhs; rw [IFEnv.litsStored]
    simp only [IFEnv.setFlags] at e ⊢
    rw [e]
    rfl

theorem IFEnv.setFlags_setFlags (fe : IFEnv) (a b c d : Bool) :
    (fe.setFlags a b).setFlags c d = fe.setFlags c d := rfl

/-- **`env_push` refines `IFEnv.push`**: the new view `vis + 1` relates the pushed environment;
the memory is the own row's write (`ownSet`) with the flag words as the push left them (unchanged,
or recomputed at a literal name: `flagsSet`). -/
@[refines ConRon.Arena.IFEnv.push]
theorem envPush_refines (hP : EnvFlagsProg p) (n : Nat) (s₀ : St) {fe : IFEnv} {ci : IConstantInfo}
    (vis q : Word) (hE : EnvR s₀.mem vis fe) (hci : decCI (erecP s₀.mem) q.toNat = some ci)
    (hc : 161 < (s₀.mem.arr64 CTL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_push" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [vis + 1] ∧ vis.toNat < 4294967294 ∧
      rowTag (erecRd s₀.mem (q + (CI.cv + CV.name))) ≤ 2 ∧
      rowIx (erecRd s₀.mem (q + (CI.cv + CV.name))) + 1 <
        (s₀.mem.arr64 (ownArr (erecRd s₀.mem (q + (CI.cv + CV.name))))).size ∧
      EnvR s'.mem (vis + 1) (fe.push ci) ∧
      s'.mem = flagsSet (ownSet s₀.mem (erecRd s₀.mem (q + (CI.cv + CV.name))) (vis + 1) q)
        (rdW (s'.mem.arr64 CTL) 160) (rdW (s'.mem.arr64 CTL) 161); ⊤⦄ :=
  triple_post (envPush_specW p hP.push n s₀ vis q) fun r s ⟨hL, hm⟩ => by
    cases n with
    | zero => rw [envPushW.eq_1] at hm; cases hm
    | succ n =>
    by_cases hv : 4294967294 ≤ vis
    · rw [envPushW.abort1 _ _ _ _ _ hv] at hm; cases hm
    rw [envPushW.arm1 _ _ _ _ _ hv] at hm
    obtain ⟨w, hw, hw32, hname⟩ := decCI_name hci
    have hq : (q + (CI.cv + CV.name)).toNat = q.toNat + CI.cv.toNat :=
      off_add_toNat CI.cv_name_toNat (erecP_lt64 hw)
    have hr : erecRd s₀.mem (q + (CI.cv + CV.name)) = w := erecRd_of (by rw [hq]; exact hw)
    change envPushW.k_env_row_set p n vis (erecRd s₀.mem (q + (CI.cv + CV.name)))
      (callW p n "env_row_set" [erecRd s₀.mem (q + (CI.cv + CV.name)), vis + 1, q] s₀.mem) =
        some (r, s.mem) at hm
    rw [hr] at hm ⊢
    have hv' : vis.toNat < 2 ^ 32 - 2 := by
      rw [UInt64.le_iff_toNat_le] at hv; simp at hv; omega
    rcases c1 : callW p n "env_row_set" [w, vis + 1, q] s₀.mem with _ | ⟨r₁, m₁⟩
    · rw [c1, envPushW.k_env_row_set.none] at hm; cases hm
    rw [c1] at hm
    obtain ⟨s₁, hs₁, hm₁, -, ht, hb⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (envRowSet_spec p hP.rowSet n ⟨s₀.mem, Locals.init []⟩ w (vis + 1) q) c1
    simp only at hm₁ ht hb
    rw [hs₁] at hm₁
    subst hm₁
    suffices H : r = [vis + 1] ∧ EnvR s.mem (vis + 1) (fe.push ci) ∧
        s.mem = flagsSet (ownSet s₀.mem w (vis + 1) q) (rdW (s.mem.arr64 CTL) 160)
          (rdW (s.mem.arr64 CTL) 161) from
      ⟨hL, H.1, by omega, ht, hb, H.2⟩
    have hE₁ := hE.push hci hw hv' ht hb
    have hctl : (ownSet s₀.mem w (vis + 1) q).arr64 CTL = s₀.mem.arr64 CTL := ownSet_ctl _ _ _ _
    have hc₁ : 161 < ((ownSet s₀.mem w (vis + 1) q).arr64 CTL).size := by rw [hctl]; exact hc
    have hpe := IFEnv.push_eq fe ci
    -- the flags kept: `pushRows`
    have keep : (!fe.strLit && litNameAt fe.base.lits ci.name 0) = false →
        s.mem = ownSet s₀.mem w (vis + 1) q → r = [vis + 1] →
        r = [vis + 1] ∧ EnvR s.mem (vis + 1) (fe.push ci) ∧
          s.mem = flagsSet (ownSet s₀.mem w (vis + 1) q) (rdW (s.mem.arr64 CTL) 160)
            (rdW (s.mem.arr64 CTL) 161) := by
      intro hre hsm hr1
      rw [hpe, ite_eq_right (by rw [hre]; simp), hsm]
      exact ⟨hr1, hE₁, (flagsSet_self _ hc₁).symm⟩
    by_cases h161 : rdW ((ownSet s₀.mem w (vis + 1) q).arr64 CTL) 161 = 0
    case neg =>
      rw [envPushW.k_env_row_set.arm2 _ _ _ _ _ _ h161, envPushW.j1.eq_1] at hm
      obtain ⟨hr1, hsm⟩ := Prod.mk.inj (Option.some.inj hm)
      have hs : fe.strLit = true := by rw [hE.strLit, ← hctl]; simpa using h161
      exact keep (by simp [hs]) hsm.symm hr1.symm
    rw [envPushW.k_env_row_set.arm1 _ _ _ _ _ _ h161] at hm
    have hs : fe.strLit = false := by rw [hE.strLit, ← hctl]; simpa using h161
    rcases c2 : callW p n "lit_name_at" [w, 0] (ownSet s₀.mem w (vis + 1) q) with _ | ⟨r₂, m₂⟩
    · rw [c2, envPushW.k_lit_name_at.eq_1] at hm; cases hm
    rw [c2] at hm
    obtain ⟨s₂, hs₂, -, hm₂, hln⟩ := triple_of_callW (s₀ := ⟨_, Locals.init []⟩)
      (litNameAt_refines hP.litNameAt n ⟨ownSet s₀.mem w (vis + 1) q, Locals.init []⟩ hE₁.lits w 0 hw32
        (by simp)) c2
    simp only at hm₂
    rw [hs₂] at hm₂; subst hm₂
    have hname' : ci.name = decI w := hname
    have hlits : (pushRows fe ci).base.lits = fe.base.lits := rfl
    rw [hlits, ← hname', show (0 : Word).toNat = 0 from rfl] at hln
    by_cases h0 : r₂.headD 0 = 0
    · rw [envPushW.k_lit_name_at.arm2 _ _ _ _ _ h0, envPushW.j1.eq_1] at hm
      obtain ⟨hr1, hsm⟩ := Prod.mk.inj (Option.some.inj hm)
      have : litNameAt fe.base.lits ci.name 0 = false := by rw [← hln, h0]; rfl
      exact keep (by simp [this]) hsm.symm hr1.symm
    rw [envPushW.k_lit_name_at.arm1 _ _ _ _ _ h0] at hm
    have hre : (!fe.strLit && litNameAt fe.base.lits ci.name 0) = true := by
      rw [hs, ← hln]; simpa using h0
    rw [hpe, ite_eq_left hre]
    rcases c3 : callW p n "lits_stored" [vis + 1, 0, 3] (ownSet s₀.mem w (vis + 1) q) with _ | ⟨r₃, m₃⟩
    · rw [c3, envPushW.k_lits_stored.eq_1] at hm; cases hm
    rw [c3] at hm
    obtain ⟨s₃, hs₃, -, hm₃, hl3⟩ := triple_of_callW (s₀ := ⟨_, Locals.init []⟩)
      (litsStored_refines hP n ⟨ownSet s₀.mem w (vis + 1) q, Locals.init []⟩ (vis + 1) 0 3 hE₁ (by simp)) c3
    simp only at hm₃
    rw [hs₃] at hm₃; subst hm₃
    replace hl3 : (r₃.headD 0 != 0) = (pushRows fe ci).natLitStoredBy := hl3
    -- the final flags `a`, `b`
    have fin : ∀ b : Word, (b != 0) = ((pushRows fe ci).natLitStoredBy && (pushRows fe ci).litsStored 3 10) →
        envPushW.j2 p vis (r₃.headD 0) b (ownSet s₀.mem w (vis + 1) q) = some (r, s.mem) →
        r = [vis + 1] ∧ EnvR s.mem (vis + 1) (let fe2 := (pushRows fe ci).setFlags (pushRows fe ci).natLitStoredBy fe.strLit
          fe2.setFlags fe2.natLit fe2.strLitStoredBy) ∧
          s.mem = flagsSet (ownSet s₀.mem w (vis + 1) q) (rdW (s.mem.arr64 CTL) 160)
            (rdW (s.mem.arr64 CTL) 161) := by
      intro b hb hj
      rw [envPushW.j2.arm1, envPushW.j1.eq_1] at hj
      obtain ⟨hr1, hsm⟩ := Prod.mk.inj (Option.some.inj hj)
      have e := hE₁.setFlags (r₃.headD 0) b hc₁
      have ha : (r₃.headD 0 != 0) = (pushRows fe ci).natLitStoredBy := hl3
      refine ⟨hr1.symm, ?_, ?_⟩
      · rw [← hsm]
        simp only [IFEnv.setFlags_setFlags, IFEnv.strLitStoredBy, IFEnv.natLitStoredBy, IFEnv.litsStored_setFlags]
        rw [ha, hb] at e
        exact e
      · rw [← hsm]
        show flagsSet (ownSet s₀.mem w (vis + 1) q) (r₃.headD 0) b = flagsSet (ownSet s₀.mem w (vis + 1) q)
          (rdW ((flagsSet (ownSet s₀.mem w (vis + 1) q) (r₃.headD 0) b).arr64 CTL) 160)
          (rdW ((flagsSet (ownSet s₀.mem w (vis + 1) q) (r₃.headD 0) b).arr64 CTL) 161)
        rw [flagsSet_rd160 _ _ _ hc₁, flagsSet_rd161 _ _ _ hc₁]
    by_cases ha0 : r₃.headD 0 = 0
    · rw [envPushW.k_lits_stored.arm2 _ _ _ _ _ ha0] at hm
      refine fin 0 ?_ hm
      have : (pushRows fe ci).natLitStoredBy = false := by rw [← hl3, ha0]; rfl
      simp [this]
    rw [envPushW.k_lits_stored.arm1 _ _ _ _ _ ha0] at hm
    rcases c4 : callW p n "lits_stored" [vis + 1, 3, 10] (ownSet s₀.mem w (vis + 1) q) with _ | ⟨r₄, m₄⟩
    · rw [c4, envPushW.k_lits_stored_2.none] at hm; cases hm
    rw [c4, envPushW.k_lits_stored_2.arm1] at hm
    obtain ⟨s₄, hs₄, -, hm₄, hl4⟩ := triple_of_callW (s₀ := ⟨_, Locals.init []⟩)
      (litsStored_refines hP n ⟨ownSet s₀.mem w (vis + 1) q, Locals.init []⟩ (vis + 1) 3 10 hE₁ (by simp)) c4
    simp only at hm₄
    rw [hs₄] at hm₄; subst hm₄
    replace hl4 : (r₄.headD 0 != 0) = (pushRows fe ci).litsStored 3 10 := hl4
    refine fin _ ?_ hm
    have : (pushRows fe ci).natLitStoredBy = true := by rw [← hl3]; simpa using ha0
    rw [this, hl4]; rfl

/-- **`env_set_flags(a, b)` refines `IFEnv.setFlags`**: the flag words written, the environment's
flags `a ≠ 0`, `b ≠ 0`. -/
@[refines ConRon.Arena.IFEnv.setFlags]
theorem envSetFlags_refines (hp : p.lookup "env_set_flags" = some envSetFlagsL) (n : Nat) (s₀ : St)
    {fe : IFEnv} (vis a b : Word) (hE : EnvR s₀.mem vis fe) (hc : 161 < (s₀.mem.arr64 CTL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_set_flags" [a, b]
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = flagsSet s₀.mem a b ∧
      EnvR s'.mem vis (fe.setFlags (a != 0) (b != 0)); ⊤⦄ :=
  triple_post (envSetFlags_specW p hp n s₀ a b) fun r s ⟨hL, hm⟩ => by
    rw [envSetFlagsW.arm1] at hm
    obtain ⟨-, hsm⟩ := Prod.mk.inj (Option.some.inj hm)
    rw [← hsm]
    exact ⟨hL, rfl, hE.setFlags a b hc⟩

end L.Arena
