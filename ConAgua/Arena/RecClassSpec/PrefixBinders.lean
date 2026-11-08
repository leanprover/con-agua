module

public import ConAgua.Arena.RecClassSpec.MnW
public import ConAgua.Arena.RecClassSpec.RuProg
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndRealAbsSim
import ConAgua.Arena.LdRd
import ConAgua.Arena.RecClassSpec.MjW
import ConAgua.Arena.RecClassSpec.PiBWRoom
import ConAgua.Arena.RecClassSpec.Rec2AppendWDec
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.RecClass

@[expose] public section

/-!
# PrefixBinders: `ConRon.Arena.ClassGen.prefixBinders`

The refinement theorems `classGenPrefixBinders_refines` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Models -/

def fcK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

theorem fcK_some (r : List Word) (m : Mem) : fcK (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl

attribute [ind_grind] fcK_some

l_model findCtorGo_spec (p : Prog) (h : PbProg p)
  fns [h.fcg ↦ fcgW list]
  grind [arena_grind]

l_model findCtor_spec (p : Prog) (h : PbProg p)
  fns [h.fc ↦ fcW list]
  specs [findCtorGo_spec p h n]
  grind [arena_grind]

/-- **The slot walk is its models `psW`, `smW`, `snW`** (generated; fuel `n`). -/
l_model slots_spec (p : Prog) (h : PbProg p)
  fns [h.psg ↦ psW list, h.psm ↦ smW list, h.psn ↦ snW list]
  specs [findCtor_spec p h n, classGenMotiveTy_spec p h.toMtProg n, classGenMinorTy_spec p h.toMnProg n,
    slCons_specW p h.alloc h.copy h.cons n]
  grind [arena_grind] finish [] gen 20

l_model prefixBinders_spec (p : Prog) (h : PbProg p)
  fns [h.pb ↦ gpbW list]
  specs [ftdsF_spec p h.ad n, (slots_spec p h n).1, slAppend_specW p h.alloc h.copy h.app n]
  grind [arena_grind]

/-! ## Finding the constructor -/

/-- What `find_ctor(_go)` returns. -/
def FcRes (m : Mem) (r : List Word) : Option ClassCtor → Prop
  | none => r.headD 0 = 0
  | some X => r.headD 0 = 1 ∧ DecB (fun m => decCC m (r.tail.headD 0).toNat) m X

theorem fcgW_ok (n : Nat) : ∀ (m m' : Mem) (io il cn : Word) (r : List Word) (xs : List ClassCtor),
    fcgW n m io il cn = some (r, m') → DecB (fun m => decPL m (decCC m) io.toNat il.toNat) m xs → H cn →
    (m.arr64 IW).size < 2 ^ 64 →
    m' = m ∧ FcRes m r (xs.find? (fun x => x.cv.name == decI cn)) := by
  sorry

theorem fcW_ok (n : Nat) (m m' : Mem) (g c cn : Word) (r : List Word) (G : ClassGen)
    (h : fcW n m g c cn = some (r, m')) (hG : DecB (fun m => decCG m g.toNat) m G) (hcn : H cn)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    m' = m ∧ FcRes m r ((G.ctors.getD c.toNat []).find? (fun x => x.cv.name == decI cn)) := by
  rcases n with _ | n
  · simp [fcW] at h
  have hG' : decCG (truncM m) g.toNat = some G := hG
  simp only [decCG, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hG'
  obtain ⟨nP, hnP, ps, hps, cls, hcls, ft, hft, sl, hsl, cts, hcts, el, hel, pre, hpre, rfl⟩ := hG'
  obtain ⟨co, cl, hco, hcl, hctd⟩ := decAt_some hcts
  obtain ⟨hcot, hcom⟩ := rec2IwN_trunc hco
  obtain ⟨hclt, hclm⟩ := rec2IwN_trunc hcl
  obtain ⟨e9, t9⟩ := rec2RdN (w := g) (k := 9) hcom hsz
  obtain ⟨e10, t10⟩ := rec2RdN (w := g) (k := 10) (by simpa [Nat.add_assoc] using hclm) hsz
  simp only [show UInt64.ofNat 9 = (9 : Word) from rfl, show UInt64.ofNat 10 = (10 : Word) from rfl] at e9 e10
  have hlen := decPL_length _ hctd
  by_cases hc : rdW (m.arr64 IW) (g + 10) ≤ c
  · rw [fcW.arm1 (hc1 := hc)] at h
    cases h
    have : cts.length ≤ c.toNat := by rw [hlen, ← t10]; rw [e10] at hc; exact UInt64.le_iff_toNat_le.mp hc
    refine ⟨rfl, ?_⟩
    have hn : cts.getD c.toNat [] = [] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
    rw [hn]
    rfl
  rw [fcW.arm2 (hc1 := hc)] at h
  have hcl' : c.toNat < cl := by
    rw [e10] at hc; have := UInt64.lt_iff_toNat_lt.mp (by simpa using hc); rwa [t10] at this
  obtain ⟨lp, hlp, hlpd⟩ := decPL_getH (truncM m) hctd c.toNat hcl'
  obtain ⟨-, hlpm⟩ := rec2IwN_trunc hlp
  obtain ⟨xo, xl, hio, hil, hdx⟩ := decAt_some hlpd
  obtain ⟨-, hiom⟩ := rec2IwN_trunc hio
  obtain ⟨-, hilm⟩ := rec2IwN_trunc hil
  have elp : rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 9) + c) = UInt64.ofNat lp := by
    rw [e9]; simpa using (rec2RdN (w := UInt64.ofNat co) (k := c.toNat) (by rw [t9]; exact hlpm) hsz).1
  have lplt := (iwN_rdW hlpm (by have := iwN_lt hlpm; omega)).2
  obtain ⟨eio, -⟩ := rec2RdN (w := UInt64.ofNat lp) (k := 0) (by simpa [UInt64.toNat_ofNat_of_lt' lplt] using hiom) hsz
  obtain ⟨eil, -⟩ := rec2RdN (w := UInt64.ofNat lp) (k := 1)
    (by simpa [UInt64.toNat_ofNat_of_lt' lplt] using hilm) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero,
    show UInt64.ofNat 1 = (1 : Word) from rfl] at eio eil
  rw [elp, eio, eil] at h
  obtain ⟨⟨r', m''⟩, hr, h⟩ := of_K h rfl
  rw [fcW.k_class_gen_prefix_binders_find_ctor_go.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have iolt := (iwN_rdW hiom (by have := iwN_lt hiom; omega)).2
  have illt := (iwN_rdW hilm (by have := iwN_lt hilm; omega)).2
  obtain ⟨hm, hres⟩ := fcgW_ok n m m'' _ _ cn r' (cts[c.toNat]'(by omega)) hr
    (by rw [UInt64.toNat_ofNat_of_lt' iolt, UInt64.toNat_ofNat_of_lt' illt]; exact hdx) hcn hsz
  subst hm
  refine ⟨rfl, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show c.toNat < cts.length by omega), Option.getD_some]
  exact hres

theorem rec2DecCS_mot {m : Mem} {p : Nat} {key : ClassKey} (h : decCS m p = some (.motive key)) :
    iwN m p = some 0 := by
  rw [decCS] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, h⟩ := h
  match t, h with
  | 0, _ => exact ht
  | 1, h => simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h; obtain ⟨_, _, _, _, _, _, h⟩ := h; cases h
  | (_ + 2), h => simp at h

theorem rec2DecCS_min {m : Mem} {p c : Nat} {C : NIdx} {ihs : List (Nat × Nat)}
    (h : decCS m p = some (.minor c C ihs)) :
    iwN m p = some 1 ∧ iwN m (p + 1) = some c ∧ iwH m (p + 2) = some C := by
  rw [decCS] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, h⟩ := h
  match t, h with
  | 0, h => simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h; obtain ⟨_, _, _, _, h⟩ := h; cases h
  | 1, h =>
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨c', hc, C', hC, ihs', -, he⟩ := h
    cases he
    exact ⟨ht, hc, hC⟩
  | (_ + 2), h => simp at h

theorem rec2Count_succ (sl : List ClassSlot) (s : Nat) (hs : s < sl.length) :
    ((sl.take (s + 1)).filter rec2IsMot).length =
      ((sl.take s).filter rec2IsMot).length + (if rec2IsMot sl[s] then 1 else 0) := by
  rw [List.take_add_one, List.filter_append, List.length_append, List.getElem?_eq_getElem hs]
  simp only [Option.toList_some]
  cases h : rec2IsMot sl[s] <;> simp [List.filter, h]

/-- The common tail of a slot: the rest of the walk, then the cons. -/
theorem pfTail {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m1 : Mem} {a1 : AState}
    (n : Nat) (ty : Word) (hty : H ty) (_hS1 : StageR vis fe m1 a1) (hg1 : IWGrow m m1)
    (rest : Option (List Word × Mem)) (opR : AM (Option (List EIdx)))
    (hrest : RSim rest opR a1
      (fun b a' o => StageR vis fe b.2 a' ∧ IWGrow m1 b.2 ∧ decIHO b.2 b.1 o ∧ AbsOK b.2)) :
    RSim (psW.k_class_gen_prefix_binders_slot_motive (smW.k_class_gen_prefix_binders_slots_go n ty rest)) (do
      let __do_lift ← opR
      match __do_lift with
      | none => pure none
      | some rest => pure (some (decI ty :: rest))) a1
      (fun b a' o => StageR vis fe b.2 a' ∧ IWGrow m b.2 ∧ decIHO b.2 b.1 o ∧ AbsOK b.2) := by
  sorry

theorem psW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (G : ClassGen) (g : Word)
    (hns : G.nP + G.slots.length < 2 ^ 64) (n : Nat) :
    ∀ (m : Mem) (a : AState) (s mc : Word), StageR vis fe m a → DecB (fun m => decCG m g.toNat) m G →
    s.toNat ≤ G.slots.length → mc.toNat = ((G.slots.take s.toNat).filter rec2IsMot).length → AbsOK m →
    RSim (psW n m g s mc) (ConRon.Arena.ClassGen.prefixBinders.slotsGo G s.toNat (G.slots.drop s.toNat)) a
      (fun b a' o => StageR vis fe b.2 a' ∧ IWGrow m b.2 ∧ decIHO b.2 b.1 o ∧ AbsOK b.2) := by
  sorry

theorem gpbW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem) (a : AState)
    (g : Word) (G : ClassGen) (hS : StageR vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hA : AbsOK m) :
    RSim (gpbW n m g) (ConRon.Arena.ClassGen.prefixBinders G) a
      (fun b a' x => KP dn vis fe m decIHO b a' x ∧ AbsOK b.2) := by
  sorry

/-- **`class_gen_prefix_binders` refines `ClassGen.prefixBinders`** (through the stubs of
`class_gen_motive_ty`, `class_gen_minor_ty` and `fvar_type_ds`): the parameters' binders, then
every slot's, a slice below the top. -/
@[refines ConRon.Arena.ClassGen.prefixBinders]
theorem classGenPrefixBinders_refines (p : Prog) (hp : PbProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g : Word) (G : ClassGen)
    (hS : StageR vis fe s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_prefix_binders" [g]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.prefixBinders G) a₀ ∧
      KP dn vis fe s₀.mem decIHO (r, s'.mem) (AM.st (ConRon.Arena.ClassGen.prefixBinders G) a₀)
        (AM.res (ConRon.Arena.ClassGen.prefixBinders G) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (prefixBinders_spec p hp n s₀ g) fun _ _ ⟨hl, hw⟩ =>
    let h := (gpbW_sim dn vis fe n _ a₀ g G hS hG hns hA).am hw
    ⟨hl, h.1, h.2.1, h.2.2⟩

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem loc_init13 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: r) 13 =
      x13 := rfl
theorem loc_init14 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: r)
      14 = x14 := rfl
theorem loc_init15 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) (r : List Word) :
    Locals.init
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: r)
      15 = x15 := rfl

l_model findSlotGo_spec (p : Prog) (h : RuProg p)
  fns [h.fsg ↦ fsgW list]
  grind [arena_grind]

l_model pvarsGo_spec (p : Prog) (h : RuProg p)
  fns [h.pv ↦ pvW list]
  specs [rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n,
    slotVar_spec p h.pw h.sf h.sp h.isort h.fvf h.fvp h.ifv h.sv n, slCons_specW p h.alloc h.copy h.cons n]
  grind [arena_grind] finish [rdW_eq] gen 20

/-! ## One call -/

l_model call1Close_spec (p : Prog) (h : RuProg p)
  fns [h.c1c ↦ c1cW list]
  specs [ftdsF_spec p h.ad n, closeLams_spec p h.db h.lf h.lp h.il h.mkl h.cl h.ab n]
  grind [arena_grind]

l_model call1Tail_spec (p : Prog) (h : RuProg p)
  fns [h.c1t ↦ c1tW list]
  specs [rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, mknF_spec p h.ad n,
    internConst_spec p h.cf h.cp h.ic n, slAppend_specW p h.alloc h.copy h.app n,
    slSnoc_specW p h.alloc h.copy h.snoc n, call1Close_spec p h n]
  grind [arena_grind]

/-- **`class_gen_rule_call1` is its model `c1W`** (generated). -/
l_model call1_spec (p : Prog) (h : RuProg p)
  fns [h.c1 ↦ c1W list]
  specs [rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, rec2IhParts_specF p h.ihp h.ad h.opf n,
    classRecOf_spec p h.cro n, call1Tail_spec p h n]
  grind [arena_grind] finish [] gen 20 trace

theorem c1W_tail_eq : c1W.k_class_gen_rule_call1_tail = fcK := by
  funext o; cases o <;> rfl

/-! ## The calls -/

/-- **`class_gen_rule_calls_go` is its model `cgW`** (generated). -/
l_model callsGo_spec (p : Prog) (h : RuProg p)
  fns [h.cg ↦ cgW list]
  specs [call1_spec p h n, slCons_specW p h.alloc h.copy h.cons n]
  grind [arena_grind] extra [ld64_rd_spec]

section cgArms
variable (n : Nat) (m : Mem) (g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i : Word)

/-- A field that is not a recursive call: the walk goes on. -/
theorem cgW_ord (h : ¬ nn = 0) (ht : ¬ isTag m x i = 1) :
    cgW (n + 1) m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i =
      cgW.k_class_gen_rule_calls_go_2
        (cgW n m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e (nn - 1) (i + 1)) := by
  by_cases hi : i < rdW (m.arr64 IW) (x + 3)
  · rw [cgW.arm2 (hc1 := h) (hc2 := hi), cgW.j1.arm2 (hc1 := by simpa [isTag, hi] using ht)]
  · rw [cgW.arm3 (hc1 := h) (hc2 := hi), cgW.j1.arm2 (hc1 := by simp)]

/-- A recursive field: its call, then the walk. -/
theorem cgW_rec (h : ¬ nn = 0) (ht : isTag m x i = 1) :
    cgW (n + 1) m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i =
      cgW.k_class_gen_rule_call1 n g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i
        (c1W n m g (rdW (m.arr64 IW) (isKp m x i + 1)) (rdW (m.arr64 IW) (isKp m x i + 2)) wso wsl fvso fvsl
          pvo pvl rlvls rco rcl cgo cgl i e) := by
  have hi : i < rdW (m.arr64 IW) (x + 3) := by
    by_cases hi : i < rdW (m.arr64 IW) (x + 3)
    · exact hi
    · simp [isTag, hi] at ht
  rw [cgW.arm2 (hc1 := h) (hc2 := hi), cgW.j1.arm1 (hc1 := by simpa [isTag, hi] using ht)]
  rfl
end cgArms

/-! ## The closing, the body, the rule -/

l_model ruleClose_spec (p : Prog) (h : RuProg p)
  fns [h.rc ↦ grcW list]
  specs [slotVar_spec p h.pw h.sf h.sp h.isort h.fvf h.fvp h.ifv h.sv n,
    slAppend_specW p h.alloc h.copy h.app n, mknF_spec p h.ad n, ftdsF_spec p h.ad n,
    closeLams_spec p h.db h.lf h.lp h.il h.mkl h.cl h.ab n]
  grind [arena_grind]

l_model ruleBody_spec (p : Prog) (h : RuProg p)
  fns [h.rb ↦ rbW list]
  specs [targetPiDomsWith_spec p h.ev h.copy h.alloc h.cons h.tpd h.hi1 n, pvarsGo_spec p h n,
    callsGo_spec p h n, ruleClose_spec p h n]
  grind [arena_grind]

def ruK2 (n : Nat) (g rco rcl cgo cgl rlvls x rP s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0], m2)
    else fcK (rbW n m2 g rco rcl cgo cgl rlvls x rP s (r2.tail.headD 0) (r2.tail.tail.headD 0))

def ruK1 (n : Nat) (g rco rcl cgo cgl rlvls x rP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0], m1)
    else ruK2 n g rco rcl cgo cgl rlvls x rP (r1.tail.headD 0)
      (opfF m1 [rdW (m1.arr64 IW) (x + 1), rdW (m1.arr64 IW) (x + 4), rP])

section arms2
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (next : Mem → Option (List Word × Mem))
  (g x so sl j c cn rP i v e app fvso fvsl pvo pvl rlvls xso xsl idxo idxl r t tele wso wsl rco rcl cgo cgl
    nn s fo fl ihso ihsl body sv rc fx : Word) (r1 r2 r3 r4 r5 r6 : List Word)
theorem ruK1_fail (h : r1.headD 0 = 0) : ruK1 n g rco rcl cgo cgl rlvls x rP (some (r1, m1)) = some ([0, 0], m1) := by
  rw [ruK1, ite_eq_left h]
theorem ruK1_ok (h : r1.headD 0 ≠ 0) : ruK1 n g rco rcl cgo cgl rlvls x rP (some (r1, m1)) =
    ruK2 n g rco rcl cgo cgl rlvls x rP (r1.tail.headD 0)
      (opfF m1 [rdW (m1.arr64 IW) (x + 1), rdW (m1.arr64 IW) (x + 4), rP]) := by
  rw [ruK1, ite_eq_right h]
theorem ruK2_fail (h : r2.headD 0 = 0) : ruK2 n g rco rcl cgo cgl rlvls x rP s (some (r2, m2)) = some ([0, 0], m2) := by
  rw [ruK2, ite_eq_left h]
theorem ruK2_ok (h : r2.headD 0 ≠ 0) : ruK2 n g rco rcl cgo cgl rlvls x rP s (some (r2, m2)) =
    fcK (rbW n m2 g rco rcl cgo cgl rlvls x rP s (r2.tail.headD 0) (r2.tail.tail.headD 0)) := by
  rw [ruK2, ite_eq_right h]
end arms2

attribute [ind_grind] ruK1_fail ruK1_ok ruK2_fail ruK2_ok

end L.Ind

end

end
